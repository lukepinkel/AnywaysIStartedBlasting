theory PosetsRel4
  imports Main
begin

hide_const top bot
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev Sup Inf trans refl Greatest
declare [[show_consts, show_results]]
declare [[show_abbrevs=true]]


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

abbreviation semitop where
  "semitop R X top \<equiv> is_inf_semilattice R X \<and> is_greatest R X top"


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
  "filter_closure R X A \<equiv> if A={} then {Greatest R X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"

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

definition cl_from_clr::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "cl_from_clr R C \<equiv> (\<lambda>x. Least R  (ubd R  C {x}))"

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

definition fne_sup_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow>  'a set" where
  "fne_sup_cl R X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x}"


definition mesh::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infixl "(#)" 70)
   where "A # B \<equiv> (\<forall>a. \<forall>b. a \<in> A \<longrightarrow> b \<in> B \<longrightarrow> a \<inter> b \<noteq> {})"

definition grill::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" 
  where "grill PX A \<equiv> {E \<in> PX. {E}#A}"

definition pwr  where
    "pwr X \<equiv> {(A, B). A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B}"

subsection Convergence
  
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

definition cont_at:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set \<Rightarrow> 'b set \<Rightarrow> ('b set set \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> bool" where
  "cont_at f X q Y p x \<equiv> (\<forall>\<F>.  (\<F>, x)\<in> q \<longrightarrow> ({E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E}, f x) \<in> p)"

definition centered::"'a set \<Rightarrow> ('a set set \<times> 'a) set \<Rightarrow> bool" where
  "centered X q \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (lcro (pwr X) (Pow X) {x}, x) \<in> q )"

definition isoconv::"'a set \<Rightarrow> ('a set set \<times> 'a) set \<Rightarrow> bool" where
  "isoconv X q \<equiv> (\<forall>\<G> \<F> x. \<G> \<in> pfilters_on (pwr X) (Pow X) \<and> (\<F>, x) \<in> q \<and> \<F>\<subseteq> \<G> \<longrightarrow> (\<G>,x)\<in>q)"

definition onpconv:: "'a set \<Rightarrow> ('a set set \<times> 'a) set \<Rightarrow> bool" where
  "onpconv X q \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q)"

definition isconvs:: "'a set \<Rightarrow> ('a set set \<times> 'a) set \<Rightarrow> bool" where
  "isconvs X q \<equiv> (\<forall>x \<E>. (\<E>, x) \<in> q \<longrightarrow> x \<in> X \<and>  \<E> \<in> (pfilters_on (pwr X) (Pow X)))"

definition ispsmap:: "'a set \<Rightarrow> ('a \<times> 'a set) set \<Rightarrow> bool" where
  "ispsmap X N \<equiv> (\<forall>x V. (x, V) \<in> N \<longrightarrow> x \<in> X \<and> V \<in> Pow X)"

definition isspmap:: "'a set \<Rightarrow> ('a set \<times> 'a) set \<Rightarrow> bool" where
  "isspmap X Cl \<equiv> (\<forall>x V. (V, x) \<in> Cl \<longrightarrow> x \<in> X \<and> V \<in> Pow X)"

abbreviation is_gconv where
  "is_gconv X q \<equiv> isconvs X q \<and> centered X q \<and> isoconv X q"

abbreviation is_prtop where
  "is_prtop X q \<equiv> isconvs X q \<and> centered X q \<and> isoconv X q \<and> onpconv X q"

abbreviation iso_spmap::"'a set \<Rightarrow> ('a set \<times> 'a) set \<Rightarrow> bool" where
  "iso_spmap X Cl \<equiv> (\<forall>A B. A \<in> Pow X \<and> B \<in> Pow X \<longrightarrow> Cl``{A} \<subseteq> Cl``{B})"

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
  "A \<in> Pow_ne X \<Longrightarrow> A \<subseteq> X \<and> A \<in> Pow X \<and> A \<noteq> {}"
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

lemma refl_subset:
  "refl R X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> refl R A"
  by (simp add: in_mono refl_def)

section SubsetRelation

lemma pwr_memI:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (A,B)\<in>pwr X"
  by (simp add:pwr_def)

lemma pwr_memI1:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (A,B)\<in>pwr X"
   using pwr_memI[of A X B] subset_trans[of A B X] by fastforce

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

lemma pwr_mem_iff:
  "(A, B) \<in> pwr X \<longleftrightarrow> (A \<subseteq> B) \<and> (B \<subseteq> X)"
  by (meson dual_order.trans pwr_memD pwr_memI)

lemma pwr_refl_sub:
  "C \<subseteq> Pow X \<Longrightarrow> refl(pwr X) C"  
  using pwr_refl[of X] refl_subset by blast

lemma powrel1[intro?]:
  "antisym_on (Pow X) (pwr X)"  
  by(auto simp add:antisym_on_def pwr_def)

lemma powrel2[intro?]:
  "trans_on (Pow X) (pwr X)"  
  by(auto simp add:trans_on_def pwr_def)

lemma powrel3[intro?]:
  "refl_on (Pow X) (pwr X)"  
  by(auto simp add:refl_on_def pwr_def)

lemma powrel4:
  "A \<subseteq> Pow X \<Longrightarrow> is_inf (pwr X) (Pow X) A (X \<inter>(\<Inter>A))" 
  unfolding is_sup_def is_greatest_def ubd_def pwr_def converse_def by(auto)

lemma powrel5[intro?]:
  "A \<subseteq> Pow X \<Longrightarrow> is_sup (pwr X) (Pow X) A (\<Union>A)" 
  unfolding is_sup_def is_greatest_def ubd_def pwr_def by auto

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
  unfolding is_sup_def is_greatest_def ubd_def pwr_def by(auto)

lemma powrel4b:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (pwr X) (Pow X) A (\<Inter>A)"
  by (simp add: pwr_ne_inf)

lemma pord_sub:
  assumes sub:"A \<subseteq> X" and por:"pord R X"
  shows pord_sub1:"pord R A" and
        pord_sub2:"pord (dual R) A"
proof-
  show P0:"pord R A"
    using antisym_on_subset[of X R A] refl_subset[of R X A] trans_on_subset[of X R A] por sub by blast
  show P1:"pord (dual R) A"
    by (simp add: P0 refl_dualI)
qed

lemma powrel_top:
  "is_greatest (pwr X) (Pow X) X"
  by (simp add: is_greatest_def pwr_memI ubd_def)

lemma powrel_bot:
  "is_least (pwr X) (Pow X) {}"
  by (simp add: is_greatest_def pwr_memI ubd_def)

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


lemma is_leastI1:
  "m \<in> lbd R A A \<Longrightarrow> is_least R A m"
  by (simp add:is_greatest_def)

lemma is_leastI2:
  "\<lbrakk>m \<in> A; A \<subseteq> X; m \<in> lbd R X A\<rbrakk> \<Longrightarrow> is_least R A m"
  unfolding is_greatest_def ubd_def by blast

lemma is_leastI3:
  "\<lbrakk>m \<in> A; (\<And>a. a \<in> A \<Longrightarrow> (m,a)\<in>R)\<rbrakk> \<Longrightarrow> is_least R A m"
  by (simp add: is_greatestI1 ubdI1)

lemma is_leastD1:
  "is_least R A m \<Longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (m,a)\<in>R) \<and> (m \<in> A)"
  by (simp add: is_greatest_def ubd_def)

lemma is_leastD2:
  "is_least R A m \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (m,a)\<in>R)"
  by (simp add: is_greatest_def ubd_def)

lemma least_unique:
  "\<lbrakk>antisym R A; is_least R A m1; is_least R A m2\<rbrakk> \<Longrightarrow> m1 =m2"
  by (simp add: antisym_onD is_leastD1)

lemma least_equalityI1:
  "\<lbrakk>antisym R A; (\<And>a. a \<in> A \<Longrightarrow> (m,a)\<in>R); m \<in> A\<rbrakk> \<Longrightarrow> Least R A = m"
  by (simp add: Least_def is_leastI3 least_unique the_equality) 

lemma least_equalityI2:
  "\<lbrakk>antisym R A; is_least R A m\<rbrakk> \<Longrightarrow> Least R A = m"
  by (simp add: is_leastD1 least_equalityI1)

lemma least_unique_witness:
  "\<lbrakk>antisym R A; is_least R A m\<rbrakk> \<Longrightarrow> \<exists>!x. is_least R A x"
  using least_unique by fastforce

lemma least_unique_ex:
  "\<lbrakk>antisym R A; \<exists>m. is_least R A m\<rbrakk> \<Longrightarrow> \<exists>!x. is_least R A x"
  using least_unique by fastforce

lemma leastI:
  assumes max:"is_least R A m" and 
          ant:"antisym R A" and
          prp:"\<And>x. is_least R A x \<Longrightarrow> Q x"
        shows "Q (Least R A)"
 using ant least_equalityI2[of A R] max prp by auto

lemma ex_leastI:
  assumes exm:"\<exists>m. is_least R A m" and 
          ant:"antisym R A" and
          prp:"\<And>x. is_least R A x \<Longrightarrow> Q x"
  shows "Q (Least R A)"
  using ant exm prp least_equalityI2[of A R] by blast


lemma ex_min:
  assumes ant:"antisym R A" and ex:"\<exists>m. is_least R A m" 
  shows ex_min0:"\<And>a. a \<in> A \<Longrightarrow> (Least R A,a)\<in>R" and
        ex_min1:"Least R A \<in> A" and
        ex_min2:"Least R A \<in> lbd R A A" and
        ex_min3:"\<And>X. A \<subseteq> X \<Longrightarrow> Least R A \<in> lbd R X A"
proof-
  show P0:"\<And>a. a \<in> A \<Longrightarrow> (Least R A,a)\<in>R" 
    using ant ex is_leastD2[of R A] least_equalityI2[of A R] by fastforce  
  show P1:"Least R A \<in> A"
    using ant ex is_leastD1[of R A] least_equalityI2[of A R] by fastforce  
  show P2:"Least R A \<in> lbd R A A" 
    using ant ex is_greatest_def[of "dual R" A] least_equalityI2[of A R] by blast
  show P3:"\<And>X. A \<subseteq> X \<Longrightarrow> Least R A \<in> lbd R X A"
    using P2 ubd_fst_iso by fastforce
qed


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

lemma is_supI4:
  "\<lbrakk>m \<in> ubd R X A;(\<And>b. b\<in>ubd R X A\<Longrightarrow>(m,b)\<in>R)\<rbrakk>\<Longrightarrow> is_sup R X A m "
  by (simp add: is_leastI3 is_supI1)

lemma upper_eq_sup_eq:
  "ubd R  X A = ubd R  X B \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (simp add: is_sup_def)

lemma upper_eq_sup_eq2:
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

lemma upper_eq_sup_eq3:
  "\<lbrakk>is_sup R X A s1;  is_sup R X B s2;ubd R X A=ubd R X B; antisym R X\<rbrakk> \<Longrightarrow> s1=s2"
  by(drule_tac ?R="R" and ?X="X" and ?A="A" and ?s1.0="s1" and ?B="B" in upper_eq_sup_eq2,simp,simp add: is_sup_unique)

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

lemma is_inf_iso1:
  "A \<subseteq> B \<Longrightarrow> is_inf R X A ma \<Longrightarrow> is_inf R X B mb \<Longrightarrow> (mb, ma)\<in>R "
  using is_sup_iso1 by fastforce

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


lemma upper_eq_sup_eq4:
  assumes ant:"antisym R X" and ex1:"\<exists>s1. is_sup R X A1 s1" and ubd_eq:"ubd R X A1 = ubd R X A2"
  shows "Sup R X A1 = Sup R X A2"
  using ant ex1 sup_equality[of R X] ubd_eq upper_eq_sup_eq2[of R X A1 _ A2] by blast

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
proof(rule upper_eq_sup_eq)
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
proof(rule upper_eq_sup_eq)
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

lemma sup_insert2:
  assumes A0:"s1 \<in> X" and 
          A1:"is_sup R X F s1" and 
          A2:"s2 \<in> X" and
          A3:"is_sup R X {s1, x} s2" and
          A4:"trans R X" and 
          A6:"F \<subseteq> X" and 
          A7:"x \<in> X"
  shows "is_sup R X (insert x F) s2"
proof-
  obtain "insert x F \<subseteq> X"
    by (simp add: A6 A7) 
  then show ?thesis 
    using A0 A1 A2 A3 A4 sup_insert[of s1 X R F s2 x] by simp
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



lemma infI:
  assumes lub:"is_inf R X A s" and 
          ant:"antisym R X" and
          prp:"\<And>x. is_inf R X A x \<Longrightarrow> Q x"
  shows "Q (Inf R X A)"
  using ant lub prp sup_equality by fastforce

lemma ex_infI:
  assumes exs:"\<exists>s. is_inf R X A s" and 
          ant:"antisym R X" and
          prp:"\<And>x. is_inf R X A x \<Longrightarrow> Q x"
        shows "Q (Inf R X A)"
  using ant exs prp sup_equality by fastforce

lemma ex_inf:
  assumes ant:"antisym R X" and ex:"\<exists>s. is_inf R X A s"
  shows ex_inf0:"\<And>a. a \<in> A \<Longrightarrow> (Inf R X A,a)\<in>R" and
        ex_inf1:"Inf R X A \<in> lbd R X A" and
        ex_inf2:"(\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (b,a)\<in>R) \<Longrightarrow> (b,Inf R X A)\<in>R)" and
        ex_inf3:"\<And>b. b \<in> lbd R X A \<Longrightarrow> (b,Inf R X A)\<in>R" and
        ex_inf4:"is_greatest R (lbd R X A) (Inf R X A)" and
        ex_inf5:"Inf R X A \<in> X"
proof-
  show P0:"\<And>a. a \<in> A \<Longrightarrow> (Inf R X A,a)\<in>R"
    using ant ex is_supD3 sup_equality by fastforce
  show P1:"Inf R X A \<in> lbd R X A"
    by (simp add: ant ex ex_sup1) 
  show P2:"(\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (b,a)\<in>R) \<Longrightarrow> (b,Inf R X A)\<in>R)"
    using ant ex is_supD5[of "dual R" X A] ex_supI[of "dual R" X A] by auto
  show P3:"\<And>b. b \<in> lbd R X A \<Longrightarrow> (b,Inf R X A)\<in>R"
    using P2 ubdD1[of _ "dual R" X A] ubdD2[of _ "dual R" X A] by blast
  show P4:"is_greatest R (lbd R X A) (Inf R X A)" 
    using ant ex is_sup_def sup_equality by fastforce
  show P5:"Inf R X A \<in> X"
    using P1 ubdD1[of _ "dual R" X A] by blast
qed


lemma inf_singleton:
  assumes A0:"antisym R X" and A1:"refl R X" and A2:"x \<in> X"
  shows inf_singleton1:"is_inf R X {x} x" and
        inf_singleton2:"Inf R X {x} = x" 
proof-
  show "is_inf R X {x} x"
    using A1 A2 is_supI3 reflD2 by fastforce 
  then show "Inf R X {x} = x" 
     by (simp add: A0 sup_equality) 
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
  assumes max:"is_maximal R A x"
  shows "\<not>(\<exists>a\<in>A. (x,a)\<in>R \<and> x\<noteq>a)"
proof(rule ccontr)
  assume cont:"\<not>\<not>(\<exists>a\<in>A. (x,a)\<in>R \<and> x\<noteq>a)" 
  then obtain a where "a \<in> A" and "(x,a)\<in>R" and xna:"x\<noteq>a"
    by blast
  then obtain "x=a" 
    using maximalD3[of R A x a] max by blast
  then show False
    by (simp add: xna)
qed
    
lemma maximalI1:
  "\<lbrakk>x \<in> A; (\<And>a. \<lbrakk>a \<in> A; (x, a) \<in> R\<rbrakk> \<Longrightarrow> a = x)\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by(simp add:is_maximal_def)


lemma maximalI2:
  assumes xia:"x \<in> A" and nex:"\<not>(\<exists>a \<in> A. (x, a)\<in>R \<and> x \<noteq> a)"
  shows "is_maximal R A x"
proof(rule maximalI1)
  show "x \<in> A" 
    by (simp add:xia)
  show "\<And>a. a \<in> A \<Longrightarrow> (x, a) \<in> R \<Longrightarrow> a = x"
    using nex by blast
qed


section SupSemilattices

lemma sup_semilatticeI1:
  "\<lbrakk>X \<noteq> {};(\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X {x1,x2} s)\<rbrakk> \<Longrightarrow>is_sup_semilattice R X"
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
    proof(rule upper_eq_sup_eq4)
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
  by (simp add: assms  bsup_ge1 bsup_le1 bsup_le2 ssl_ex_sup5)

lemma inf_iso:
  assumes ord:"ord R X" and
          isl:"is_inf_semilattice R X" and
          a1x:"a1 \<in> X" and b1x:"b1 \<in> X" and 
          a2x:"a2\<in>X" and b2x:"b2\<in>X" and 
          lt1:"(a1,b1)\<in>R" and lt2:"(a2,b2)\<in>R"
  shows "(Inf R X {a1,a2}, Inf R X {b1,b2})\<in>R"
proof-
  obtain "ord (dual R) X" and "(b1,a1)\<in>(dual R)" and "(b2,a2)\<in>(dual R)"
    by (simp add: lt1 lt2 ord)
  then show ?thesis
    using a1x a2x b1x b2x isl sup_iso[of X "dual R" b1 a1 b2 a2] converseD by fastforce
qed

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

lemma binf_assoc:
  assumes A0:"ord R X" and A1:"is_inf_semilattice R X" and A2:"x \<in> X" and A3:"y \<in> X" and A4:"z \<in> X"
  shows "Inf R X {Inf R X {x, y}, z} = Inf R X {x, y, z}"
  by (simp add: A0 A1 A2 A3 A4 bsup_as1)
 

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
  using finite_sup_closed2[of A "dual R" X E]
  by (simp add: A0 A1 A2 A3 A4 A5 A6 A7) 





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



lemma semilattice_assoc_inf:
  assumes por:"pord R X" and sem:"is_inf_semilattice R X" and
          ax:"a \<in> X" and bx:"b \<in> X" and cx:"c \<in> X" and dx:"d \<in> X"
  shows "Inf R X {Inf R X {a,b}, Inf R X {c,d}} = Inf R X {a,b,c,d}"
  by (simp add: ax bx cx dx por refl_dualI sem semilattice_assoc_sup)

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

lemma lattD42:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma dual_lattice:
  "is_lattice R X \<longleftrightarrow> is_lattice (dual R) X"
  unfolding is_lattice_def by auto

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


lemma lattice_dualization:
  assumes lat:"is_lattice R X" and por:"pord R X" and
          lem:"(\<And>R X. \<lbrakk>is_lattice R X; pord R X\<rbrakk> \<Longrightarrow> P R X)"
  shows "P (converse R) X"
  using dual_lattice lat lem por refl_dualI by fastforce

lemma lattice_fext:
  assumes ord:"ord R X" and lat:"is_lattice R X" and sub:"A \<subseteq> X" and 
          fin:"finite A" and nem:"A \<noteq> {}"
 shows l_finsup:"\<exists>s. is_sup R X A s" and
       l_fininf:"\<exists>s. is_inf R X A s"
proof-
  show P0:"\<exists>s. is_sup R X A s"
    by (simp add:assms Fpow_neI1 lattD42 ssl_fin_sup0)
  show P1:"\<exists>s. is_inf R X A s"
    by (simp add: Fpow_neI1 fin lat lattD4 nem ord ssl_fin_sup0 sub)
qed

section DistributiveLattices

lemma distr_latticeI0:
  assumes lat:"is_lattice R X" and
          dst:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  shows "distributive_lattice R X"
  by (simp add: distributive_lattice_def dst lat)

lemma distrI0:
  assumes lat:"is_lattice R X" and
          por:"pord R X" and
          dst:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" 
  shows "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  fix x y z assume x0:"x \<in> X" and y0:"y \<in> X" and z0:"z \<in> X"
  obtain iss:"is_sup_semilattice R X" and iis:"is_inf_semilattice R X" 
    using lat lattD4 by blast
  let ?yz="Inf R X {y, z}" let ?xz="Inf R X {x, z}"
  obtain yz0:"?yz \<in> X" and xz0:"?xz\<in> X" and xy0:"Sup R X {x, y} \<in> X"
    by (simp add: por x0 y0 z0 iss iis ssl_ex_sup5)  
  have B0:"Sup R X {x, ?yz} = Sup R X {Sup R X {x,?xz}, ?yz}"
    by (simp add: lat por x0 y0 z0 lat_absorb1)  (*x \<or> (x \<and> z) = ((x \<or> (x \<and> z) \<or> (z \<and> y)))*)
  also have B1:"... = Sup R X {x, Sup R X {?xz, ?yz}}"
    using por x0 y0 z0 iss yz0 xz0 bsup_assoc2[of X R x ?xz ?yz] by blast   (* x \<or> ((z \<and> x) \<or> (z \<and> y)) *)
  also have B2:"... = Sup R X {x, Sup R X {Inf R X {z, x}, Inf R X {z, y}}}"
    by (simp add: insert_commute)
  also have B3:"... = Sup R X {x, Inf R X {z, Sup R X {x, y}}}" (*x \<or> (z \<and> (x \<or> y))*)
    by (simp add: dst x0 y0 z0) 
  also have B4:"... = Sup R X {Inf R X {Sup R X {x, y}, x}, Inf R X {Sup R X {x, y}, z}}"
    by (simp add: lat por x0 y0 z0 insert_commute lat_absorb2) 
  also have B5:"... = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    by (simp add: dst x0 y0 z0 xy0)
  finally show "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    by blast
qed

lemma distrI1:
  assumes lat:"is_lattice R X" and
          por:"pord R X" and
          dst:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  shows "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" 
proof-
   fix x y z assume x0:"x \<in> X" and y0:"y \<in> X" and z0:"z \<in> X"
   also obtain "is_lattice (dual R) X" and "pord (dual R) X"
     using dual_lattice antisym_on_converse lat por refl_dualI trans_on_converse by blast
   then show "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
   using distrI0[of "dual R" X] by (simp add: dst x0 y0 z0)
qed



lemma distr_latticeE1:
  "distributive_lattice R X \<Longrightarrow> (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}})"
  by (simp add: distributive_lattice_def)

lemma dist_latticeE2:
  "\<lbrakk>distributive_lattice R X; pord R X\<rbrakk> \<Longrightarrow> (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}})" 
  using distrI1[of R X] unfolding distributive_lattice_def by blast
        

lemma distr_latticeI1:
  assumes lat:"is_lattice R X" and
          por:"pord R X" and
          dst:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  shows "distributive_lattice R X"
proof(rule distr_latticeI0)
  show "is_lattice R X" 
    using lat by simp
  show "\<And>x y z. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    using lat por dst distrI0[of R X] by blast
qed

lemma distr_latticeI2:
  assumes lat:"is_lattice R X" and
          por:"pord R X" and
          dle:"(\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R)"
  shows "distributive_lattice R X"
proof(rule distr_latticeI0)
  show "is_lattice R X" 
    using lat by simp
  show "\<And>x y z. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  proof-
    fix x y z assume x0:"x\<in>X" and y0:"y\<in>X" and z0:"z\<in>X"
    let ?a="Sup R X {x, Inf R X {y, z}}" let ?b="Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    obtain a0:"?a \<in> X" and b0:"?b \<in> X"
      by (simp add: lat lattD4 por ssl_ex_sup5 x0 y0 z0) 
    obtain ba:"(?b, ?a)\<in>R"
      using x0 y0 z0 dle[of x y z]  by blast 
    obtain ab:"(?a, ?b)\<in>R"
      by (simp add: distrib_sup_le lat por x0 y0 z0)
    then show "?a=?b"
      using por a0 b0 ba ab antisym_onD[of X R ?a ?b] by blast
  qed
qed

lemma distr_latticeI3:
  assumes lat:"is_lattice R X" and
          por:"pord R X" and
          dle:"(\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R)"
  shows "distributive_lattice R X"
proof(rule distr_latticeI1)
  show "is_lattice R X"
    by(simp add:lat)
  show "pord R X" 
    by(simp add:por)
  show "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  proof-
    fix x y z assume x0:"x\<in>X" and y0:"y\<in>X" and z0:"z\<in>X"
    let ?a="Inf R X {x, Sup R X {y, z}}" let ?b="Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    obtain a0:"?a \<in> X" and b0:"?b \<in> X"
      by (simp add: lat lattD4 por ssl_ex_sup5 x0 y0 z0) 
    obtain ba:"(?a, ?b)\<in>R"
      using x0 y0 z0 dle[of x y z]  by blast 
    obtain ab:"(?b, ?a)\<in>R"
      by (simp add: distrib_inf_le lat por x0 y0 z0)
    then show "?a=?b"
      using por a0 b0 ba ab antisym_onD[of X R ?a ?b] by blast
  qed
qed

lemma distr_latticeD:
  assumes dlt:"distributive_lattice R X" and
          x0:"x \<in> X" and y0:"y \<in> X" and z0:"z \<in> X"
  shows distr_latticeD1:"Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" and
        distr_latticeD2:"Sup R X {Inf R X {y, z}, x} = Inf R X {Sup R X {y, x}, Sup R X {z, x}}" and
        distr_latticeD3:"pord R X \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
proof-
  show P0:"Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    using dlt x0 y0 z0 insert_commute unfolding distributive_lattice_def by blast 
  show P1:"Sup R X {Inf R X {y, z}, x} = Inf R X {Sup R X {y, x}, Sup R X {z, x}}"
     by (simp add: P0 insert_commute)
  show P2:"pord R X \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  proof-
    assume "pord R X"
    then show ?thesis
      by (simp add: dist_latticeE2 dlt x0 y0 z0)
  qed
qed


lemma distr_latticeD5:
  "distributive_lattice R X \<Longrightarrow> is_lattice R X" 
  by (simp add: distributive_lattice_def)

section LatticeDuals

lemma distributive_lattice_dual:
  assumes por:"pord R X"
  shows "distributive_lattice R X  \<Longrightarrow> distributive_lattice (dual R) X"
proof-
  assume lhs:"distributive_lattice R X" 
  show "distributive_lattice (dual R) X"
  proof(rule distr_latticeI2)
    show P0:"pord (dual R) X"
      by (simp add: por refl_iff)
    have lat:"is_lattice R X"
      by (simp add: distr_latticeD5 lhs)
    show P1:"is_lattice (dual R) X"
      using dual_lattice lat by blast
    show " \<And>x y z. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> (Inf (dual R) X {Sup (dual R) X {x, y}, Sup (dual R) X {x, z}}, Sup (dual R) X {x, Inf (dual R) X {y, z}}) \<in> dual R"
    proof-
      fix x y z assume x0:"x \<in> X" and y0:"y \<in> X" and z0:"z \<in> X"
      let ?yz="Sup R X {y, z}" let ?xy="Inf R X {x, y}" let ?xz="Inf R X {x, z}"
      obtain isl:"is_sup_semilattice R X" and iis:"is_inf_semilattice R X"
        by (simp add: lat lattD4)
      obtain yz0:"?yz \<in> X" and xy0:"?xy \<in> X" and xz0:"?xz \<in> X"
        by (simp add: distr_latticeD5 lattD4 lhs por ssl_ex_sup5 x0 y0 z0)
      have B0:"Inf (dual R) X {Sup (dual R) X {x, y}, Sup (dual R) X {x, z}} = Sup R X {?xy, ?xz}"
        by (simp add: Sup_def)
      have B1:"Sup (dual R) X {x, Inf (dual R) X {y, z}} = Inf R X {x, ?yz}"
        by (simp add: Sup_def)
      have B2:"Inf R X {x, ?yz} = Sup R X {?xy, ?xz}"
        by (simp add: dist_latticeE2 lhs por x0 y0 z0)
      also obtain B3:"Inf R X {x, ?yz} \<in> X" and  B4:"Sup R X {?xy, ?xz} \<in> X"
        by (simp add: B2 isl por ssl_ex_sup5 xy0 xz0)
      then obtain B5:"(Inf R X {x, ?yz}, Sup R X {?xy, ?xz})\<in>R"
        using calculation por reflE1 by auto
      then show "(Inf (dual R) X {Sup (dual R) X {x, y}, Sup (dual R) X {x, z}}, Sup (dual R) X {x, Inf (dual R) X {y, z}}) \<in> dual R"
        using B0 B1 by force
    qed
  qed
qed

lemma distributive_lattice_dualization:
  assumes lat:"distributive_lattice R X" and por:"pord R X" and
          lem:"(\<And>R X. \<lbrakk>distributive_lattice R X; pord R X\<rbrakk> \<Longrightarrow> P R X)"
  shows "P (converse R) X"
  by (simp add: distributive_lattice_dual lat lem por refl_dualI)



section IndexedExtrema

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
      by (simp add: A0 por refl_iff sup_singleton2)
    also have B1:"{Sup R X {b, a}|a. a \<in> {a1}} = {Sup R X {b, a1}}"  by auto
    then show "Sup R X {b, (Inf R X {a1})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1}}"
      by (simp add: A0 A1 lat lattD4 por refl_iff ssl_ex_sup5 sup_singleton2)
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
       by (simp add: A0 A1 A2 distr_latticeD5 lat lattD4 por ssl_ex_sup5)
    obtain B4:"{Inf R X {b, a}|a. a \<in> {a1, a2}} = {Inf R X {b, a1}, Inf R X {b, a2}}" by blast
    then show "Inf R X {b, Sup R X {a1, a2}} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}"
      by (simp add: A0 A1 A2 distr_latticeD3 lat por)
   qed
   show P1:"\<And>a1 a2 b. \<lbrakk>a1 \<in> X; a2 \<in>X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {b, (Inf R X {a1, a2})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}" 
   proof-
     fix a1 a2 b assume A0:"a1 \<in> X" and A1:"a2 \<in> X" and A2:"b \<in> X"
     obtain B0:"is_lattice R X" and B1:"Inf R X {a1, a2} \<in> X" and B2:"Sup R X {b, a1} \<in> X" and B3:"Sup R X {b, a2}\<in>X"
       by (simp add: A0 A1 A2 distr_latticeD5 lat lattD4 por ssl_ex_sup5)
    obtain B4:"{Sup R X {b, a}|a. a \<in> {a1, a2}} = {Sup R X {b, a1}, Sup R X {b, a2}}" by blast
    then show "Sup R X {b, Inf R X {a1, a2}} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}"
      by (simp add: A0 A1 A2 distr_latticeD1 lat)
   qed
qed

lemma sup_insertE1:
  "\<And>a. is_sup R X A m \<Longrightarrow> (x, m) \<in> R \<Longrightarrow> a \<in> insert x A \<Longrightarrow> (a, m) \<in> R"
  using is_supD1 by fastforce

lemma sup_insert3:
  assumes iss:"is_sup R X A m" and xlm:"(x,m)\<in>R"
  shows "is_sup R X (insert x A) m"
proof(rule is_supI3)
  show "m \<in> X"
    using iss is_supD1[of R X A m] by simp
  show "\<And>a. a \<in> insert x A \<Longrightarrow> (a, m) \<in> R"
  proof-
    fix a assume "a \<in> insert x A" 
    then show "(a,m)\<in>R"
      using is_supD3 iss xlm by fastforce
  qed
  show"\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> insert x A \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (m, b) \<in> R"
  proof-
    fix b assume bix:"b\<in>X" and bbd:" (\<And>a. a \<in> insert x A \<Longrightarrow> (a, b) \<in> R)"
    then show "(m,b)\<in>R" 
      using iss is_supD1[of R X A m] by force
  qed
qed

lemma sup_insert4:
  assumes A0:"is_sup R X A s1" and A1:"is_sup R X {s1,x} s2" and A2:"trans R X" and A3:"A \<subseteq> X"
  shows "s2 \<in> ubd R X A"
proof(rule ubdI1)
  show P0:"s2 \<in> X"
    using A1 is_supD1 by fastforce
  show "\<And>a. a \<in> A \<Longrightarrow> (a, s2) \<in> R"
  proof-
    fix a assume aix:"a\<in>A"
    obtain "(a,s1)\<in>R" and "(s1,s2)\<in>R"
      using A0 A1 aix is_supD3 by fastforce
    also obtain "a\<in>X" and "s1\<in>X" and "s2\<in>X"
      using A0 A3 P0 aix is_supD1[of R X A s1] subsetD[of A X s1] by blast
    then show "(a, s2) \<in> R"
      using A2 calculation trans_onD[of X R a s1 s2] by blast
  qed
qed


lemma sup_insert5:
  assumes A0:"is_sup R X A s1" and A1:"is_sup R X {s1,x} s2" and A2:"trans R X" and A3:"A \<subseteq> X"
  shows "s2 \<in> (ubd R X (insert x A))"
proof(rule ubdI1)
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
    case False then obtain A5:"a \<in> A" 
        using A4 by blast 
    then show ?thesis
      using A0 A1 A2 A3 sup_insert4[of R X A s1 x s2] ubdD2[of s2 R X A a] by blast
    qed
  qed
qed


lemma sup_ubd:
  assumes A0:"is_sup R X A s1" and A1:"is_sup R X {s1,x} s2" and A2:"trans R X" and A3:"A \<subseteq> X"
  shows "is_sup R X (insert x A) s2"
proof(rule is_supI3)
  show P0:"s2 \<in> X"
    using A1 is_supD1 by fastforce
  show Pq:"\<And>a. a \<in> insert x A \<Longrightarrow> (a, s2) \<in> R"
  proof-
    fix a assume Pq0:"a \<in> insert x A"
    have " s2 \<in> ubd R X (insert x A)"
      using A0 A1 A2 A3 sup_insert5[of R X A s1 x s2] by simp
    then show "(a,s2)\<in>R"
      using Pq0 ubdD2[of s2 R X "insert x A" a]  by auto
  qed
  show "\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> insert x A \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (s2, b) \<in> R"
  proof-
    fix b assume A4:"b \<in> X" and A5:"(\<And>a. a \<in> insert x A \<Longrightarrow> (a, b) \<in> R)"
    then obtain "\<And>a. a \<in> {s1,x} \<Longrightarrow> (a,b)\<in>R" 
      using A0 is_supD1[of R X A s1] by force
    then show "(s2,b)\<in>R"
    by (meson A1 A4 is_supD1)
  qed
qed

lemma fsup_insert:
  assumes por:"pord R X"  and lat:"is_lattice R X" and fne:"F \<in> Fpow_ne X" and xmem:"x \<in> X"
  shows "Sup R X {x, (Sup R X F)} = Sup R X (insert x F)"
proof-
  let ?Fx="insert x F"
  obtain fin1:"finite F" and fsub1:"F \<subseteq> X" and fne1:"F \<noteq> {}"
    using Fpow_neD fne by auto 
  obtain fin2:"finite (?Fx)" and fsub2:"?Fx \<subseteq> X" and fne2:"?Fx \<noteq> {}"
    by (simp add: fin1 fsub1 xmem)
  obtain fne3:"?Fx \<in> Fpow_ne X"
    using Fpow_neI1 fin2 fsub2 by blast
  obtain B0:"is_sup R X F (Sup R X F)" and B1:" is_sup R X ?Fx (Sup R X ?Fx)"
    by (simp add: fne fne3 lat lattD4 por ssl_fin_sup7)
  then obtain B2:"is_sup R X ?Fx (Sup R X {x,Sup R X F})"
    by (simp add: fsub1 insert_commute is_supD1 lat lattD32 por sup_ubd xmem)
  then show ?thesis
    by (simp add: por sup_equality)
qed

lemma distr_finite2:
  assumes 
    A0:"b \<in> X" and
    A1: "\<And>a1 a2. \<lbrakk>a1\<in>X;a2\<in>X\<rbrakk>\<Longrightarrow>Inf R X {b,(Sup R X {a1,a2})}=Sup R X {Inf R X {b,a}|a. a\<in>{a1,a2}}" and 
    A2:"finite A" and
    A3:"A \<noteq> {}" and
    A4:"A \<subseteq> X" and
    A5:"distributive_lattice R X" and 
    A6:"pord R X"         
  shows "Inf R X {b, (Sup R X A)} = Sup R X {Inf R X {b, a}|a. a \<in> A}"
  using A2 A3 A4 A1 A0
proof (induct A rule: finite_ne_induct)
  case (singleton x) 
  then show ?case 
    using A5 by fastforce 
next
  case (insert x F)
  obtain P0:"x \<in> X" and P1:"F \<subseteq> X" and P2:"finite F" and P3:"F \<noteq> {}"
    using insert.hyps(1,2) insert.prems(1) by blast
  obtain lat:"is_lattice R X" and dor:"pord (dual R) X"
    by (simp add: A5 A6 distr_latticeD5 refl_iff)
  obtain ssl:"is_sup_semilattice R X" and isl:"is_inf_semilattice R X"
    by (simp add: lat lattD4)
  let ?ba="{Inf R X {b, a} |a. a \<in> F}" and ?xba="{Inf R X {b, a}|a. a \<in> (insert x F)}"
  let ?s="Sup R X F" and ?sba="Sup R X ?ba" and ?sxba="Sup R X ?xba"
  have P4:"?ba \<subseteq> X" 
  proof
    fix z assume "z \<in> ?ba" 
    then obtain a where "a \<in> F" and "z=Inf R X {b,a}" 
      by blast
    also obtain "a \<in> X"
      using P1 calculation by auto
    then show "z \<in> X" 
      using A0 P1 dor isl ssl_ex_sup5[of X "dual R"] calculation by blast
  qed
  have P5:"?xba \<subseteq> X" 
  proof
    fix z assume "z \<in> ?xba" 
    then obtain a where "a \<in> (insert x F)" and "z=Inf R X {b,a}" 
      by blast
    also obtain "a \<in> X"
      using calculation(1) insert.prems(1) by auto
    then show "z \<in> X"
      using A0 calculation dor isl ssl_ex_sup5[of X "dual R"] by blast
  qed
  have P6:"finite ?ba"
    using P2 by force
  have P7:"finite ?xba"  
    by (simp add: insert.hyps(1))
  have P8:"?xba = {Inf R X {b, x}} \<union> ?ba" 
    by auto
  have P9:"Inf R X {b, x} \<in> X"
    using P5 by blast
  have P10:"?ba \<noteq> {}"  
     using P3 by blast
  have P11:"?xba \<noteq> {}" 
     using P3 by blast
  have P12:"?sba \<in> X"
    using A6 Fpow_neI1 P10 P4 P6 ssl ssl_fin_sup6 by fastforce
  have P13:"?sxba \<in> X"
    using A6 P11 P5 P7 ssl ssl_fin_sup6[of X R ?xba] Fpow_neI1[of ?xba X] by blast 
  let ?s2=" (Sup R X {(?sba), (Inf R X {b, x})})"
  have P14:"?s2 \<in> X"
    by (simp add: A6 P12 P9 ssl ssl_ex_sup5)
  have B0:"Inf R X {b, ?s} = ?sba"  
    using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Inf R X {b, (Sup R X {?s, x})} = Sup R X {(Inf R X {b, ?s}), (Inf R X {b, x})}"
    by (simp add: A0 A5 A6 Fpow_neI1 P0 P1 P2 P3 distr_latticeD3 ssl ssl_fin_sup6)
  have B2:"... = Sup R X {(?sba), (Inf R X {b, x})}"  
    using B0 by fastforce
  have B3:"... = Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" 
      by blast
    have B5:"is_sup R X ?ba ?sba"
      using A6 Fpow_neI1 P10 P4 P6 ssl ssl_fin_sup7 by fastforce
    have B6s:"{Inf R X {b, x}, ?sba}={?sba, Inf R X {b,x}}"
      by (simp add: doubleton_eq_iff)
    have B6:"is_sup R X {Inf R X {b, x},?sba} (Sup R X {(Inf R X {b, x}), (?sba)})"
      by (simp add: A6 P12 P9 lat lattD32)
    have B7:"is_sup R X {Inf R X {b, x},?sba} ?s2"
      using B6 B6s by auto 
    have B8:"is_sup R X (insert (Inf R X {b, x}) ?ba) ?s2"
      using A6 B5 B6 B6s P12 P14 P4 P9 sup_insert2[of _ X R " {Inf R X {b, a} |a. a \<in> F}" ?s2 "Inf R X {b, x}"] by fastforce
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
      by (simp add: A6 Fpow_neI1 P0 P1 P2 P3 fsup_insert lat ssl ssl_ex_sup6 ssl_fin_sup6)
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


section CompleteLattices

lemma is_clatticeI1:
  "\<lbrakk>X \<noteq> {}; (\<And>A. A\<subseteq>X\<Longrightarrow>(\<exists>s. is_sup R X A s))\<rbrakk>\<Longrightarrow>is_clattice R X"
  by (simp add: is_clattice_def)

lemma clatI1:
  assumes css:"is_csup_semilattice R X" and cis:"is_cinf_semilattice R X"
  shows "is_clattice R X"
proof(rule is_clatticeI1)
  show " X \<noteq> {}"
    using css is_csup_semilattice_def by blast
  show "\<And>A. A \<subseteq> X \<Longrightarrow> \<exists>s. is_sup R X A s"
  proof-
    fix A assume asub:"A \<subseteq> X"
    show "\<exists>s. is_sup R X A s"
    proof(cases "A={}")
      case True
      then obtain l where "is_least R X l"
        using cis dual_order.refl is_cinf_semilattice_def is_infD1 sup_maxI1 by metis
      then show ?thesis
        using True sup_empty by fastforce
    next
      case False
      then show ?thesis
        using asub css is_csup_semilattice_def by blast
    qed
  qed
qed
  

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

lemma cisdual:
  " is_cinf_semilattice R X \<Longrightarrow>  is_csup_semilattice (dual R) X"
  by (simp add: is_cinf_semilattice_def is_csup_semilattice_def)

lemma cssdual:
  " is_csup_semilattice R X \<Longrightarrow>  is_cinf_semilattice (dual R) X"
  by (simp add: is_cinf_semilattice_def is_csup_semilattice_def)

lemma clatD22:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (metis converse_converse is_clattice_def sup_if_inf_ub ubd_space)

lemma clatD1:
  "is_clattice R X \<Longrightarrow> is_csup_semilattice R X"
  by (simp add: is_clattice_def is_csup_semilattice_def)

lemma clatD2:
  "is_clattice R X \<Longrightarrow> is_cinf_semilattice R X"
  by (metis inf_if_sup_lb is_cinf_semilattice_def is_clattice_def ubd_space)

lemma cltdual:
  "is_clattice R X \<Longrightarrow> is_clattice (dual R) X"
  using cisdual clatD1 clatD2 clatI1 cssdual by blast


lemma csupD3:
  "is_csup_semilattice R X \<Longrightarrow> (\<exists>x. is_greatest R X x)"
  by (metis dual_order.refl is_csup_semilattice_def is_supD1 sup_maxI1)

lemma cinfD4:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf R X A (Inf R X A)"
  by (metis cinfD2 inf_equality)

lemma clatD41:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (simp add: clatD1 csupD4)

lemma cinfD50:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf R X A) \<in> X"
  by (meson cinfD4 is_supD1)

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
  by (simp add: cinf_sinf clatD1 clatD2 csup_fsup lattI2)

lemma sup_iso1b:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis bot.extremum_uniqueI csupD4 dual_order.trans is_sup_iso1)

lemma sup_iso1:
  "\<lbrakk>ord R X;is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis clatD21 dual_order.trans is_sup_iso1 sup_equality)

lemma inf_iso1b:
  assumes ord:"ord R X" and cis:"is_cinf_semilattice R X" and
          asb:"A \<subseteq> B" and bsx:"B \<subseteq> X" and ane:"A \<noteq> {}"
  shows "(Inf R X B, Inf R X A)\<in>R"
proof-
  obtain dord:"ord (dual R) X" and css:"is_csup_semilattice (dual R) X"
    by (simp add: cis cisdual ord)
  then obtain "(Sup (dual R) X A, Sup (dual R) X B)\<in>(dual R)"
    using ane asb bsx sup_iso1b by blast
  then show ?thesis
    by simp
qed

lemma inf_iso1:
  assumes ord:"ord R X" and cis:"is_clattice R X" and
          asb:"A \<subseteq> B" and bsx:"B \<subseteq> X"
  shows "(Inf R X B, Inf R X A)\<in>R"
proof-
  obtain dord:"ord (dual R) X" and css:"is_clattice (dual R) X"
    by (simp add: cis cltdual ord)
  then obtain "(Sup (dual R) X A, Sup (dual R) X B)\<in>(dual R)"
    using ord asb bsx sup_iso1 by blast
  then show ?thesis
    by simp
qed

lemma sup_iso2:
  assumes ord:"ord R X" and clx:"is_clattice R X" and cly:"is_clattice R Y" and
          asy:"A \<subseteq> Y" and ysx:"Y \<subseteq> X" and yne:"Y \<noteq> {}"
  shows "(Sup R X A, Sup R Y A)\<in>R"
proof-
  obtain sxa sya where sx:"is_sup R X A sxa" and sy:"is_sup R Y A sya"
    using clx cly is_clattice_def[of R X]  is_clattice_def[of R Y] order_trans[of A Y X] asy ysx by presburger
  then obtain "(sxa, sya)\<in>R"
    using asy ysx is_sup_iso2[of A Y X R sya sxa] by simp
  then show ?thesis
    by (metis antisym_on_subset ord sup_equality sx sy ysx)
qed

lemma clatD4:
  "\<lbrakk>ord R X; is_clattice R X;  A \<subseteq> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A \<Longrightarrow> (Sup R X A, b) \<in> R "
  by (simp add: clatD21 ex_sup3)

lemma is_clatticeI2:
  "(\<And>A. A \<in> Pow X \<Longrightarrow> (\<exists>s. is_sup R X A s) \<and> (\<exists>i. is_inf R X A i)) \<Longrightarrow> is_clattice R X"
  by (metis Pow_iff empty_iff empty_subsetI is_clattice_def is_supD4)

lemma pow_is_clattice:
  "is_clattice (pwr X) (Pow X)"
  by (meson Pow_not_empty is_clattice_def pwr_ar_sup)

section Isotonicity

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
proof(rule ubdI1)
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

section Extensivity

lemma extensiveI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (x, f x) \<in> R) \<Longrightarrow> extensive R X f" 
  by (simp add:extensive_def)

lemma extensiveD1:
  "extensive R X f \<Longrightarrow> x \<in> X \<Longrightarrow> (x, f x) \<in> R" 
  by (simp add:extensive_def)


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
  
lemma is_iso_extD1:
  "\<lbrakk>isotone R X R f;  extensive R X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x))\<in>R"
  by (simp add: extensive_def image_subset_iff)

lemma is_iso_sup:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A x \<Longrightarrow> is_sup R (f`X) (f`A) y  \<Longrightarrow> (y, f x)\<in>R"
  by (meson is_supD2 is_supD6 isotoneD41)

lemma is_iso_inf:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf R X A x \<Longrightarrow> is_inf R (f`X) (f`A) y  \<Longrightarrow> (f x,y)\<in>R"
  using  dual_isotone[of R X R f] is_iso_sup[of "dual R" X f A x y] by blast

section Idempotency

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

section Closures 

lemma closureI1:
  "\<lbrakk>extensive R X f; idempotent X f; isotone R X R f; (f`X \<subseteq> X)\<rbrakk> \<Longrightarrow> closure R X f"
  by (simp add: closure_def)

lemma closureI3:
  "\<lbrakk>pord R X; extensive R X f; f`X \<subseteq> X;  closure_cond R X f\<rbrakk> \<Longrightarrow> closure R X f"
  using closure_def[of R X f] idempotentI3[of X R f] isotoneI2[of R X f] by simp

lemma closureD:
  "closure R X f \<Longrightarrow> extensive R X f \<and> idempotent X f \<and> isotone R X R f \<and> (f`X \<subseteq> X)"
  by (simp add: closure_def)

section ClosureRanges
lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R C {x}) c)) \<rbrakk> \<Longrightarrow> clr R X C"
  by (simp add:closure_range_def)

lemma clrD1:
  "clr R X C \<Longrightarrow> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least R (ubd R C {x}) c)) "
  by (simp add:closure_range_def)

lemma clrD2:
  "clr R X C \<Longrightarrow> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_sup R C {x} c)) "
  by (simp add: closure_range_def is_sup_def)

lemma clrD3:
  "\<lbrakk>clr R X C; antisym R X\<rbrakk>\<Longrightarrow>antisym R C"
  using antisym_on_subset[of X R C] clrD1[of R X C] by simp

lemma clrD4:
  "\<lbrakk>clr R X C; antisym R X\<rbrakk>\<Longrightarrow>antisym R (ubd R C {x})"
  using antisym_on_subset[of C R "ubd R C {x}"] clrD3[of R X C] ubd_space[of R C "{x}"] by simp

lemma clr_equality:
  "\<lbrakk>antisym R X; clr R X C; is_least R (ubd R C {x}) c\<rbrakk> \<Longrightarrow> cl_from_clr R C x = c"
  by (simp add: cl_from_clr_def clrD4 least_equalityI2)

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
      using is_leastD1[of R "ubd R C {x}" y] ubdD2[of y R C "{x}"] singleton_iff by blast
  qed
  next
  show B1:"C \<subseteq> (cl_from_clr R C)`X"
  proof
    fix y assume B10:"y \<in> C"
    then obtain "is_least R (ubd R C {y}) y"
      using A0 A1 A2 clrD3[of R X C] is_sup_def[of R C "{y}" y] sup_singleton1[of C R y] by blast
    also obtain "y \<in> X"  
      using A2 B10 clrD1 by blast
    then show "y \<in> (cl_from_clr R C)`X"
      using A1 A2 calculation clr_equality[of X R C y y] 
        rev_image_eqI[of y X y "cl_from_clr R C"]  by presburger
  qed
qed


lemma clr_induced_cl:
  assumes por:"pord R X" and
          isc:"clr R X C"
  shows clr_map:"cl_from_clr R C ` X \<subseteq> X" and
        clr_iso:"isotone R X R (cl_from_clr R C)" and
        clr_ext:"extensive R X (cl_from_clr R C)" and
        clr_ide:"idempotent X (cl_from_clr R C)" and
        clr_icl:"closure R X (cl_from_clr R C)"
proof-
  obtain B0:"C \<subseteq> X"
    using clrD1 isc by auto
  then obtain B1:"refl R C" and B2:"trans R C"
    using por pord_sub1 by blast
  then show P0:"cl_from_clr R C ` X \<subseteq> X" 
    by (simp add: B0 por isc clr_induced_closure_id)
  show P1:"isotone R X R (cl_from_clr R C)"
  proof(rule isotoneI1)
    fix x1 x2 assume A4:"x1 \<in> X" and A5:"x2 \<in> X" and A6:"(x1,x2)\<in>R"
    then obtain B30:"ubd R C {x2} \<subseteq> ubd R C {x1}" 
      using ubd_iso3[of x1 X x2 R C] por B0 by fastforce
    obtain c1 where B31:"is_least R (ubd R C {x1}) c1"
      using A4 clrD1[of R X C] isc by blast
    obtain c2 where B32:"is_least R (ubd R C {x2}) c2"
      using A5 clrD1[of R X C] isc by blast
    obtain B33:"(c1,c2)\<in>R"  
      using B30 B31 B32 is_greatest_iso2[of "ubd R C {x2}" "ubd R C {x1}"] converse.simps by blast
    then show "(cl_from_clr R C x1, cl_from_clr R C x2) \<in> R" 
      using por isc B31 B32 clr_equality by fastforce
  qed
  show P2:"extensive R X (cl_from_clr R C)"
  proof(rule extensiveI1)
    fix x assume A7:"x \<in> X"
    then obtain c where A8:"is_least R (ubd R C {x}) c"
      using clrD1 isc by blast
    then obtain "c \<in> ubd R C {x}"
      by (simp add: is_leastD1) 
    then  obtain "(x,c)\<in>R"
      by (simp add: ubd_singleton_mem) 
    also have "cl_from_clr R C x=c"
      using por isc A8 clr_equality[of X R C x c] by blast
    then show "(x, cl_from_clr R C x)\<in>R"
      using calculation by blast
  qed
  show P3:"idempotent X (cl_from_clr R C)"
  proof(rule idempotentI1)
    fix x assume A8:"x \<in> X"
    then obtain xc where B0:"xc \<in> X" and B1:"is_least R (ubd R C {x}) xc"
      by (metis por isc P0 clrD1 clr_equality image_subset_iff) 
    have B2:"is_least R (ubd R C {xc}) xc"
    proof(rule is_leastI3)
      show "xc \<in> ubd R C {xc}"
        by (meson B1 is_greatestD1 is_leastD2 ubd_singleton_mem)
      show "\<And>a. a \<in> ubd R C {xc} \<Longrightarrow> (xc, a) \<in> R"
        by (simp add: ubd_singleton_mem)
    qed
    then show "cl_from_clr R C (cl_from_clr R C x) = cl_from_clr R C x"
      using B1 por clr_equality isc by fastforce 
  qed
  show P4:"closure R X (cl_from_clr R C)"
    by (simp add: P0 P1 P2 P3 closureI1)
qed


lemma cl_is_closure:
  assumes ref:"refl R C" and
          ant:"antisym R X" and
          trn:"trans R X" and
          isc:"clr R X C"
  shows "closure R X (cl_from_clr R C)"
proof(rule closureI1)
  obtain B0:"C \<subseteq> X"
    using clrD1 isc by auto
  then obtain B1:"refl R C" and B2:"trans R C"
    using ref trans_on_subset trn by auto
  then show B3:"cl_from_clr R C ` X \<subseteq> X" 
    by (simp add: B0 ant isc clr_induced_closure_id)
  show B4:"isotone R X R (cl_from_clr R C)"
  proof(rule isotoneI1)
    fix x1 x2 assume A4:"x1 \<in> X" and A5:"x2 \<in> X" and A6:"(x1,x2)\<in>R"
    then obtain B30:"ubd R C {x2} \<subseteq> ubd R C {x1}" 
      using ubd_iso3[of x1 X x2 R C] trn B0 by fastforce
    obtain c1 where B31:"is_least R (ubd R C {x1}) c1"
      using A4 clrD1[of R X C] isc by blast
    obtain c2 where B32:"is_least R (ubd R C {x2}) c2"
      using A5 clrD1[of R X C] isc by blast
    obtain B33:"(c1,c2)\<in>R"  
      using B30 B31 B32 is_greatest_iso2[of "ubd R C {x2}" "ubd R C {x1}"] converse.simps by blast
    then show "(cl_from_clr R C x1, cl_from_clr R C x2) \<in> R" 
      using ant isc B31 B32 clr_equality by fastforce
  qed
  show B5:"extensive R X (cl_from_clr R C)"
  proof(rule extensiveI1)
    fix x assume A7:"x \<in> X"
    then obtain c where A7b:"is_least R (ubd R C {x}) c"
      using isc clrD1[of R X C]  by presburger
    from A7 obtain A7d:"C \<noteq> {}" and A7e:"C \<subseteq> X "
      using isc clrD1[of R X C]  by simp 
    show "(x, cl_from_clr R C x)\<in>R"
      using A7b ant isc clr_equality[of X R C x c] is_leastD1[of R "ubd R C {x}" c]   
            ubdD2[of "cl_from_clr R C x" R C "{x}" x]  insertCI
      by blast
  qed
  show "idempotent X (cl_from_clr R C)"
  proof(rule idempotentI1)
    fix x assume A8:"x \<in> X"
    then obtain xc where B0:"xc \<in> X" and B1:"is_least R (ubd R C {x}) xc"
      by (metis ant isc B3 clrD1 clr_equality image_subset_iff) 
    have B2:"is_least R (ubd R C {xc}) xc"
    proof(rule is_leastI3)
      show "xc \<in> ubd R C {xc}"
        by (meson B1 is_greatestD1 is_leastD2 ubd_singleton_mem)
      show "\<And>a. a \<in> ubd R C {xc} \<Longrightarrow> (xc, a) \<in> R"
        by (simp add: ubd_singleton_mem)
    qed
    then show "cl_from_clr R C (cl_from_clr R C x) = cl_from_clr R C x"
      using B1 ant clr_equality isc by fastforce 
  qed
qed


lemma cl_is_closure2:
  assumes por:"pord R X" and
          isc:"clr R X C"
  shows "closure R X (cl_from_clr R C)"
proof-
  obtain B0:"C \<subseteq> X"
    using clrD1 isc by auto
  then obtain ref:"refl R C" and ant:"antisym R X" and trn:"trans R X"
    by (simp add: por pord_sub1)
  then show ?thesis
    using ref ant trn isc cl_is_closure[of R C X]  by simp
qed

lemma closure_is_clr:
  assumes A0:"antisym R X" and A1:"closure R X f" and A2:"X \<noteq> {}"
  shows closure_is_clr1:"f ` X \<noteq> {}"  and 
        closure_is_clr2:"f ` X \<subseteq> X" and
        closure_is_clr3:"\<And>x. x \<in> X \<Longrightarrow>is_least R (ubd R (f`X) {x}) (f x)" and
        closure_is_clr4:"\<And>x. x \<in> X \<Longrightarrow> \<exists>c. is_least R (ubd R (f ` X) {x}) c" and
        closure_is_clr5:"clr R X (f`X)"
proof-
  show B0:"f ` X \<noteq> {}"
    by (simp add: A2)
  show B1:"f ` X \<subseteq> X"
    using A1 closureD by blast
  show B2:"\<And>x. x \<in> X \<Longrightarrow> is_least R (ubd R (f`X) {x}) (f x)"
  proof-
    fix x assume A3:"x \<in> X"
    obtain B20:"extensive R X f" and B21:"isotone R X R f" and B22:"idempotent X f" 
      using A1 closureD by blast 
    show B23:"is_least R (ubd R (f`X) {x}) (f x)"
    proof(rule is_greatestI3)
      show "f x \<in> ubd R (f ` X) {x}"
         by (meson A3 B20 extensiveD1 image_eqI ubd_singleton_mem)
      show "\<And>a. a \<in> ubd R (f ` X) {x} \<Longrightarrow> (a, f x) \<in> dual R"   
        by (metis A3 B1 B21 B22 converseI idempotent_isotoneD1 ubd_singleton_mem)
    qed
  qed
  then show B3:"\<And>x. x \<in> X \<Longrightarrow> \<exists>c. is_least R (ubd R (f ` X) {x}) c" 
    by blast
  show "clr R X (f`X)"  
    using B0 B1 B3 closure_range_def by blast
qed


lemma closure_induced_clr_id:
  "\<lbrakk>antisym R X; closure R X f; X \<noteq> {};x\<in>X\<rbrakk>  \<Longrightarrow> (cl_from_clr R (f`X)) x = f x"
  by (simp add: closure_is_clr3 closure_is_clr5 clr_equality)

lemma closure_induced_clr_dual:
  assumes ant:"antisym R X" and cl1:"closure R X f1" and cl2:"closure R X f2" and
          leq:"\<And>x. x \<in> X \<Longrightarrow> (f1 x,f2 x)\<in>R"
  shows "(f2`X) \<subseteq> (f1`X)"
proof
  fix y assume y0:"y \<in> f2`X" 
  obtain y1:"y \<in> X"
    using y0 cl2 closureD by blast
  obtain y2:"(y, f1 y)\<in>R"
    using cl1 y1 closureD[of R X f1] extensiveD1[of R X f1 y] by simp
  obtain y3:"(f1 y, y)\<in>R"
    using cl2 closureD[of R X f2] idempotentD3[of X f2 y] leq[of y] y0 y1 by simp
  obtain y4:"f1 y \<in> X"
    using cl1 closureD y1 by blast
  from y1 y2 y3 y4 obtain "f1 y = y"
    using ant antisym_onD[of X R "f1 y" y] by simp
  then show "y \<in> f1`X"
    using y1 by force
qed
                    
lemma clr_induced_closure_dual:
  "\<lbrakk>refl R C; antisym R X;clr R X C1; clr R X C2; C2 \<subseteq> C1; x \<in> X\<rbrakk> \<Longrightarrow> (((cl_from_clr R C1) x),((cl_from_clr R C2) x))\<in>R"
  using clrD1 clr_equality converseD is_greatest_iso2 ubd_fst_iso by metis

lemma extensiveI4:
  "refl R X \<Longrightarrow> (\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> extensive R X f"
proof(rule extensiveI1)
  fix x assume A0:"refl R X" and A1:"(\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R)"  and 
              A2:" f`X \<subseteq> X" and A3:"x \<in> X"
  then obtain B0:"is_sup R X {x} x" and B1:"{x} \<subseteq> X"
    by (simp add: is_greatestI2 reflD2 sup_maxE1 ubd_singleton_mem)
  then show "(x, f x) \<in> R"  
    using A1 by presburger  
qed

lemma idempotentI4:
  assumes A0:"refl R X" and
          A1:"antisym R X" and 
          A2:"(\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup R X A s1 \<Longrightarrow> is_sup R X (f`A) s2 \<Longrightarrow> f s1 = f s2)" and
          A3:"f`X \<subseteq> X" 
  shows "idempotent X f"
proof(rule idempotentI1)
  fix x assume A5:"x \<in> X"
  obtain B0:"is_sup R X {x} x" and B1:"{x} \<subseteq> X" and B2:"f x \<in> X"
    by (metis A0 A1 A3 A5 empty_subsetI image_subset_iff insert_subsetI sup_singleton1)
  then obtain B3:"is_sup R X ({f x}) (f x)"
    by (simp add: A0 A1 sup_singleton1) 
  then obtain B4:"is_sup R X (f`{x}) (f x)" 
    by force
  then show "f (f x) = f x"  
    by (metis A2 B0 B1)
qed


lemma isotoneI4:
  assumes A0:"(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s))" and A1:"f`X \<subseteq>X " and A2:"refl R X"
  shows "isotone R X R f"
proof(rule isotoneI1)
  show "\<And>x1 x2. \<lbrakk>x1 \<in> X;x2 \<in> X; (x1, x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
  proof-
    fix x1 x2 assume A3:"x1 \<in> X" and A4:"x2 \<in> X" and A5:"(x1,x2)\<in>R"
    have B01:"is_sup R X {x1, x2} x2"
      by (metis A2 A4 A5 is_supI3 refl_def singletonD singletonI sup_insert3)
    have B02:"is_sup R (f`X) (f`{x1, x2}) (f x2)" 
      by (meson A0 A3 A4 B01 empty_subsetI insert_subset)
    then show "(f x1, f x2)\<in>R"   
      by (simp add: is_supD3) 
  qed
qed

lemma induced_clr_props:
  assumes A0:"refl R X" and A1:"antisym R X" and A2:"clr R X C" and A3:"A \<subseteq> C" and A4:"is_inf R X A i"
  shows clrD8:"(cl_from_clr R C) i \<in> lbd R X A" and
        clrD9:"((cl_from_clr R C) i,i)\<in>R" and
        clrD10:"(cl_from_clr R C) i = i" and
        clrD11:"i \<in> C"
proof-
  obtain c where B0:"is_least R (ubd R C {i}) c" 
    by (meson A2 A4 clrD1 is_supD1)
  then obtain B1:"c \<in> X" and B2:"cl_from_clr R C i \<in> X"
    by (metis A1 A2 clrD1 clr_equality is_greatestD1 subsetD ubd_space)
  show B3:"(cl_from_clr R C) i \<in> lbd R X A"
  proof(rule ubdI1)
    show B30:"cl_from_clr R C i \<in> X" 
       by (simp add:B2)
    show B31:"\<And>a. a \<in> A \<Longrightarrow> (a, cl_from_clr R C i) \<in> dual R"
      by (metis A1 A2 A3 A4 B0 clr_equality is_greatestD4 is_infD1 subsetD ubd_singleton_mem) 
  qed
  show B4:"((cl_from_clr R C) i,i)\<in>R" 
    using A4 B3 is_supD2 by fastforce 
  show B5:"(cl_from_clr R C) i = i"
    by (metis A1 A2 A4 B0 B2 B4 antisym_on_def clr_equality is_greatestD3 is_supD4 ubdD1 ubd_singleton_mem) 
  show B6:"i \<in> C" 
    by (metis A1 A2 B0 B5 clr_equality is_supD1 sup_empty ubdD1)
qed

lemma moore_clI1:
  assumes A0:"C \<subseteq> Pow X" and
          inf_closed:"(\<And>E. E \<subseteq> C\<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C)" 
  shows "clr (pwr X) (Pow X) C"
proof(rule clrI1)
  show B0:"C \<noteq> {}"  using inf_closed by blast
  show B1:"C \<subseteq> Pow X" by(simp add:A0)
  show B2:"\<And>x. x \<in> Pow X \<Longrightarrow> \<exists>c. is_least (pwr X) (ubd (pwr X) C {x}) c"
  proof-
    fix x assume A1:"x \<in> Pow X"
    let ?c="(X \<inter> (\<Inter>(ubd (pwr X) C {x})))"
    obtain B20:"?c \<in> C"  
      by (simp add: inf_closed ubd_space)
    have B21:"is_least (pwr X) (ubd (pwr X) C {x})  ?c"
    proof(rule is_greatestI3)
      show B22:"?c \<in> ubd (pwr X) C {x}" 
      proof(rule ubdI1)
        show "?c \<in> C" 
           by (simp add:B20)
        obtain "x \<subseteq> ?c"
          using A1 Int_subset_iff PowD le_Inf_iff ubd_singleton_mem
          by (metis (no_types, lifting) pwr_memD)
        then show "\<And>a. a \<in> {x} \<Longrightarrow> (a, ?c) \<in> pwr X"   
          by (simp add: pwr_memI)
      qed
      show B23:"\<And>a. a \<in> ubd (pwr X) C {x} \<Longrightarrow> (a,?c) \<in> dual (pwr X)"
      proof-
        fix a assume aub:"a \<in> ubd (pwr X) C {x} "
        then obtain "?c \<subseteq> a" and "a \<in> C"
          by (simp add: Inf_lower le_infI2 ubd_singleton_mem)
        then obtain "(?c, a)\<in> pwr X"
          using pwr_memI1[of ?c a X] A1 B1 by blast
        then show " (a,?c) \<in> dual (pwr X)"
          by force
      qed
    qed
    then show "\<exists>c. is_least (pwr X) (ubd (pwr X) C {x}) c" 
      by blast
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
  obtain B0:"C \<subseteq> X" and B1:"A \<subseteq> X" 
    using A0 A5 clrD1 by blast
  then obtain i where B2:"is_inf R X A i" 
    using A1 A2 A4 A6 cinfD2 by blast
  then obtain B3:"i \<in> C"  
    by (meson A0 A2 A3 A5 clrD11)
  have B4:"is_inf R C A i"
  proof(rule is_supI3)
    show "i \<in> C" 
      by (simp add:B3)
    show "\<And>a. a \<in> A \<Longrightarrow> (a, i) \<in> dual R"  
      by (meson B2 is_supD3)
    show "\<And>b. b \<in> C \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> dual R) \<Longrightarrow> (i, b) \<in> dual R" 
      by (meson B0 B2 is_supD1 subsetD)
  qed
  from B2 B4 show ?thesis 
    by blast
qed
   


lemma clr_clattice:
  assumes A0:"clr R X C" and A1:"is_clattice R X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows clr_clattice1:"\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)" and
        clr_clattice2:"is_clattice R C"
proof-
  show "\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"
  proof-
    fix A assume A2:"A \<subseteq> C" then have B0:"A \<subseteq> X" 
      using A0 clrD1 by blast
    also have B1:"ubd R C A \<subseteq> X" 
      by (meson A0 clrD1 dual_order.trans ubd_space)
    then obtain x where B2:"is_inf R X (ubd R C A) x" 
      using A1 A4 assms(3) clatD22 by blast
    then have B1:"is_sup R C A x"   
      by (metis A0 A2 A3 assms(3) clrD11 clrD1 converse_converse inf_if_sup_lb sup_in_subset ubd_space)
    then show "(\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"  
      using B2 by auto
  qed
  then show "is_clattice R C" 
    by (metis A0 closure_range_def is_clattice_def)
qed


section Directedness

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
  case (insert x F) obtain c1 where P0:"c1 \<in> X" and P1:"(\<forall>a. a\<in>F\<longrightarrow>(a,c1)\<in>R)" 
    using insert.hyps(4) insert.prems by blast
  then obtain c2 where P2:"c2\<in>X" and P3:"(c1, c2) \<in> R \<and> (x, c2) \<in> R"  
    by (meson A0 insert.prems insert_subset)
  then have P4:"\<And>a. a \<in> (insert x F)\<Longrightarrow>(a, c2) \<in> R"
  proof-
    fix a assume P5:"a\<in>(insert x F)"
    show "(a,c2)\<in>R"
    proof(cases "a=x")
      case True 
      then show ?thesis 
        by (simp add: P3)
    next
      case False  
      then show ?thesis  
        by (meson A4 P0 P1 P2 P3 P5 in_mono insert.prems insertE trans_onD)
    qed
  qed
  then show ?case  
    using P2 by blast
qed


lemma inf_dwdir:
  "is_sup_semilattice R X \<Longrightarrow> is_dir X R" and
  "is_inf_semilattice R X \<Longrightarrow> is_dir X (converse R)" 
proof-
  show "is_sup_semilattice R X \<Longrightarrow> is_dir X R"
  proof(rule is_dirI1)
    fix a b assume A0:"is_sup_semilattice R X" and A1:"a\<in>X" and A2:"b\<in>X"
    then obtain c where "is_sup R X {a,b} c"
      by (meson sup_semilattice_ex1)
    then show "\<exists>c\<in>X. (a, c) \<in>  R \<and> (b, c) \<in> R" 
      by (meson insertCI is_supD1)
  qed
  show "is_inf_semilattice R X \<Longrightarrow> is_dir X (converse R)"
  proof(rule is_dirI1)
    fix a b assume A0:"is_inf_semilattice R X" and A1:"a\<in>X" and A2:"b\<in>X"
    then obtain c where "is_inf R X {a,b} c"
      by (meson sup_semilattice_ex1) 
    then show "\<exists>c\<in>X. (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
      by (meson insertCI is_supD1)
  qed
qed
  
section OrderClosure
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

section FiltersDefinitionAndBasicProps

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
  obtain f where B0:"f \<in> F" 
    by (metis A0 ex_in_conv is_filterD1)
  then obtain B1:"f \<in> X" and B2:"(f,top)\<in>R"  
    by (meson A1 assms is_greatestD1 in_mono is_filterD1)
  then show "top \<in> F" 
    by (meson A1 B0 assms is_greatestD1 is_filterD1 is_ord_clE1)
qed


lemma top_filters2:
 "\<lbrakk>refl R X; antisym R X; is_greatest R X top\<rbrakk> \<Longrightarrow> is_filter R X {top}"
proof-
  assume A1:"refl R X" and A2:"antisym R X" and A3:"is_greatest R X top"
  then obtain B0:"{top} \<noteq>{}" and B1:"{top} \<subseteq> X" and B2:"is_dir {top} (dual R)" and B3:"is_ord_cl X {top} R"
    by (simp add: antisym_on_def is_greatestD1 is_dir_def is_ord_cl_def)
  then show "is_filter R X {top}" 
    by (simp add: is_filter_def)
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

lemma filter_inf_closed:
  assumes fil:"is_filter R X F" and isl:"is_inf_semilattice R X" and ant:"antisym R X" and aif:"a \<in> F" and
          bif:"b \<in> F"
 shows filter_inf_closed2:"Inf R X {a,b}\<in>F" and
       filter_inf_closed2b:"Inf R X {b,a}\<in>F"
proof-
  show P0:"Inf R X {a,b}\<in>F"
  using fil aif bif
  proof(rule filter_inf_closed1)
    obtain "a \<in> X" and "b \<in> X" 
       using aif bif fil is_filterD1[of R X F] by blast
     then show "is_inf R X {a, b} (Inf R X {a, b})" 
       using isl by (simp add: ant inf_semilattice_infI)
   qed
  show P1:"Inf R X {b,a}\<in>F"
    by (simp add: P0 insert_commute)
qed


lemma filter_inf_closed3:
  "\<lbrakk>antisym R X; trans R X; is_inf_semilattice R X; is_filter R X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf R X A \<in> F"
  by (simp add: filter_inf_closed2 finite_inf_closed2 is_filterD1)

section SetOfFilters

lemma filters_on_iff:
  "F \<in> filters_on R X \<longleftrightarrow> is_filter R X F"
  by (simp add: filters_on_def)

lemma filters_onD1:
  "F \<in> filters_on R X \<Longrightarrow> is_filter R X F"
  by (simp add: filters_on_def)

lemma filters_onD2:
  "F \<in> filters_on R X \<Longrightarrow> F \<noteq> {}\<and> F \<subseteq> X \<and> is_dir F (dual R) \<and> (is_ord_cl X F R)"
  by (simp add: filters_on_iff is_filterD1)

lemma sub_filters_onD1:
  assumes "E \<subseteq>filters_on R X"
  shows "E \<subseteq> Pow X"
  using assms filters_onD2 by fastforce

lemma pfilters_on_iff:
  "F \<in> pfilters_on R X \<longleftrightarrow> is_pfilter R X F"
  by (simp add: pfilters_on_def)

lemma is_pfilterD1: 
  "is_pfilter R X A \<Longrightarrow> is_filter R X A" 
  by(simp add:is_pfilter_def)

lemma pfilters_onD1:
  "F \<in> pfilters_on R X \<Longrightarrow> is_filter R X F"
  by (simp add: is_pfilterD1 pfilters_on_iff)

lemma is_pfilterD2:
  "is_pfilter R X A \<Longrightarrow>  X \<noteq> A"
  by(simp add:is_pfilter_def)


lemma pfilters_onD2:
  "F \<in> pfilters_on R X \<Longrightarrow> X \<noteq> F"
  by (simp add: is_pfilterD2 pfilters_on_iff)

lemma is_pfilterI1:
  "\<lbrakk>is_filter R X A; X \<noteq> A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by(simp add:is_pfilter_def)

lemma is_pfilterI2:
  "\<lbrakk>is_least R X bot; bot \<notin> A; is_filter R X A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by (metis is_greatestD1 is_pfilterI1)

section FiltersClosureRange

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
  obtain B0:"\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F" 
    using A3 filters_on_iff by fastforce
  obtain B1:"\<And>F. F \<in> EF \<Longrightarrow> top \<in> F" 
    using A1 B0 top_filters1[of R X _ top] by blast
  obtain B2:"\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> X \<and> is_dir F (dual R) \<and> is_ord_cl X F R"  
    using B0 is_filterD1 by blast 
  show "is_filter R X (\<Inter>EF)"
  proof(rule is_filterI1)
    show F0:"?F \<noteq> {}" 
      using B1 by auto
    show F1:"?F \<subseteq> X" 
      using A4 B2 by auto
    show F2:"is_dir ?F (dual R)"
    proof(rule is_dirI1)
      fix a b assume A5:"a \<in> ?F" and A6:"b \<in> ?F"
      then obtain F23:"\<And>F. F \<in> EF \<Longrightarrow> Inf R X {a,b}\<in>F" 
        by (simp add: A0 A2 B0 filter_inf_closed2)
      also obtain F20:"a \<in> X" and F21:"b \<in> X" and F22:"Inf R X {a,b}\<in>X"
        by (meson A0 A2 A5 A6 F1 bot_filters1 filter_inf_closed2 subsetD)
      then obtain "Inf R X {a,b} \<in> ?F" and "(Inf R X {a,b},a)\<in>R" and "(Inf R X {a,b},b)\<in>R"
        by (meson A0 A2 Inter_iff \<open>\<And>thesis. ((\<And>F. F \<in> EF \<Longrightarrow> Inf R X {a, b} \<in> F) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> antisym_on_converse converse_iff ssl_ex_sup0a ssl_ex_sup0b)  
      then show "\<exists>c \<in> ?F. (a,c)\<in>(dual R)\<and>(b,c)\<in>(dual R)" 
        by blast
    qed
    show F3:"is_ord_cl X ?F R" 
      by (simp add: A4 B2 is_ord_cl_in)
  qed
  then show "?F \<in> filters_on R X" 
    unfolding filters_on_def by blast
qed


lemma filters_clr:
  assumes A0:"is_inf_semilattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"antisym R X" 
  shows "clr (pwr X) (Pow X) (filters_on R X)"
proof(rule moore_clI3)
  show "filters_on R X \<subseteq> Pow X" 
    unfolding filters_on_def using is_filterD1 by blast
  show "X \<in> filters_on R X"
    by (simp add: A0 bot_filters1 filters_on_iff) 
  show "\<And>E. E \<subseteq> filters_on R X \<Longrightarrow> E \<noteq> {} \<Longrightarrow> \<Inter> E \<in> filters_on R X"
    by (metis A0 A1 A2 Pow_iff filter_inter2) 
qed

section FilterClosure

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
      using B0 ant ref  by (simp add: reflD2 refl_iff sup_singleton2)
  then show ?thesis 
    using filter_closure_memI2[of a X "{a}" A R] B0 B1 B2 B3 by auto
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
      fix A assume amem:"A \<in> Pow_ne X" then obtain asub:"A \<subseteq> X" and ane:"A \<noteq> {}"
        by (simp add: Pow_neD) 
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
      by (simp add: filter_closure_def greatest_equalityI2 por)
    then show ?thesis
      by (simp add: is_filterD1 por top top_filters2) 
  qed
  show P2:"is_inf_semilattice R X \<Longrightarrow> (\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_dir (filter_closure R X A) (converse R))"
  proof-
     assume isl:"is_inf_semilattice R X" 
     show "\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_dir (filter_closure R X A) (converse R)"
     proof-
      fix A assume amem:"A \<in> Pow_ne X" then obtain asub:"A \<subseteq> X" and ane:"A \<noteq> {}" 
        using Pow_neD by blast
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
		      by (meson B15 B18 B19 Fpow_neI1 antisym_on_converse is_supI1 isl por ssl_fin_sup5 trans_on_converse)
		    obtain B23:"is_inf R X Fa (Inf R X Fa)" and B24:"is_inf R X Fb (Inf R X Fb)"
		      by (simp add: B02 B03 B06 B07 B10 B11 Fpow_neI1 isl por ssl_fin_sup7)
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
      by (simp add: filter_closure_def greatest_equalityI2 por)
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
      by (simp add: Pow_ne_iff)
    then obtain A3:"\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F"
      using filters_on_iff by auto
    then obtain A4:"EF \<subseteq> Pow X" and A5:"{} \<notin> EF"
      by (meson PowI is_filterD1 subsetI)
    let ?A="\<Union>EF"
    have B0:"?A \<in> Pow_ne X"
      using A2 A4 A5 Pow_ne_iff by fastforce
    let ?S="filter_closure R X ?A"
    have B1:"is_filter R X ?S"
    proof(rule is_filterI1)
      show  P0:"?S \<noteq> {}"
        by (metis B0 Pow_ne_iff empty_subsetI filter_cl0 por subset_antisym)
      show P1:"?S \<subseteq> X"
      proof-
        obtain "?A \<noteq> {}" 
          using B0 Pow_ne_iff by blast 
        then obtain "?S= {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"
          unfolding filter_closure_def by presburger 
        then show ?thesis 
          by blast
      qed
      show "is_dir ?S (dual R)"
        by (meson B0 filter_closure2_ne lat por)
      show "is_ord_cl X ?S R"
        by (meson B0 filter_closure1_ne lat por)
    qed
    show B2:"is_sup (pwr X) (filters_on R X) EF ?S"
    proof(rule is_supI3)
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
          by (meson A2 A7 all_not_in_conv pwr_memD pwr_memI subset_trans)
      qed
    qed
  qed
  show P1:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<exists>S. is_sup (pwr X) (filters_on R X) EF S)"
    using P0 by auto
  show P2:"\<And>A. A \<in> Pow_ne (filters_on R X) \<Longrightarrow> Sup (pwr X) (filters_on R X) A= (filter_closure R X (\<Union>A))"
    by (simp add: P0 antisym_on_def pwr_memD subset_antisym sup_equality)  
qed

  
lemma filter_cl1:
  assumes por:"pord R X" and sem:"semitop R X top" and asub:"A \<subseteq> X"
  shows "is_ord_cl X (filter_closure R X A) R"
  by (metis Pow_neI1 asub filter_closure1_em filter_closure1_ne por sem)

lemma filter_cl2:
  assumes por:"pord R X" and sem:"semitop R X top" and asub:"A \<subseteq> X"
  shows  "is_dir (filter_closure R X A) (converse R)"
  by (metis Pow_neI1 asub filter_closure2_em filter_closure2_ne por sem)
 
lemma filter_cl_range:
	assumes ant:"antisym R X" and ref:"refl R X" and top:"is_greatest R X top" and sub:"A \<subseteq> X"
	shows filter_cl_sp:"(filter_closure R X A) \<subseteq> X" and
				filter_cl_ne:"(filter_closure R X A) \<noteq> {}"
proof-
	show "(filter_closure R X A) \<subseteq> X" 
	proof(cases "A={}")
		case True then show ?thesis 	
			by (metis ant filter_closure_def greatest_equalityI2 is_filterD1 ref top top_filters2) 
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
			by (metis Int_insert_right_if1 asb fil filter_closure_def greatest_equalityI2 inf.absorb_iff2 por sem top_filters1) 
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
	  by (meson fil is_filterD1 pwr_memI subset_trans)
qed

lemma filter_cl_lub:
  assumes por:"pord R X" and 
				sem:"semitop R X top" and 
				fil:"is_filter R X F" and 
				asb:"A \<subseteq> X"
	shows "is_least (pwr X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A)"
proof(rule is_greatestI3)
	show "filter_closure R X A \<in> ubd (pwr X) (filters_on R X) {A}"
		by (meson asb filter_cl_ubd por sem)
	show "\<And>a. a \<in> ubd (pwr X) (filters_on R X) {A} \<Longrightarrow> (a, filter_closure R X A) \<in> dual (pwr X)"
	  by (metis converseI filter_cl_least2 filters_on_iff por pwr_memD sem ubd_singleton_mem)
qed


lemma filter_closure_of_empty:
	assumes ref:"refl R X" and ant:"antisym R X" and sem:"semitop R X top"
	shows filter_closure_of_empty1:"is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}" and
			filter_closure_of_empty2:"(cl_from_clr (pwr X) (filters_on R X)) {} = {top}"
proof-
	show "is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
  proof(rule is_greatestI3)
		show "{top} \<in> ubd (pwr X) (filters_on R X) {{}}"
			by (meson ant empty_subsetI filters_on_iff is_filterD1 pwr_memI ref sem top_filters2 ubd_singleton_mem)
		show "\<And>a. a \<in> ubd (pwr X) (filters_on R X) {{}} \<Longrightarrow> (a, {top}) \<in> dual (pwr X)"
		  by (metis PosetsRel4.is_filter_def converse_iff empty_subsetI filters_on_iff insert_subset pwr_memI sem subset_trans top_filters1 ubdD1)
	qed
	then show "(cl_from_clr (pwr X) (filters_on R X)) {} = {top}"
	  by (meson ant clr_equality filters_clr pwr_antisym sem)
qed


lemma filter_cobounded:
  "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, b) \<in> dual (pwr X)) \<Longrightarrow> (F1 \<inter> F2, b) \<in> dual (pwr X)"
proof-
  fix b assume A0:"b \<in> filters_on R X" and A1:" \<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, b) \<in> dual (pwr X)"
  then obtain B0:"\<And>a. a \<in> {F1,F2} \<Longrightarrow> (b, a)\<in> pwr X"
    by (simp add: filters_onD1) 
  then obtain B1:"b \<subseteq> F1" and B2:"b \<subseteq> F2" and B3:"F1 \<subseteq> X" and B4:"F2 \<subseteq> X"
    by (simp add: pwr_mem_iff)
  then obtain B5:"b \<subseteq> F1 \<inter> F2" and B6:"F1 \<inter> F2 \<subseteq> X"
    by auto
  then obtain B7:"(b, F1 \<inter> F2) \<in> pwr X"
    by (simp add: pwr_mem_iff)
  then show "(F1 \<inter> F2, b) \<in> dual (pwr X)"
    by fastforce
qed

lemma filter_cl_eq_cl:
  assumes por:"pord R X" and 
				sem:"semitop R X top" and 
				asb:"A \<subseteq> X"
	shows "filter_closure R X A = (cl_from_clr (pwr X) (filters_on R X)) A"
	by (metis asb clr_equality filter_cl3 filter_cl_lub filters_clr por pwr_antisym sem)


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
   by (simp add: pwr_antisym pwr_refl pwr_trans)
 have fil0:"pord (pwr X) (filters_on R X)"
   by (meson PowI filters_on_iff is_filterD1 pwr_antisym_sub pwr_refl_sub pwr_trans_sub subsetI)
 show P0:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow>is_filter R X (F1 \<inter> F2)"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and  fil2:"is_filter R X F2"
    obtain B0:"F1 \<subseteq> X" and B1:"F2 \<subseteq> X"
      using fil1 fil2 is_filterD1 by blast 
    obtain f1 f2 where B2:"f1 \<in> F1" and B3:"f2 \<in> F2" and B4:"f1 \<in> X" and B5:"f2 \<in> X"
      by (metis is_filter_def fil1 fil2 subsetD subset_empty subset_emptyI)
    obtain B6:"Sup R X {f1,f2} \<in> F1" and  B7:"Sup R X {f1,f2} \<in> F2"
      by (meson B2 B3 B4 B5 fil1 fil2 is_filterD1 is_ord_clE1 lat lattD4 por ssl_ex_sup0a ssl_ex_sup0b ssl_ex_sup5)
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
          by (meson B12 B13 IntI antisym_on_converse lat latt_iff por ssl_ex_sup0a ssl_ex_sup0b)
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
    proof(rule is_supI3)
      show "F1 \<inter> F2 \<in> filters_on R X"
        by (simp add: P0 fil1 fil2 filters_on_iff)
      show "\<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, F1 \<inter> F2) \<in> dual (pwr X)"
        by (metis Int_lower1 converseI fil1 fil2 inf.cobounded2 insertE is_filterD1 le_infI1 pwr_memI singleton_iff)
      show "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, b) \<in> dual (pwr X)) \<Longrightarrow> (F1 \<inter> F2, b) \<in> dual (pwr X)"
        using filter_cobounded[of _ R X F1 F2] by presburger
    qed
   qed
   show P2:"is_inf_semilattice (pwr X) (filters_on R X)"
    by (metis P1 bot_filters1 empty_iff filters_on_iff is_sup_semilattice_def lat lattD4)
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
      proof-
        obtain a where a0:"a \<in> (\<Union> A)"
          using B1 by blast
        have "a \<in> ?FC"
        proof(rule filter_closure_singleton)
          show "refl R X"
            using por by blast
          show "antisym R X"
            by (simp add: por)
          show "\<Union> A \<subseteq> X"
            using B2 by blast
          show "a \<in> \<Union> A"
            using a0 by auto
        qed
        then show ?thesis
          by blast
      qed
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
          by (meson B15 B18 B19 Fpow_neI2 Pow_neD Pow_ne_iff antisym_on_converse lat lattD4 por ssl_fin_sup7 trans_on_converse)
        obtain B23:"is_inf R X Fa (Inf R X Fa)" and B24:"is_inf R X Fb (Inf R X Fb)"
          by (simp add: B02 B03 B06 B07 B10 B11 Fpow_neI1 lat lattD4 por ssl_fin_sup7)
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
    proof(rule is_supI3)
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
          by (meson B1 Sup_bot_conv(1) bsup1 pwr_memI subset_trans)
		  qed
    qed
    then show "\<exists>x. is_sup (pwr X) (filters_on R X) A x" by blast
  qed
  show P5:"is_csup_semilattice (pwr X) (filters_on R X)"
    by (metis P2 P4 is_csup_semilattice_def is_sup_semilattice_def)
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
      by (metis P3 Pow_neD ef0 filters_on_iff)
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
          using Pow_neD ef0 filters_on_iff by blast
        obtain B9:"Inf R X Fx \<in> b"
          by (metis B2 B3 B5 bfil filter_inf_closed3 filters_on_iff lat latt_iff por)
        then show "x \<in> b"
          by (meson B4 P9 bfil ef0 fcmen filters_on_iff is_filterD1 is_ord_clE1 subsetD)
      qed
      show "(filter_closure R X (\<Union> EF), b) \<in> pwr X"
        by (meson bfil dual_order.trans fcsub filters_on_iff is_filterD1 pwr_memI)
    qed
  qed
  show P12:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
  proof-
    fix EF assume ef0:"EF \<in> Pow_ne (filters_on R X)"
    show " is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
    proof(rule is_supI3) 
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


section FiltersAndDirectedUnions

lemma lattice_filter_dunion:
  assumes por:"pord R X" and
          lat:"is_lattice R X" and
          sub:"D \<subseteq> filters_on R X" and
          nem:"D \<noteq> {}" and
          dir:"is_dir D (pwr X)"
 shows "is_filter R X (\<Union>D)"
proof(rule is_filterI1)
  let ?U="\<Union>D"
  show F0:"?U\<noteq>{}"
    using sub nem filters_on_iff is_filterD1 by fastforce
  show F1:"?U\<subseteq>X"
    using sub_filters_onD1[of D R X] sub by blast
  show F2:"is_dir (\<Union> D) (dual R)"
  proof(rule is_dirI1)
    fix a b assume a0:"a \<in> ?U" and b0:"b \<in> ?U"
    obtain Da Db where a1:"a \<in> Da" and a2:"Da \<in> D" and b1:"b \<in> Db" and b2:"Db \<in> D"
      using a0 b0 by blast
    obtain Dab where ab0:"Dab \<in> D" and  ab1:" (Da, Dab)\<in>pwr X" and ab2: "(Db, Dab)\<in>pwr X"
      using a2 b2 dir is_dirE1[of D "pwr X" Da Db] by blast
    then obtain B0:"Da \<subseteq> Dab" and B1:"Db \<subseteq> Dab"
      by (simp add: pwr_memD) 
    then obtain B2:"a \<in> Dab" and B3:"b  \<in> Dab"
      using a1 b1 by blast
    then obtain B4:"is_filter R X Dab"
      using ab0 filters_onD1 sub by auto
    then obtain B5:"is_dir Dab (dual R)"
      by (simp add: is_filterD1)
    then show "\<exists>c\<in>?U. (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
      using B2 B3 UnionI ab0 is_dirE1[of Dab "dual R" a b] by blast
  qed
  show F3:"is_ord_cl X (\<Union> D) R"
    by (meson filters_onD2 is_ord_cl_un sub subsetD)
qed


lemma lattice_filters_complete:
  "\<lbrakk>pord R X;is_lattice R X;  is_greatest R X top\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (filters_on R X)"
  by (meson clr_clattice2 filters_clr latt_iff pow_is_clattice pwr_antisym pwr_refl pwr_trans)

lemma filters_inf_semilattice_inf:
  assumes por:"pord R X" and sem:"semitop R X top" and 
          mem:" EF \<in> Pow_ne (filters_on R X)"
  shows "is_inf (pwr X) (filters_on R X) EF (\<Inter>EF)"
proof(rule is_supI3)
  let ?I="\<Inter>EF"
  obtain mem1:"EF \<noteq> {}" and mem2:"EF \<in> Pow(filters_on R X)"
    using Pow_neD mem by auto
  then show P0:"?I \<in> filters_on R X"  
    by (metis filter_inter2 por sem)
  then show P1:"\<And>a. a \<in> EF \<Longrightarrow> (a,?I)\<in>(dual (pwr X))"
    by (meson Inf_lower Pow_neD converseI filters_on_iff is_filterD1 mem pwr_memI subsetD) 
  then show P2:"\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> dual (pwr X)) \<Longrightarrow> (?I, b) \<in> dual (pwr X)"
    by (metis converse_iff ex_in_conv le_Inf_iff mem1 pwr_memD pwr_memI)
qed

section PrincipalFilters

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
  by (simp add: lcro_eq_upbd ubd_space)

lemma lcro_top:
  "\<lbrakk>is_greatest R X m; a \<in> X\<rbrakk> \<Longrightarrow> m \<in> lcro R X a"
  by (simp add: is_greatestD1 lcroI1)

lemma lcro_sup_latticeD1:
  "\<lbrakk>pord R X;is_sup_semilattice R X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, y} \<in> (lcro R X x)"
  by (simp add: lcroI1 ssl_ex_sup0a ssl_ex_sup5)

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
  let ?\<FF>="filters_on R X"
  obtain iss:"is_sup_semilattice R X" and iis:"is_inf_semilattice R X"
    by (simp add: A0 lattD4)
  from A1 obtain A1a:"F \<subseteq> X" and A1b:"finite F" and A1c:"F \<noteq> {}"
    by (simp add: Fpow_neD)
  then obtain B0a:"?A \<subseteq> ?\<FF>"
    using filters_on_iff lcro_filter por by fastforce 
  obtain B0b:"finite ?A" and B0c:"?A \<noteq> {}"
    using A1b A1c by force
  obtain D0:"?A \<in> Pow_ne (?\<FF>)"
    using B0a B0c Pow_neI1 by fastforce
  obtain B0d:"Inf R X F \<in> X"
    by (simp add: A0 A1 lattD4 por ssl_fin_sup6)
  have B0e:"pord (dual R) X"
    using A1a por pord_sub2 by blast
  have B0:"\<And>f. f \<in> F \<Longrightarrow> (lcro R X f) \<subseteq> (lcro R X (Inf R X F))"
  proof-
    fix f assume fmem:"f \<in> F"
    show "(lcro R X f) \<subseteq> (lcro R X (Inf R X F))"
      by (meson A0 A1 A1a B0e fmem in_mono is_infD1 lattD4 lcro_dual_iso2 por ssl_fin_sup7)
  qed
  have B1:" (lcro R X (Inf R X F)) \<in> ubd (pwr X) (?\<FF>) ?A"
  proof(rule ubdI1)
    show "lcro R X (Inf R X F) \<in> ?\<FF>"
      by (simp add: B0d filters_on_iff lcro_filter por)
    show "\<And>a. a \<in> {lcro R X f |f. f \<in> F} \<Longrightarrow> (a, lcro R X (Inf R X F)) \<in> pwr X"
    proof-
      fix a assume amem:"a \<in> {lcro R X f |f. f \<in> F}"
      then obtain f where fmem:"f \<in> F" and aeq:"a = lcro R X f"
        by blast
      then show "(a, lcro R X (Inf R X F)) \<in> pwr X"
        using B0[of f] converse_converse lcro_subset1[of "dual R" X "Inf R X F"] 
              pwr_mem_iff[of a "lcro R X (Inf R X F)" X] by simp
    qed
  qed
  have B2:"(Sup (pwr X) (?\<FF>) ?A, lcro R X (Inf R X F))\<in>pwr X"
  proof-
    let ?\<AA>="filter_closure R X (\<Union> ?A)" let ?\<BB>="lcro R X (Inf R X F)"
    obtain B20:" is_sup (pwr X) (?\<FF>) ?A ?\<AA>"
      using D0 iis por semilat_filters_isl0 by blast
    obtain B21:"Sup (pwr X) (?\<FF>) ?A = ?\<AA>"
      by (simp add: D0 iis por semilat_filters_isl2)
    obtain B22:"?\<BB> \<in> ubd (pwr X) (?\<FF>) ?A "
      using B1 by blast
    then show ?thesis
      using B20 B21 is_supD2[of "pwr X" ?\<FF> ?A ?\<AA> ?\<BB>]  by presburger
  qed
  have B3:"\<And>G. G \<in> ubd (pwr X) (?\<FF>) ?A \<Longrightarrow>  lcro R X (Inf R X F) \<subseteq> G"
  proof-
    fix G assume B30:"G \<in> ubd (pwr X) ?\<FF> ?A" 
    have  B31:"\<And>f. f \<in> F \<Longrightarrow> f \<in> G"
    proof-
      fix f assume f1:"f \<in> F" then obtain "f \<in> X" and "f \<in> lcro R X f"
        by (meson A1a lcro_memI1 por subsetD)
      then show "f \<in> G"
        using B30 f1 ubdD2[of G "pwr X" ?\<FF> ?A " lcro R X f"] pwr_memD[of "lcro R X f" G X]  by blast 
    qed
    then obtain B32:"F \<subseteq> G" and B33:"finite F" and B34:"F \<noteq> {}" 
      using A1b A1c by blast
    then obtain B34:"Inf R X F \<in> G"
      by (meson A0 B30 filter_inf_closed3 filters_on_iff latt_iff por ubdD1)
    from B30 have B35:"is_filter R X G" 
      unfolding ubd_def filters_on_def by auto
    then obtain B36:"is_ord_cl X G R" 
      using is_filterD1 by auto
    then show "lcro R X (Inf R X F) \<subseteq> G"
      by (meson B34 is_ord_clE1 lcroD1 subsetI)
  qed
  then have "(lcro R X (Inf R X F), Sup (pwr X) ?\<FF> ?A)\<in>pwr X"
    by (metis (no_types, lifting) A0 B0a B0c B2 Pow_neI1 is_supD6 lattD4 por pwr_memD pwr_memI semilat_filters_isl0 semilat_filters_isl2)
  then show ?thesis
    using B2 pwr_memD by blast
qed
    
section CompactnessBasicLemmas

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
  proof(rule is_supI3)
    show "x \<in> X" 
      by (simp add: xmem)
    show "\<And>a. a \<in> lorc R D x \<Longrightarrow> (a, x) \<in> R" 
      using lcroD1 by force
    show "\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> lorc R D x \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (x, b) \<in> R"  
      by (meson B2 is_supD1 subset_iff xsup)
  qed
  then show "x= Sup R X (lorc R D x)"  
    by (simp add: ant sup_equality) 
qed

lemma join_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X (lorc R D x) x) \<rbrakk> \<Longrightarrow> join_dense R X D"
  by (meson PowI join_dense_def lcro_subset1)  

lemma meet_denseD2:
  "\<lbrakk>antisym R X; meet_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf R X (lcro R D x))"
  by (metis antisym_on_converse converse_converse join_denseD2)

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
  then obtain B3:"F \<subseteq> A" and B4:"F \<subseteq> X" and B5:"finite F" and B6:"F \<noteq> {}" 
    using Fpow_neD by blast
  have B7:"pord R A" 
    by (meson B2 antisym_on_subset por refl_subset trans_on_subset)
  obtain B8:"(\<And>a b. \<lbrakk>a\<in>A;b\<in>A\<rbrakk>\<Longrightarrow>(\<exists>c\<in>A.(a,c)\<in>R\<and>(b,c)\<in>R))"
    using dir is_dirD1[of A R] by blast
  then obtain a where B9:"a \<in> A" and B10:"(\<forall>x. x \<in> F \<longrightarrow> (x,a)\<in>R)"
    using B3 B5 B6 B7 dir dir_finite1[of A R F] by blast
  then show ?thesis 
    using B0 B1 by blast
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
    using B0 Fpow_neD by blast
  then obtain B12:"a \<in> ubd R X F"
    by (simp add: B2 B6 ubdI1)
  then obtain B13:"(Sup R X F,a)\<in>R"
    by (simp add: B10 B11 B9 Fpow_neI1 por sem ssl_fin_sup4)
  then obtain B14:"(c,a)\<in>R"
    by (meson B10 B11 B3 B6 B9 Fpow_neI1 cmp compactD2 por sem ssl_fin_sup6 trans_onD)
  then show ?thesis 
    using B1 by blast
qed

section FiniteSupClosure

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
    by (simp add: P0 P1 extensive_def pwr_memI)
  show P3:"\<And>A B. \<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X B" 
  proof-
    fix A B assume A0:"A \<subseteq> B" and A1:"B \<subseteq> X" 
    then obtain B0:"A \<subseteq> X" 
      by simp
    then show "fne_sup_cl R X A \<subseteq> fne_sup_cl R X B"
      unfolding fne_sup_cl_def using A0 Fpow_mono by force
  qed
  show P4:"isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. fne_sup_cl R X A)"
  proof(rule isotoneI1)
    fix x1 x2 assume x1m:"x1 \<in> Pow X" and x2m:"x2 \<in> Pow X" and x1l2:"(x1,x2)\<in>pwr X"
    then show "(fne_sup_cl R X x1, fne_sup_cl R X x2) \<in> pwr X"
      by (simp add: P0 P3 pwr_mem_iff)
  qed
  show P5:"\<And>A. A \<subseteq> X \<Longrightarrow> fne_sup_cl R X (fne_sup_cl R X A) = fne_sup_cl R X A"
  proof-
    fix A assume sub:"A \<subseteq> X" let ?L1="fne_sup_cl R X A" let ?L2="fne_sup_cl R X ?L1"
    show "?L2 = ?L1"
    proof
      show "?L1 \<subseteq>?L2"  
        by (simp add: P0 P1) 
    next
      show "?L2 \<subseteq> ?L1"
      proof
        fix s assume A0:"s \<in>?L2"
        obtain E where B0:"E \<in> Fpow ?L1" and B1:"E \<noteq> {}" and B2:"is_sup R X E s"  
          by (meson A0 fne_sup_cl_imp1) 
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
          then show "(F x) \<subseteq> X" 
             using sub by auto
        qed
        obtain B4:"is_sup R X (id`E) s"  by (simp add: B2)
        then obtain B5:"is_sup R X (\<Union>(F`E)) s" 
          using sup_families1[of E R X F id] sfA0 sfA1 sfA3 por  by blast
        obtain B7:"finite (\<Union>(F`E))" 
          by (metis B0 B3 Fpow_Pow_finite Int_Collect finite_UN)
        obtain B8:"(\<Union>(F`E)) \<noteq> {}"  
          by (simp add: B3 sfA0) 
        obtain B9:"(\<Union>(F`E)) \<subseteq> A" 
           using B3 Fpow_subset_Pow by blast
        then obtain "(\<Union>(F`E)) \<in> Fpow A" 
          by (simp add: B7 Fpow_Pow_finite)  
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
          by (meson B7 Fpow_neI1 por sem ssl_fin_sup7)
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
  show "m \<in> X"
    by (meson bot is_greatestD1)  
  show "\<And>A. A \<in> Pow_ne X \<Longrightarrow> (m, Sup R X A) \<in> R \<Longrightarrow> \<exists>F. F \<in> Fpow_ne A \<and> (m, Sup R X F) \<in> R"
  proof-
    fix A assume A0:"A \<in> Pow_ne X" and A1:"(m, Sup R X A)\<in>R"
    obtain apx:"A \<in> Pow X" 
      using A0 Pow_neD by blast
    obtain a where B0:"a \<in> A"
      using A0 Pow_neD by blast 
    obtain B1:"{a} \<in> Fpow_ne A" and B2:"a \<in> X"
      using B0 Fpow_ne_iff apx by blast
    then obtain B3:"(m,Sup R X{a})\<in>R"
      using bot is_greatestD1 por sup_singleton2 by fastforce
    then show "\<exists>F. F \<in> Fpow_ne A \<and> (m, Sup R X F) \<in> R"
       using B1 by blast
  qed
qed

section CompactnessAndClosureRanges

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
  obtain xmem:"{x}\<in>?P" 
    by (simp add: A3)
  obtain B0:"antisym ?R ?P" and B1:"refl ?R ?P" and B2:"trans ?R ?P"
    by (simp add: pwr_antisym pwr_refl pwr_trans)  
  let ?f="cl_from_clr ?R C"
  obtain B3:"C \<subseteq> Pow X" and B4:"A \<subseteq> C" and B5:"\<Union>A \<in> C"
    by (metis A0 A2 A4 A6 Pow_ne_iff closure_range_def)
  then obtain B6:"is_sup ?R C A (\<Union>A)" and B7:"Sup ?R C A = \<Union>A"
    by (meson B0 antisym_on_subset dual_order.trans pwr_ar_sup sup_equality sup_in_subset)
  from A0 A3 B0 B1 B3 obtain B8:"?f {x} \<in> C" and fxmem:"?f {x} \<in> ?P"
    by (metis Int_iff clr_induced_closure_id image_eqI inf.orderE refl_subset xmem)
  from A0 A3 B3 obtain B9:"({x}, ?f {x})\<in>?R"
    by (meson B0 B1 B2 clr_ext extensiveD1 xmem)
  then have B10:"{x} \<subseteq> ?f {x}"
    using pwr_memD by blast 
  also have B11:"... \<subseteq> \<Union>A"   
    using A5 B7 by auto 
  then have B12:"{x} \<subseteq> \<Union>A" 
    using calculation by blast 
  then obtain a where B13:"a \<in> A" and B14:"x \<in> a" 
    by auto 
  then obtain amem:"a \<in> ?P" and amem2:"a \<in> C" and B15:"({x},a)\<in>?R"
    by (meson B3 B4 Pow_iff empty_subsetI insert_subsetI pwr_memI subsetD)
  then obtain B16:"a \<in> ubd ?R C {{x}}"
    by (meson B13 B4 subsetD ubd_singleton_mem)
  then obtain fa1:"?f a \<in> C" and fa2:"?f a \<in> ?P"
    by (metis A0 B0 B1 B3 IntE amem clr_induced_closure_id image_eqI inf.orderE refl_subset)
  then obtain  B17:"?f a = a"
    by (meson A0 B0 B1 B3 amem2 clr_equality is_sup_def powrel6 refl_subset sup_singleton1)
  then obtain B18:"(?f {x},?f a)\<in>?R"
    by (metis A0 B0 B16 closure_range_def clr_equality converseD is_greatestD1 xmem)
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
  by (metis A0 A2 A3 A4 A5 A6 is_dirE1 pwr_memD pwr_memI)

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
  then obtain B0:"is_clattice (pwr X) C"
    using A0 clr_clattice2 by blast
  have B0b:"pord ?R C"
    by (meson A0 clrD1 por pwr_antisym_sub pwr_trans_sub refl_subset)
  have B1:"\<And>x. x \<in> X \<Longrightarrow> is_compact (pwr X) C (?f {x})" 
    by (metis A0 A1 A2 singleton_closure_compact)
  obtain B2:"E \<in> Pow X" 
    using A0 A3 clrD1 by blast 
  obtain B3:"\<And>x. x \<in> E \<Longrightarrow> {x} \<in> Pow X"  
    using B2 by blast 
  have B4:"?A \<subseteq> C"
  proof 
    fix y assume A9:"y \<in> ?A" then obtain x where B40:"x \<in> E" and B41:"y = ?f {x}" 
       by blast
    then show "y \<in> C"  
      using B1 B2 compactD2 by fastforce 
  qed
  have B5:"\<And>x. x \<in> E \<Longrightarrow> {x} \<subseteq> ?f {x}"
  proof-
    fix x assume "x \<in> E" then obtain "{x}\<in>Pow X" 
      using B3 by force
    then show "{x} \<subseteq> ?f {x}"
      by (metis A0 clrD1 clr_equality is_greatestD1 powrel1 powrel8 ubd_singleton_mem)
  qed
  have B6:"?f E = E" 
    by (metis A0 A3 cl_is_closure closure_def clrD1 clr_induced_closure_id idempotentD3 por refl_subset)
  have B7:"\<And>x. x \<in> E \<Longrightarrow> ?f {x} \<subseteq> ?f E"
  proof-
    fix x assume B70:"x \<in> E" then obtain B71:"{x}\<in>Pow X" 
      using B3 by force
    have B72:"({x}, E)\<in> pwr X"
      by (meson B2 B70 B71 PowD bot.extremum insert_subsetI pwr_memI)
    then obtain B73:"(?f {x}, ?f E)\<in>pwr X"
      using clr_iso[of "Pow X" "pwr X" C] isotoneD1[of "pwr X" "Pow X" "pwr X" ?f "{x}" E] A0 B2 B71 por by blast
    then show "?f {x} \<subseteq> ?f E"
      using powrel8 by blast
  qed
  have B8:"E \<in> ubd ?R C ?A" 
  proof(rule ubdI1)
    show B80:"E \<in> C" 
      by (simp add: A3)
    show B81:"\<And>a. a \<in> ?A\<Longrightarrow> (a, E) \<in> pwr X" 
      using B2 B6 B7 pwr_mem_iff by fastforce
  qed
  have B8b:"Sup ?R C ?A \<in> Pow X"
  proof-
    obtain s where "is_sup ?R C ?A s"
      using B0 B4 is_clattice_def[of ?R C] by blast
    then show ?thesis
      using A0 B0b clrD1[of ?R "Pow X" C] is_supD4[of ?R C ?A s] sup_equality[of ?R C ?A s] by fastforce
  qed
  have B8c:"(Sup ?R C ?A, E)\<in>pwr X" 
    using clatD4[of C ?R ?A E] B0b B0 B8 B4 by blast
  have B9:"E = (\<Union>x \<in> E. {x})" 
    by simp
  have B10:"... \<subseteq> (\<Union>x \<in> E. ?f {x})" 
    using B5 by blast
  have B11:"... = (\<Union>?A)" 
    by blast
  have B12:"... = Sup ?R (Pow X) ?A" 
    by (metis (no_types, lifting) A0 B4 clrD1 por powrel9 sup_equality) 
  have B13:"... \<subseteq> Sup ?R C ?A" 
    using sup_iso2[of "Pow X" ?R C] A0 B0 B4 clat clrD1 por pwr_mem_iff by (metis (no_types, lifting))
  have B14:"... \<subseteq> E"
    using B8c powrel8 by auto
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
    by (simp add: filters_on_iff lat lattice_filter_dunion por)
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
      by (simp add: A0 A1 A2 lat lattice_filter_dunion por)
    then show "\<Union> D \<in> filters_on R X" 
      by (simp add: filters_on_iff)
  qed
qed





section UpClosure


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
  by (simp add: bsup_ge1 lattD4)

section BinaryFilterSup

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
    then obtain B0:"y \<in> X" and B1:"a \<in> X"  
      using A1 A2 A3 is_filterD1 by blast
    then obtain B2:"(Inf R X {a, y}, a)\<in>R"
      by (meson antisym_on_converse converseD lat lattD4 por ssl_ex_sup0a)
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
      then obtain a1:"a \<in> X" 
        using filter_bsup_memD1 by force
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
      obtain amem2:"a \<in> X"
        using amem1 filter_bsup_memD1[of a R X F1 F2] by auto
      obtain bmem2:"b \<in> X" 
        using bmem1 filter_bsup_memD1[of b R X F1 F2] by auto 
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
        by (simp add: B6 B7 B8 B9 lat lattD4 por refl_dualI semilattice_assoc_sup)
      also have B17:"... = Inf R X {a1,a2,b1,b2}"
        by (simp add: insert_commute)
      also have B18:"... = Inf R X {Inf R X {a1, a2}, Inf R X {b1, b2}}"
        by (metis B6 B7 B8 B9 lat latt_iff por semilattice_assoc_inf)
      obtain B19:"(Inf R X {Inf R X {a1, a2}, Inf R X {b1, b2}},a)\<in>R "
        by (meson B14 B15 B4 amem2 antisym_on_converse converseD lat lattD4 por ssl_ex_sup0a ssl_ex_sup5 trans_onD)
      then obtain B20:"(Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}},a)\<in>R"
        using B16 B17 B18 by presburger
      obtain B21:"(Inf R X {Inf R X {a1, a2}, Inf R X {b1, b2}},b)\<in>R "
        by (meson B14 B15 B5 antisym_on_converse bmem2 converseD lat lattD4 por ssl_ex_sup0b ssl_ex_sup5 trans_onD)
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
    proof(rule ubdI1)
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
        by (metis gubd insertCI insert_Diff insert_subset powrel8 ubdD2)
      then obtain B4:"Inf R X {a1, a2} \<in> G"
        by (metis fil0 filter_inf_closed2 lat latt_iff por)
      show "x \<in> G"
        by (meson A4 B2 B4 fil0 filter_bsup_memD1 is_filterD1 is_ord_clE1)
    qed
    then show "(?FC,G)\<in>(pwr X)"
      by (meson fil0 is_filterD1 pwr_mem_iff)
  qed
  show P9:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>  \<Longrightarrow> is_sup (pwr X) (filters_on R X) {F1, F2} (binary_filter_sup R X F1 F2)"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and fil2:"is_filter R X F2" 
    let ?FC="binary_filter_sup R X F1 F2"
    obtain "?FC \<in> ubd (pwr X) (filters_on R X) {F1, F2}"
      using P7 fil1 fil2 by presburger
    also obtain "\<And>G. G \<in> ubd (pwr X) (filters_on R X) {F1, F2} \<Longrightarrow>  (?FC, G)\<in>(pwr X)"
      using P8 fil1 fil2 filters_onD1[of _ R X] ubdD1[of _ "(pwr X)" "(filters_on R X)"] by blast
    then show " is_sup (pwr X) (filters_on R X) {F1, F2} ?FC"
      by (simp add: calculation is_supI4)
  qed
  show P10:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) {F1, F2} = (binary_filter_sup R X F1 F2)"
  by (simp add: P9 antisym_on_def pwr_mem_iff subset_antisym sup_equality)
qed

  
lemma lattice_filters_distr:
  assumes A0:"distributive_lattice R X"  and A1:"antisym R X" and A2:"refl R X" and A3:"trans R X"
  shows "distributive_lattice (pwr X) (filters_on R X)"
proof-
  let ?F="filters_on R X" let ?R="pwr X"
  have B01:"is_lattice R X" 
    using assms distributive_lattice_def by blast
  have B02:"is_lattice (pwr X) ?F" 
    by (simp add: assms distr_lattice_filters)
  obtain B03:"is_sup_semilattice R X" and B04:"is_sup_semilattice ?R ?F"
    by (simp add: B01 B02 lattD4)
  have B1:" \<And>x y z. \<lbrakk>x \<in> ?F;  y \<in>?F; z \<in> ?F\<rbrakk> \<Longrightarrow> (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}})\<in>(pwr X)"
  proof-
    fix f g h assume A4:"f \<in> ?F" and A5:"g \<in> ?F" and A6:"h \<in> ?F"
    then obtain A40:"is_filter R X f" and A41:"is_filter R X g" and A42:"is_filter R X h"
      by (simp add: filters_on_iff)
    then obtain A43:"f \<in> Pow X" and A44:"g \<in> Pow X" and A45:"h \<in> Pow X"
      by (simp add: is_filterD1)
    let ?sfg="Sup ?R ?F {f, g}" and ?sfh="Sup ?R ?F {f, h}" and  ?igh="Inf ?R ?F {g, h}"
    have D0:"Inf ?R ?F {?sfg, ?sfh} \<subseteq> Sup ?R ?F {f, ?igh}"
    proof
        fix z assume A7:"z \<in> (Inf ?R ?F {?sfg, ?sfh})"
        have B2:"Inf ?R ?F {?sfg, ?sfh} =?sfg \<inter> ?sfh"
          by (metis A1 A2 A3 A4 A5 A6 B01 filter_on_lattice_bsup11 filter_on_lattice_bsup7 filters_on_iff lattice_filters_isl7)
        obtain B3:"z \<in> ?sfg" and B4:"z \<in> ?sfh" 
           using B2 A7 by blast 
        then obtain x1 y where B5:"x1 \<in> f" and B6:"y \<in> g"  and B7:"(Inf R X {x1, y},z)\<in>R"
          by (metis A1 A2 A3 A4 A5 B01 filter_bsup_memD1 filter_on_lattice_bsup11 filters_on_iff)
        obtain x2 t where B8:"x2 \<in> f" and B9:"t \<in> h" and B10:"(Inf R X {x2,t},z)\<in>R"
          by (metis A1 A2 A3 A4 A6 B01 B4 filter_bsup_memD1 filter_on_lattice_bsup11 filters_on_iff)
        obtain B11:"x1 \<in> X" and B12:"y \<in> X" and B13:"x2 \<in> X" and B14:"t \<in> X"
          using A43 A44 A45 B5 B6 B8 B9 by blast
        obtain B14b:"(x2, Sup R X {y,x2})\<in>R" and B14c:"(y,Sup R X {y,t})\<in>R" and B14d:"(t,Sup R X {y,t})\<in>R"
          by (simp add: A1 B03 B12 B13 B14 ssl_ex_sup0a ssl_ex_sup0b)
        obtain B15:"Sup R X {x1,Inf R X {x2,t}}\<in>f"
          by (meson A1 A40 B01 B5 B11 B12 B13 B14 antisym_on_converse is_filterD1 is_ord_clE1 lattD4 ssl_ex_sup0a ssl_ex_sup5)
        obtain B16:"Sup R X {y,x2}\<in>f"
          by (meson A1 A3 A4 B01 B12 B13 B8 B14b ssl_ex_sup5 filters_on_iff is_filterD1 is_ord_clE1 lattD42 ssl_ex_sup0a)
        obtain B17:"Sup R X {y,t} \<in> g"
          using B6 B14c A41 by (meson A1 B03 B12 B6 B14c B14 is_filterD1 is_ord_clE1 ssl_ex_sup5)
        obtain B18:"Sup R X {y,t} \<in> h"
          using B9 B14d A42 by (meson A1 B03 B12 B14 is_filterD1 is_ord_clE1 ssl_ex_sup5)
        have B19:"Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}} \<in> f"
          using A1 A4 B01 B15 B16 filter_inf_closed2 filters_on_iff lattD4 by fastforce
        have B20:"Inf R X {Sup R X {y, x2}, Sup R X {y, t}} = Sup R X {y, Inf R X {x2, t}}"
          by (simp add: A0 B12 B13 B14 distr_latticeD1)
        then obtain B21:
        "Inf R X {Sup R X {x1, Inf R X {x2, t}}, Inf R X {Sup R X {y, x2}, Sup R X {y, t}}} =  
                        Inf R X {Sup R X {x1, Inf R X {x2, t}},  Sup R X {y, Inf R X {x2, t}}}"
          by simp
        have B22:"... = Sup R X {Inf R X {x1, y}, Inf R X {x2, t}}"
          using A0 B11 B12 B13 B14 distr_latticeD2[of R X "Inf R X {x2, t}" x1 y] 
                B01 A1 lattD31[of X R x2 t] is_infD1[of R X "{x2, t}" "Inf R X {x2, t}"] by presburger
        obtain B23:"Inf R X {x1,y}\<in>X" and B24:"Inf R X {x2,t}\<in>X" and B25:"Inf R X {x2,t}\<in>X" and 
               B26:"Sup R X {y,x2}\<in>X" and B27:"Sup R X {y,t}\<in>X"
          by (simp add: A1 B01 B11 B12 B13 B14 lattD4 ssl_ex_sup5)
        have B28:"Sup R X {Inf R X {x1, y}, Inf R X {x2, t}} = 
                  Inf R X {Sup R X {x1, Inf R X {x2, t}}, Inf R X {Sup R X {y, x2}, Sup R X {y, t}}} "
                  by (simp add: B22 B21)
        have B29:"... =  Inf R X {Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}}, Sup R X {y, t}}"
          by (simp add: A1 A3 B01 B11 B25 B26 B27 bsup_assoc2 lattD4 ssl_ex_sup5)
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
          by (simp add: A1 A2 A3 A40 A41 A42 A5 A6 B01 filter_on_lattice_bsup11 lattice_filters_isl0 lattice_filters_isl7)
        then show "z \<in> Sup ?R ?F {f, ?igh}"
          using B37 by presburger 
       qed
      have B39:"Inf ?R ?F {?sfg, ?sfh} \<subseteq> X"
        by (metis A1 A2 A3 A4 A5 A6 B01 filter_on_lattice_bsup11 filter_on_lattice_bsup7 filters_on_iff inf.coboundedI1 is_filterD1 lattice_filters_isl7)
      have B40:"Sup ?R ?F {f, ?igh} \<subseteq> X"
        by (metis A1 A2 A3 A4 A5 A6 B01 filter_on_lattice_bsup11 filter_on_lattice_bsup6 filters_on_iff lattice_filters_isl0 lattice_filters_isl7)  
      show "(Inf ?R ?F {?sfg, ?sfh}, Sup ?R ?F {f, ?igh}) \<in> ?R"
        by (simp add: B40 D0 pwr_mem_iff)
    qed
    have P:" \<And>x y z. \<lbrakk>x \<in> ?F;  y \<in>?F; z \<in> ?F\<rbrakk> \<Longrightarrow> (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}}) \<in> (pwr X)"
      using B1 by blast
    show "distributive_lattice ?R ?F"
    proof(rule distr_latticeI2)
      show "pord ?R ?F"
        by (meson PowI filters_on_iff is_filterD1 powrel6 powrel7 pwr_memI refl_def subsetI)
      show " is_lattice ?R ?F"
        using B02 by blast
      show "\<And>x y z. \<lbrakk>x \<in> ?F; y \<in> ?F; z \<in> ?F\<rbrakk> \<Longrightarrow>  (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}}) \<in> (pwr X)"
        using P by blast
    qed
qed

section PrimeElements

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
  assumes xmem:"x \<in> X" and esp:"elem_sup_prime R X x"
  shows "sup_prime R X (lcro R X x)"
proof(rule sup_primeI1)
  fix a b assume A0:"a \<in> X" and A1:"b \<in> X" and A2:"Sup R X {a, b} \<in> lcro R X x"
  then show "a \<in> lcro R X x \<or> b \<in> lcro R X x"
    by (metis elem_sup_primeD1 esp lcroD1 lcroI1)
qed

lemma elem_inf_primeE1:
  "\<lbrakk>x \<in> X; elem_inf_prime R X x\<rbrakk> \<Longrightarrow> inf_prime R X (lorc R X x)"
  by (simp add: elem_sup_primeE1)

lemma elem_sup_primeI2:
  assumes A0:"x\<in>X" and A1:"sup_prime R X (lcro R X x)" and A2:"pord R X" and A3:"is_sup_semilattice R X"
  shows "elem_sup_prime R X x "
  proof(rule elem_sup_primeI1)
    fix a b assume A4:"a \<in> X" and A5:"b \<in> X" and A6:"(x, Sup R X {a, b})\<in>R" 
    show "(x, a) \<in> R \<or> (x, b) \<in> R"
    by (metis A1 A2 A3 A4 A5 A6 lcroD1 lcroI1 ssl_ex_sup5 sup_primeD1)
qed

lemma elem_inf_primeI2:
  assumes A0:"x\<in>X" and A1:"inf_prime R X (lorc R X x)" and A2:"pord R X" and A3:"is_inf_semilattice R X"
  shows "elem_inf_prime R X x"
  by (simp add: A0 A1 A2 A3 elem_sup_primeI2 refl_iff)

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
    by (metis A0 A1 A2 A3 A4 A5 A6 distr_latticeD5 doubleton_eq_iff elem_sup_primeD1 lat_absorb2 lat_ge_iff4 reflD2)
qed


lemma fin_inf_irrE1:
  assumes A0:"pord R X" and A1:"distributive_lattice R X" and A2:"x\<in>X" and A3:"elem_inf_prime R X x"
  shows "fin_inf_irr R X x"
proof(rule fin_inf_irrI1)
  fix a b assume A4:"a\<in>X" and A5:"b\<in>X"  and A6:"x = Inf R X {a, b}" 
  show "x = a \<or> x = b"
    by (metis A0 A1 A2 A3 A4 A5 A6 antisym_on_converse distributive_lattice_dual fin_inf_irrD1 fin_sup_irrE1 refl_dualI trans_on_converse)
qed



lemma elem_sup_primeI3:
  assumes A0:"distributive_lattice R X" and A1:"x \<in> X" and A2: "fin_sup_irr R X x" and A3:"pord R X"
  shows "elem_sup_prime R X x"
proof(rule elem_sup_primeI1)
    fix a b assume A4:"a \<in> X" and A5:"b \<in> X" and A6:"(x, Sup R X {a, b})\<in>R" 
    obtain B0:"Sup R X {a, b} \<in> X"
      by (meson A0 A3 A4 A5 distr_latticeD5 is_supD1 lattD32)
    have B1:"x = Inf R X {x, Sup R X {a, b}}"
      by (metis A0 A1 A3 A6 B0 distr_latticeD5 lat_ge_iff3)
    have B2:"... = Sup R X {Inf R X {x, a}, Inf R X {x, b}}"
      by (simp add: A0 A1 A3 A4 A5 distr_latticeD3)
    have B3:"x = Inf R X {x, a} \<or> x = Inf R X {x, b}"
      by (metis A0 A1 A2 A3 A4 A5 B1 B2 distr_latticeD5 fin_sup_irr_def is_supD1 lattD31)
    show "(x, a) \<in> R \<or> (x, b) \<in> R"
      by (metis A0 A1 A3 A4 A5 B3 distr_latticeD5 lattD6)
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

section PrimeFilters

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
    by (meson is_filterD1 is_ord_clE1 is_pfilterD1 lat lattD42 pfil por ssl_ex_sup0a ssl_ex_sup0b ssl_ex_sup5)
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
        by (meson A0 A2 B0 B1 fil1 fil2 is_filterD1 is_ord_clE1 lat lattD42 por ssl_ex_sup0a ssl_ex_sup0b ssl_ex_sup5)
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
        by (metis A6 A7 A9 IntD1 lat lcroD1 leq_sup por)
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
      by (meson A0 A2 A3 antisym_on_converse converseD lattD4 ssl_ex_sup0a)
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
      by (simp add: A0 A1 A3 B20 B22 filter_inf_closed2 lattD4)
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
      by (meson A0 A3 B30 B31 antisym_on_converse lattD4 ssl_ex_sup0a ssl_ex_sup0b)
  qed
  show "is_ord_cl X G R"
  proof(rule is_ord_clI1)
     fix x g assume A8:"g \<in> G" and A9:"x \<in> X" and A10:"(g,x)\<in>R"
     obtain y where B60:"y \<in> F" and B61:"(Inf R X {a, y}, g)\<in>R"  
        using A8 G_def by blast 
     obtain B62:"g \<in> X"  and B62:"Inf R X {a, y} \<in> X"
       by (metis A0 A1 A2 A3 A8 B60 P1 antisym_on_converse in_mono is_filterD1 lattD4 ssl_ex_sup5)
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

lemma prime_filter_fin_irr:
  assumes lat:"is_lattice R X" and 
          por:"pord R X" and
          pfl:"is_pfilter R X F" and
          spr:"sup_prime R X F"
  shows "fin_inf_irr (pwr X) (filters_on R X) F"
proof(rule fin_inf_irrI1)
  fix a b assume A0:"a\<in>filters_on R X " and A1:"b\<in>filters_on R X " and A2:"F=Inf (pwr X) (filters_on R X){a,b}"
  then obtain B0:"is_filter R X a" and B1:"is_filter R X b" and B2:"a \<inter> b = F"
    by (simp add: filters_onD1 lat lattice_filters_isl7 por) 
  then obtain B3:"F \<subseteq> a" and B4:"F \<subseteq> b" and B5:"a \<inter> b \<subseteq> F"
    by blast
  then obtain B6:"a \<subseteq> F \<or> b \<subseteq> F"
    using B0 B1 lat pfl por spr sup_prime_pfilterD4[of R X F a b] by fastforce 
  then show "F = a \<or> F = b"
    using B3 B4 by blast
qed


lemma proper_principal_prime:
  "\<lbrakk>is_pfilter R X (lcro R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow> sup_prime R X (lcro R X a)"
  by (metis lcroD1 lcroI1 sup_prime_def)

lemma proper_principal_prime2:
  "\<lbrakk>is_lattice R X;pord R X;is_pfilter R X (lorc R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a = Sup R X {x, y}\<rbrakk> \<Longrightarrow> a =x \<or> a=y)"
  by (metis antisym_onD lattD42 ssl_ex_sup0a ssl_ex_sup0b ssl_ex_sup5)

lemma proper_principal_fin_irr:
  "\<lbrakk>is_lattice R X; pord R X;is_pfilter R X (lcro R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow>fin_inf_irr (pwr X) (filters_on R X) (lcro R X a)"
  by (simp add: prime_filter_fin_irr proper_principal_prime)

lemma fin_irr_filter_prime:
  assumes dis:"distributive_lattice R X" and por:"pord R X" and pfil:"is_pfilter R X F" and
          fii:"fin_inf_irr (pwr X) (filters_on R X) F"
  shows "inf_prime R X F"
proof(rule inf_primeI1)
  fix a b assume A0:"a\<in>X" and A1:"b\<in>X" and A2:"Inf R X {a, b} \<in> F"
  obtain lat:"is_lattice R X" 
    using distr_latticeD5 dis by blast
  obtain glb:"is_inf R X {a,b}(Inf R X {a, b})" 
    using A0 A1 por lat lattD31[of X R a b] by auto
  show "a \<in> F \<or> b \<in> F" 
    by (meson A0 A2 converse_iff glb insertCI is_filterD1 is_ord_clE1 is_pfilterD1 is_supD1 pfil)
qed

lemma distr_lattice_maximal_prime:
  assumes dis:"distributive_lattice R X" and por:"pord R X" and ult:"is_maximal (pwr X) (pfilters_on R X) F"
  shows "sup_prime R X F"
proof(rule sup_primeI2)
  fix a b assume A0:"a \<in> X" and A1:"b\<in>X" and A2:"Sup R X {a, b} \<in> F" and  A3:"a \<notin> F"
  have "is_lattice R X" 
    using dis distr_latticeD5 by auto
  with A0 A1 A2 A3 obtain A4:"Sup R X {a,b}\<in>X" and A5:"lcro R X a \<in> filters_on R X" and A6:"F \<in> pfilters_on R X"
    by (meson filters_on_iff lattD42 lcro_filter maximalD1 por ssl_ex_sup5 ult)
  then obtain A7:"is_filter R X F" and A8:"is_filter R X(lcro R X a)"
    by (simp add: filters_on_iff is_pfilterD1 pfilters_on_iff)
  obtain fup:"is_ord_cl X F R"
    by (simp add: A7 is_filterD1)
  obtain A9:"is_lattice R X"
    by (simp add: dis distr_latticeD5)
  obtain isl:"is_inf_semilattice R X" and ssl:"is_sup_semilattice R X"
    by (simp add: A9 lattD4)
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
    by (metis A7 A8 A9 filter_on_lattice_bsup6 is_filterD1 maximalD2 por psubset_eq pwr_memI ult)
  obtain B4:"?Fa \<in> filters_on R X" and B5:"?Fa = X" and  B6:"b \<in> ?Fa"
    by (metis A1 A12 B3 filters_on_iff is_pfilterI1 pfilters_on_iff)
  obtain f c where A13:"f \<in>F" and A14:"c \<in> ?upa" and A15:"(Inf R X {f, c}, b)\<in>R"
    by (meson B6 filter_bsup_memD1)
  then obtain A16:"f\<in>X" and A17:"c\<in>X"
    by (metis B2 B5 lcroD1 psubsetD)
  let ?ifc="Inf R X {f, c}" let ?sbf="Sup R X {b,f}" let ?sbc="Sup R X {b,c}" let ?sba="Sup R X {b, a}" let ?ifa="Inf R X{f,a}"
  obtain A18:"?ifc\<in>X"  and A19:"?sbf\<in>X" and A20:"?sbc\<in>X" and A21:"?sba\<in>X" and A21b:"?ifa\<in>X"
    by (simp add: A0 A1 A16 A17 A9 lattD4 por ssl_ex_sup5)
  have B8:"b = Sup R X {b, ?ifc}"
    by (metis A1 A15 A18 A9 lat_ge_iff2 por)
  have B9:"... = Inf R X {?sbf, ?sbc}"
    by (simp add: A1 A16 A17 dis distr_latticeD1)
  let ?i_sbf_sbc="Inf R X {?sbf,?sbc}"
  obtain A22:"?i_sbf_sbc \<in> X"
    using A1 B8 B9 by presburger 
  obtain B10a:"?sbf \<in>F"
    using A1 A16 por ssl ssl_ex_sup0b[of X R b f] fup A13 A19 is_ord_clE1[of X F R f "Sup R X {b,f}"] by blast
  obtain B10b:"?sbc \<in>?upa"
    using A0 A1 A14 A20 A9 lcroD1 lcroI1 lattD42 por  bsup_le2 by metis
  obtain B10c:"b=?i_sbf_sbc"
    using B8 B9 by presburger
  have B11:"(a, ?sbc) \<in> R"
    by (meson B10b lcroD1)
  let ?s_b_sbf=" Sup R X {b, ?sbf}" let ?s_b_sbc="Sup R X {b, ?sbc}"
  obtain A23:"?s_b_sbf \<in> X" and A24:"?s_b_sbc \<in> X"
    using A1 A19 A20 A9 latt_iff por by (simp add: lattD4 ssl_ex_sup5)
  have B12:"(?sbf, ?s_b_sbf)\<in>R"
    using A1 A19 A9 lattD42 por by (metis ssl_ex_sup0b)
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
    using A7 A2 B10a  filter_inf_closed2b[of R X F ?sbf ?sba]
    by (simp add: A9 insert_commute lattD4 por)
  have B19:"(Inf R X {?sbf, ?sba}, b)\<in>R"
    using A25 B17 by presburger
  then show "b \<in> F"
    by (meson A1 A7 B18 is_filterD1 is_ord_clE1)
qed

section FiltersOnLattice

(*
  letting (X, \<le>) be a lattice with a top element 1.  Then for filters {F\<^sub>j} for j=1,...,n the 
    \<And>F\<^sub>j=\<Inter>F\<^sub>j={\<Or>x\<^sub>j:x\<^sub>j\<in>F\<^sub>j}
  which is find_fil8 and find_fil9 of finite_ind_fil.  Moreover for arbitrary family of filters
    \<Or>\<F>={x \<in> X: for finitely many {F\<^sub>j}\<subseteq>\<F> and x\<^sub>j\<in>F\<^sub>j it holds \<And>x\<^sub>j \<le> x }
  which is finite_ind_fil8 and for filters {F\<^sub>j}  
     \<Or>F\<^sub>j={x \<in> X: \<And>x\<^sub>j \<le> x for x\<^sub>j\<in>F\<^sub>j}
  which is finite_ind_fil12 then for topped distributive lattices we have in finite_ind_fil16
     \<Or>F\<^sub>j={x \<in> X: \<And>x\<^sub>j = x for x\<^sub>j\<in>F\<^sub>j}

*)

lemma fin_filter_inf_lattice:
  assumes por:"pord R X" and
          top:"is_greatest R X m" and 
          ind1:"finite I" and 
          ind2:"I \<noteq> {}" and 
          fil:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))"
  shows find_fil_inf1:"is_inf_semilattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))" and
        find_fil_inf2:"is_lattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))" and
        find_fil_inf3:"\<And>x s. \<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)); is_sup R X (x` I) s\<rbrakk> \<Longrightarrow> s \<in> (\<Inter>(f` I))" and
        find_fil_inf4:"\<And>s. \<lbrakk>s \<in> (\<Inter>(f` I))\<rbrakk>\<Longrightarrow>  \<exists>x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> is_sup R X (x` I) s" and
        find_fil_inf5:"\<And>x. \<lbrakk>is_lattice R X;(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))\<rbrakk> \<Longrightarrow> Sup R X (x` I) \<in> \<Inter>(f`I)" and
        find_fil_inf6:"\<And>s. \<lbrakk>s \<in> (\<Inter>(f` I))\<rbrakk> \<Longrightarrow>  s \<in> {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}" and
        find_fil_inf7:"\<Inter>(f`I) \<subseteq> {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}" and
        find_fil_inf8:"is_lattice R X \<Longrightarrow> \<Inter>(f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}" and
        find_fil_inf9:"is_lattice R X \<Longrightarrow> Inf (pwr X) (filters_on R X) (f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
proof-
  show P1:"is_inf_semilattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
  proof-
    assume isl:"is_inf_semilattice R X"
    obtain "(f`I) \<in> Pow_ne (filters_on R X)"
      by (simp add: Pow_neI1 fil filters_on_iff image_subset_iff ind2)
    then show "is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
      using isl por top filters_inf_semilattice_inf[of X R m "f`I"] by blast
  qed
  show P2:"is_lattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
    by (simp add: P1 latt_iff)
  show P3:"\<And>x s. \<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)); is_sup R X (x` I) s\<rbrakk> \<Longrightarrow> s \<in> (\<Inter>(f` I))"
  proof-
    fix s x assume prd:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and iss:"is_sup R X (x` I) s" 
    show "s \<in> (\<Inter>(f` I))"
    proof(rule INT_I)
      fix i assume i0:"i \<in> I"
      obtain B0:"(x i) \<in> (f i)" and B1:"(x i) \<in> (x` I)" and B2:"is_filter R X (f i)"
        by (simp add:i0 fil prd)
      obtain B3:"is_ord_cl X (f i) R"
        by (simp add: B2 is_filterD1)
      obtain B4:"s \<in> X" 
        using is_supD4[of R X "x`I" s] iss by blast 
      obtain B5:"(x i, s)\<in>R" 
        using B1 is_supD1[of R X "x`I" s] iss by blast
      show "s \<in> f i"
        using is_ord_clE1[of X "f i" R "x i" s] B0 B3 B4 B5 by simp
    qed
  qed
  show P4:"\<And>s. s \<in> (\<Inter>(f` I))\<Longrightarrow>  (\<exists>x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> is_sup R X (x` I) s)"
  proof-
    fix s assume fil3:"s \<in> (\<Inter>(f` I))"
    show "(\<exists>x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> is_sup R X (x` I) s)"
    proof-
      define x where "x = (\<lambda>(i::'b). s)"
      have B0:"is_sup R X (x` I) s"
      proof(rule is_supI3)
        show B01:"s \<in> X"
          using is_filterD1 fil fil3 ind2 by fastforce
        show B02:"\<And>a. a \<in> x ` I \<Longrightarrow> (a, s) \<in> R"
          using refl_def x_def B01 por by fastforce
        show B03:"\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> x ` I \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (s, b) \<in> R"
          using ind2 x_def by blast
      qed
      also have B1:" (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"
        using fil3 x_def by fastforce
      then show ?thesis
        using calculation by blast 
    qed
  qed
  show P5:"\<And>x. \<lbrakk>is_lattice R X;(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))\<rbrakk> \<Longrightarrow> Sup R X (x` I) \<in> \<Inter>(f`I)"
  proof-
    fix x assume prd:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and lat:"is_lattice R X"
    show "Sup R X (x` I) \<in> \<Inter>(f`I)"
    proof-
      let ?F="(x` I)" let ?s="Sup R X (x` I)"
      have B0:"finite ?F"
        by (simp add: ind1)
      have B1:"?F \<subseteq> X"
        using fil is_filterD1 prd by fastforce
      have B2:"is_sup R X ?F ?s"
        by (simp add: B0 B1 Fpow_neI1 ind2 lat lattD4 por ssl_fin_sup7)
      have B3:"\<And>i. i \<in> I \<Longrightarrow> ?s \<in> f i"
        using B2 P3 prd by blast
      then show ?thesis
        by blast
    qed
  qed
  show P6:"\<And>s. \<lbrakk>s \<in> (\<Inter>(f` I))\<rbrakk> \<Longrightarrow>  s \<in> {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  proof-
    fix s assume s0: "s \<in> (\<Inter>(f` I))"
    then obtain x where "(\<And>i. i \<in> I \<longrightarrow> x i \<in> f i)" and "is_sup R X (x ` I) s"
      using P4[of s] by auto
    then show "s \<in> {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
      using por sup_equality[of R X "x`I" s] by force
  qed
  show P7:"\<Inter>(f`I) \<subseteq> {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"  (is "?LHS \<subseteq>?RHS")
  proof
    fix a assume "a \<in> ?LHS"
    then obtain x where "(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))" and "is_sup R X (x` I) a"
      using P4[of a] by blast
    then show "a \<in> ?RHS"
      using por sup_equality[of R X "x`I" a] by force 
  qed
  show P8:"is_lattice R X \<Longrightarrow> \<Inter>(f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}" 
  proof-
    assume lat:"is_lattice R X"
    show "\<Inter>(f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"   (is "?LHS=?RHS")
    proof
      show "?LHS \<subseteq> ?RHS"
        using P7 by blast
      next
      show "?RHS \<subseteq> ?LHS"
      proof
        fix a assume "a \<in> ?RHS"
        then obtain x where "\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)" and "a=Sup R X (x` I)" 
          by blast
        then show "a \<in> ?LHS" 
          using P6  P5 lat by presburger
      qed
    qed
  qed
  show P9:"is_lattice R X \<Longrightarrow>  Inf (pwr X) (filters_on R X) (f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  proof-
    assume lat:"is_lattice R X"
    show "Inf (pwr X) (filters_on R X) (f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
    proof-
     let ?F1="\<Inter>(f`I)" let ?F2=" {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
     have B0:"?F1 = ?F2" 
       using P8 lat by fastforce
     have B1:"is_inf (pwr X) (filters_on R X) (f`I) ?F1" 
       using P2 lat by blast
     then obtain B2:"is_inf (pwr X)  (filters_on R X) (f`I) ?F2"
       by (simp add: B0)
     have B3:"is_clattice (pwr X) (filters_on R X)"
       using lattice_filters_complete[of X R] por top lat by blast
     have B4:"(f`I) \<subseteq>(filters_on R X) "
       using fil filters_on_iff by blast
     have B5:"antisym (pwr X) (filters_on R X)"
        by (simp add: antisym_on_def powrel8 set_eq_subset)
     have B6:"Inf (pwr X) (filters_on R X) (f`I) = ?F1" 
        using B1 B5 inf_equality[of "pwr X" "filters_on R X" " (f`I)" ?F1] by fastforce
      also have B7:"... = ?F2" 
        using B0 by blast
      finally show ?thesis by blast
    qed
  qed
qed 

lemma filter_sup_lattice:
  assumes por:"pord R X" and
          lat:"is_lattice R X" and
          top:"is_greatest R X m" and 
          ind2:"I \<noteq> {}" and 
          fil:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))"
  shows "Sup (pwr X) (filters_on R X) (f`I) = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). (Inf R X F, x)\<in>R}"
proof-
  let ?fI="f`I" let ?A="\<Union>?fI"
  obtain B0:"?A \<noteq> {}" and B1:"is_inf_semilattice R X"
    using ind2 fil is_filterD1 lat lattD4 by fastforce
  have B2:"f`I \<in> Pow_ne (filters_on R X)"
    by (simp add: ind2 fil Pow_ne_iff filters_on_iff image_subset_iff)
  have B3:"Sup (pwr X) (filters_on R X) (f`I) = filter_closure R X (?A)"
    using por B1 B2 semilat_filters_isl2 by auto
  also have B4:"... = {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R} " 
      unfolding filter_closure using B0 by (simp add: filter_closure_def)
  also have B5:"... = {x \<in> X. \<exists>F \<in> Fpow_ne ?A.  (Inf R X F, x)\<in>R}"
    using Fpow_ne_iff  by (metis (mono_tags, opaque_lifting))
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


lemma fin_filter_sup_lattice:
  assumes por:"pord R X" and 
          lat:"is_lattice R X" and
          top:"is_greatest R X m" and 
          ind1:"finite I" and 
          ind2:"I \<noteq> {}" and 
          fil:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))"
        shows "Sup (pwr X) (filters_on R X) (f`I) =
               {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}" (is "?L = ?R")
proof-
  have eq1:"?L = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). (Inf R X F, x)\<in>R}"  (is "?L = ?R1")
    using assms filter_sup_lattice[of X R m I f] by presburger
  have eq2:"f`I \<noteq> {}"
    using ind2 by auto
  show "?L=?R"
  proof(rule order.antisym)
    show "?L \<subseteq> ?R" 
    proof
      fix z assume zil:"z \<in> ?L"
      obtain F where B0:"F \<in> Fpow_ne (\<Union>(f`I))" and B1:"(Inf R X F, z)\<in>R"
        using eq1 zil by fastforce
      obtain "z \<in> ?R1"
        using eq1 zil by blast
      then obtain B2:"z \<in> X"
        by blast 
      have B3:"\<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), z)\<in>R"
      proof-
        define G where "G = {(i, w)|w i. w \<in> F \<and> (w \<in> f i)}"
        define x where "x = (\<lambda>i. if G``{i} \<noteq> {} then Inf R X (G``{i}) else SOME z. z \<in> (f i))"
        have C0:"\<And>i. \<lbrakk>i \<in> I;  G``{i} \<noteq> {}\<rbrakk>  \<Longrightarrow> G``{i} \<subseteq> F"
          using G_def by force
        have C1:"\<And>i w. \<lbrakk>i \<in> I;  G``{i} \<noteq> {};w \<in> G``{i}\<rbrakk>\<Longrightarrow>w \<in> f i"
          using G_def by force
        have C2:"\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)"
        proof-
          fix i assume imem:"i \<in> I"
          show "x i \<in> f i"
          proof(cases " G``{i} \<noteq> {}")
            case True
            then obtain C20:"x i = Inf R X (G``{i})" and C21:"G``{i} \<subseteq> f i"
              using C1 imem x_def by auto
            have C22:"finite (G``{i})"
              by (metis B0 C0 Fpow_ne_iff True finite_subset imem)
            have C23:"Inf R X (G``{i}) \<in> (f i)"
              using C21 C22 True fil filter_inf_closed3 imem lat latt_iff por by blast
            then show ?thesis
              using C20 by auto
          next
            case False
            then show ?thesis
              unfolding x_def using fil imem is_filterD1 some_in_eq  by metis
          qed
        qed
        have C3:"\<And>w. w \<in> F \<Longrightarrow>(\<exists>wi \<in> (x` I). (wi, w)\<in>R)"
        proof-
          fix w assume wmem:"w \<in> F"
          obtain i where C30:"i \<in> I" and C31:"w \<in> (f i)"
            by (metis B0 Fpow_neD UN_E subsetD wmem)
          then obtain C32:"G``{i} \<noteq> {}" and C33:"x i =  Inf R X (G``{i})" and C34:"w \<in> G``{i}"
            using G_def wmem x_def by auto
          obtain C35:"finite (G``{i})" and C36:"(G``{i}) \<subseteq> X"
            by (meson B0 C0 C1 C30 C32 Fpow_neD fil finite_subset is_filterD1 subsetD subsetI)
          obtain C37:"(Inf R X (G``{i}), w)\<in>R"
            by (meson C32 C34 C35 C36 Fpow_neI1 antisym_on_converse is_infD1 lat lattD4 por ssl_fin_sup7 trans_on_converse)
          then show "(\<exists>wi \<in> (x` I). (wi, w)\<in>R)"
            using C30 C33 imageI  by metis
        qed
        obtain C4:"finite (x` I)" and C5:"x` I \<subseteq> X" and C6:"\<And>i. i \<in> I \<Longrightarrow> (f i) \<subseteq> X"
          by (metis C2 fil finite_imageI image_subset_iff ind1 is_filterD1 subsetD)
        obtain C7:"\<Union>(f`I) \<subseteq> X"
          using C6 by auto
        obtain C8:"finite F" and C9:"F \<subseteq> X" and C10:"F \<noteq> {}"
          by (metis B0 C7 Fpow_ne_iff subset_trans)
        have C11:"(Inf R X (x` I), Inf R X F)\<in>R"
          apply(rule_tac ?X="X" and ?A1.0="x` I" and ?A2.0="F" in inf_comp)
          apply (simp add: por)
          apply (simp add: C5)
          apply (simp add: C9)
          apply (simp add: C4 C5 Fpow_neI1 ind2 lat lattD4 por ssl_fin_sup7)
          apply (simp add: C10 C8 C9 Fpow_neI1 lat lattD4 por ssl_fin_sup7)
          using C3 by blast
        have C12:"Inf R X (x` I) \<in> X"
          by (simp add: C4 C5 Fpow_neI1 ind2 lat lattD4 por ssl_fin_sup6)
        have C13:" Inf R X F \<in> X"
          by (simp add: C10 C8 C9 Fpow_neI1 lat lattD4 por ssl_fin_sup6)
        have C14:"(Inf R X (x` I), z)\<in>R"
          by (meson B1 B2 C11 C12 C13 por trans_onD)
        then show ?thesis
          using C2 by blast
      qed
      then obtain x where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))" and B4:"(Inf R X (x` I), z)\<in>R"
        by blast
      then show "z \<in> ?R"
        using B2 by blast 
    qed
    show "?R \<subseteq> ?L"
    proof
      fix z assume zil:"z \<in> ?R"
      then obtain x where prd:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))" and zgt:"(Inf R X (x` I) ,z)\<in>R"
        by blast 
      have ximem:"(x` I) \<in> Fpow_ne (\<Union>(f`I))"
      proof(rule Fpow_neI1)
        show "x ` I \<subseteq> \<Union> (f ` I)"
          using prd by auto
        show "x ` I \<noteq> {}"
          by (simp add: ind2)
        show "finite (x ` I)"
          by (simp add: ind1)
      qed
      show "z \<in> ?L"
        using eq1 ximem zgt zil by blast
    qed
  qed
qed


lemma fin_filter_sup_distlat:
  assumes por:"pord R X" and 
          dlt:"distributive_lattice R X" and
          top:"is_greatest R X m" and 
          ind1:"finite I" and 
          ind2:"I \<noteq> {}" and 
          fil:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))"
        shows "Sup (pwr X) (filters_on R X) (f`I) =
               {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf R X (x`I) = y}" (is "?L = ?R")
proof-
  obtain lat:"is_lattice R X"
    by (simp add: distr_latticeD5 dlt) 
  obtain ssl:"is_sup_semilattice R X"
    by (simp add: lat lattD42)
  obtain dpr:"pord (dual R) X"
    by (simp add: por refl_dualI)
  obtain clt:"is_clattice (pwr X) (filters_on R X)"
    using lat lattice_filters_complete por top by fastforce
  obtain fis:"(f`I) \<subseteq> (filters_on R X)"
    using fil filters_on_iff by blast
  obtain lsb:"?L \<subseteq> X"
    using lat por fis ind1 ind2 Fpow_neI1 filters_on_iff lattice_filters_isl8 finite_imageI
          image_is_empty is_filterD1 by meson
  obtain eq1:"Sup (pwr X) (filters_on R X) (f`I) = 
          {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}" (is "?L = ?R1")
    using fin_filter_sup_lattice[of X R m I f] por top lat ind1 ind2 fil by blast 
  show "?L=?R"
  proof
    show "?L \<subseteq> ?R"
    proof
      fix y assume ymem1:"y \<in> ?L"
      then obtain ymem2:"y \<in> X" and ymem3:"y \<in> ?R1"
        using lsb eq1 by blast
      then obtain x where prd:"\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> f i " and ygt:"(Inf R X (x` I), y)\<in>R"
        by blast
      then obtain xfin:"finite (x`I)" and xisub:"x`I \<subseteq> X" and xineq:"x`I \<noteq> {}"
        using ind1 ind2 is_filterD1[of R X ] fil by blast
      have ex1:"\<exists>x1. (\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf R X (x1` I) =y"
      proof-
        define x1 where "x1 = (\<lambda>i. Sup R X {y, x i})"
        then obtain x1fin:"finite (x1`I)"  and x1ineq:"x1`I \<noteq> {}"
          using ind1 ind2 by blast 
        obtain x1isub:"(x1 ` I) \<subseteq> X"
          using ssl ssl_ex_sup5 xisub ymem2 por image_subset_iff x1_def by metis
        obtain ix1mem:"Inf R X (x` I) \<in> X"
          by (meson Fpow_ne_iff dpr lat latt_iff ssl_fin_sup6 xfin xineq xisub)
        have B0:"y = Sup R X {y, Inf R X (x` I)}"
          by (simp add: bsup_or2 ix1mem por ssl ygt ymem2)
        have B1:"... = Inf R X {Sup R X {y,a}|a.  a \<in> (x` I)}"
          using dlt fin_distr1 por xfin xineq xisub ymem2 by fastforce 
        have B2:"... = Inf R X {Sup R X {y, x i}|i. i \<in> I}"
        proof-
          have "{Sup R X {y, a} |a. a \<in> x ` I} = {Sup R X {y, x i} |i. i \<in> I}" by blast
          then show ?thesis by presburger
        qed
        have B3:"... = Inf R X {x1 i|i. i \<in> I}"  
          using x1_def by auto
        have B4:"... = Inf R X (x1 ` I)"  
          by (simp add: Setcompr_eq_image)
        have B5:"Inf R X (x1 ` I) = y"  
          using B0 B1 B2 B3 B4 by presburger
        have B6:"\<And>i. i \<in> I \<Longrightarrow>  (x1 i) \<in> (f i)"
        proof-
          fix i assume i0:"i \<in> I"
          obtain "(x i) \<in> f i" and "(x i, x1 i)\<in>R" and "(x1 i) \<in> X" and "is_filter R X (f i)"
            by (metis fil i0 image_subset_iff por prd ssl ssl_ex_sup0b ssl_ex_sup5 x1_def xisub ymem2)
          then show "(x1 i ) \<in> (f i)"
            by (meson is_filterD1 is_ord_clE1)
        qed
        show ?thesis 
           using B5 B6 by blast
       qed
       then show "y \<in> ?R"
         using ymem2 by blast 
    qed
    show "?R \<subseteq> ?L"
    proof
      fix y assume ymem1:"y \<in> ?R"
      then obtain x1 where prd:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i))" and eq3:"Inf R X (x1` I) =y"
        by blast 
      obtain ymem2:"y \<in> X"
        using ymem1 by blast
      then obtain ygt:"(Inf R X (x1` I), y)\<in>R"
        using eq3 por reflE1 by blast  
      then show "y \<in> ?L"
        using eq1 prd ymem2 by blast
    qed
  qed
qed
    
lemma filter_sup_distattice:
  assumes por:"pord R X" and
          dlt:"distributive_lattice R X" and
          top:"is_greatest R X m" and 
          ind2:"I \<noteq> {}" and 
          fil:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))"
  shows "Sup (pwr X) (filters_on R X) (f`I) = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). x = Inf R X F}"  (is "?L=?R")
proof-
 obtain lat:"is_lattice R X"
    by (simp add: distr_latticeD5 dlt) 
  obtain ssl:"is_sup_semilattice R X"
    by (simp add: lat lattD42)
  obtain dpr:"pord (dual R) X"
    by (simp add: por refl_dualI)
  obtain clt:"is_clattice (pwr X) (filters_on R X)"
    using lat lattice_filters_complete por top by fastforce
  have B0:"?L = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). (Inf R X F, x)\<in>R}" (is "?L=?R2")
    using filter_sup_lattice[of X R m I] por top ind2 fil lat by presburger
  have RL:"?R \<subseteq> ?L"
  proof
    fix x assume R0:"x \<in> ?R"
    then obtain F where F0:"F\<in>Fpow_ne (\<Union> (f ` I))" and "x = Inf R X F"
      by blast
    then obtain "(Inf R X F, x)\<in>R"
      using R0 por reflE1 by auto
    then obtain "x \<in> ?R2"
      using F0 R0 by blast
    then show "x \<in> ?L"
      using B0 by blast
  qed
  have LR:"?L \<subseteq> ?R"
  proof
    fix x assume L0:"x \<in> ?L"
    then obtain F where F0:"x \<in> X" and F1:"F\<in>Fpow_ne (\<Union> (f ` I))" and F2:"(Inf R X F,x)\<in>R"
      using B0 by auto
    from F1 obtain F3:"finite F" and F4:"F \<noteq> {}" and F5:"F \<subseteq> X"
      by (metis Fpow_ne_iff SUP_le_iff dual_order.trans fil is_filterD1)
    then have F7:"Sup R X {x, (Inf R X F)} = Inf R X {Sup R X {x, xj}|xj. xj \<in> F}"
      using fin_distr1[of R X F x] por  F0 dlt by fastforce
    have F8:"x = Sup R X {x, (Inf R X F)}"
      by (simp add: F0 F2 F3 F4 F5 Fpow_neI1 bsup_or2 lat lattD4 por ssl_fin_sup6)
    have F9:"\<And>y. y \<in> F \<Longrightarrow> (\<exists>i. i \<in> I \<and> (y \<in> f i))"
    proof-
      fix y assume y0:"y \<in> F"
      then obtain y1:"y \<in> \<Union> (f ` I)"
        using F1 Fpow_neD by blast
      then obtain Fj where y2:"Fj \<in> (f`I)" and y3:"y \<in> Fj"
        by blast
      then obtain i where y4:"i \<in> I" and y5:"Fj = (f i)"
        by blast
      then show "(\<exists>i. i \<in> I \<and> (y \<in> f i))"
        using y3 by blast
    qed
    let ?G="{Sup R X {x, xj}|xj. xj \<in> F}"
    have L1:"?G \<in>Fpow_ne (\<Union> (f ` I)) "
    proof(rule Fpow_neI1)
      show "?G \<subseteq> \<Union>(f`I)"
      proof
        fix xa assume C0:"xa \<in> ?G"
        then obtain xj where C1:"xj \<in> F" and C2:"xa = Sup R X {x, xj}"
          by blast
        then obtain i where C3:"i \<in> I" and C4:"xj \<in> (f i)"
          using F9 by auto
        obtain "(xj,xa)\<in>R" and "xa \<in> X"
          by (metis C1 C2 F0 F5 por ssl ssl_ex_sup0b ssl_ex_sup5 subset_eq)
        then obtain "xa \<in> (f i)"
          by (metis C3 C4 fil is_filterD1 is_ord_clE1)
        then show "xa \<in>  \<Union>(f`I)"
          using C3 by blast
      qed
      show "?G \<noteq> {}"
        by (simp add: F4)
      show "finite ?G"
        by (simp add: F3)
    qed
    have L2:"x = Inf R X ?G"
      using F7 F8 by presburger
    then have L3:"\<exists>G\<in>Fpow_ne (\<Union> (f ` I)). x = Inf R X G"
      using L1 by blast
    then show "x \<in> ?R"
      using F0 by blast
  qed
  from LR RL show ?thesis
    by blast
qed
    
      
         
section MeetReducibility

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
    using B0 Pow_neD by blast
  obtain a where B4:"a \<in> A"  
    using B0 Pow_neD by fastforce  
  have B3:"(x, a) \<in> R \<and> x \<noteq> a"
    using B1 B2 B4 is_supD1 by fastforce  
  show "\<not>(is_greatest R X x)" 
  proof(rule ccontr)
   assume A1:"\<not>(\<not>(is_greatest R X x))" then obtain B30:"is_greatest R X x" by simp
  then have B31:"(a, x) \<in> R"
    by (meson B0 B4 Pow_ne_iff is_greatestD1 subsetD)
  have B32:"a \<in> X"
    using B0 B4 Pow_neD by blast
  have B33:"(x, a) \<in>R"
    by (simp add: B3)
  then have B34:"a = x"
    by (meson A0 B30 B32 antisym_onD is_greatestD1)
  then show False
    using B3 by auto
  qed
qed

lemma mredD3:
  assumes por:"pord R X" and 
          clt:"is_clattice R X" and
          ntp:"\<not>(is_greatest R X m)" and
          mix:"m\<in>X"
  shows "{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x} \<noteq> {}"
proof-
  from por clt obtain top where "is_greatest R X top"
    using clatD1 csupD3 by blast
  then obtain "top \<in> X" and "(m,top)\<in>R" and "m \<noteq> top"
    using is_greatestD1 mix ntp by fastforce
  then show ?thesis
    by blast
qed

lemma mredD4:
  assumes por:"pord R X" and
          clt:"is_clattice R X" and 
          mix:"m \<in> X" and
          ntp:"\<not>(is_greatest R X m)" and 
          nli:"\<not>((m, Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}) \<in> R \<and> m \<noteq> Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x})"
  shows "meet_reducible R X m"
proof-
  let ?A="{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  obtain B0:"?A \<subseteq> X" and B1:"?A \<noteq> {}" 
    using por clt ntp mix mredD3[ of X R m] by blast 
  have B2:"(m, Inf R X ?A)\<in>R"
    using por clt clatD22[of X R ?A] mix ex_inf2[of X R ?A m]  by blast 
  have B3:"m = Inf R X ?A"
    using B2 nli by blast   
  have B4:"?A \<in> Pow_ne X"
    using B1 Pow_ne_iff by auto
  have B5:"m \<notin> ?A"  
    by simp
  obtain "is_inf R X ?A (Inf R X ?A)"
    using B0 B1 cinfD4 clatD2 clt por by blast
  then have B6:"is_inf R X ?A m"
    using B3 by fastforce   
  then show "meet_reducible R X m"
    using B4 mredI1[of ?A X m R] by blast
qed

lemma filter_compl:
  assumes por:"pord R X" and
          lat:"is_lattice R X" and
          pfl:"is_pfilter R X F"
  shows filter_compl1:"X-F \<noteq> {}" and
        filter_compl2:"X-F \<noteq> X" and
        filter_compl3:"\<And>x y. \<lbrakk>x \<in>(X-F); y \<in>X; (y,x)\<in>R\<rbrakk>\<Longrightarrow>y \<in> X-F" and
        filter_compl4:"is_ord_cl X (X-F) (dual R)" and
        filter_compl5:"\<And>x y. \<lbrakk>sup_prime R X F; x \<in> (X-F); y \<in> (X-F)\<rbrakk>\<Longrightarrow>Sup R X {x, y} \<in> (X-F)" and
        filter_compl6:"\<And>x y. \<lbrakk>sup_prime R X F; x \<in> X; y \<in>X; Inf R X {x, y} \<in> (X-F)\<rbrakk> \<Longrightarrow> (x \<in> (X-F)) \<or> (y \<in> (X-F))" and
        filter_compl7:"sup_prime R X F \<Longrightarrow> inf_prime R X (X-F)"
proof-
  obtain fil:"is_filter R X F" and nst:"F \<noteq> X"
    using is_pfilter_def pfl by blast
  obtain ocl:"is_ord_cl X F R" and ddr:"is_dir F (dual R)" and nem:"F \<noteq> {}" and fsb:"F \<subseteq> X"
    using is_filterD1 fil by auto
  have ssl:"is_sup_semilattice R X" 
    using lattD42 lat by auto
  show P1:"X-F \<noteq> {}"
    using fsb nst by auto
  show P2: " (X - F \<noteq> X)"
    using fsb nem by auto
  show P3:"\<And>x y. \<lbrakk>x \<in>(X-F); y \<in>X; (y,x)\<in>R\<rbrakk>\<Longrightarrow>y \<in> X-F"
  proof-
    fix x y assume xmem:"x \<in>(X-F)" and ymem:"y\<in>X" and ylx:"(y,x)\<in>R"
    then show "y \<in> X-F" 
      using ocl is_ord_clE1[of X F R] Diff_iff by blast
  qed
  show P4:"is_ord_cl X (X-F) (dual R)"
    unfolding is_ord_cl_def using converseD P3 by metis
  show P5:"\<And>x y. \<lbrakk>sup_prime R X F; x \<in> (X-F); y \<in> (X-F)\<rbrakk>\<Longrightarrow>Sup R X {x, y} \<in> (X-F)"
  proof-
    fix x y assume spr:"sup_prime R X F" and xmme:"x \<in> X-F" and ymem:"y \<in> X-F"
    show "Sup R X {x, y} \<in> (X-F)"
      using por ssl ssl_ex_sup5[of X R] sup_primeD1 spr xmme ymem by fastforce 
  qed
  show P6:"\<And>x y. \<lbrakk>sup_prime R X F; x \<in> X; y \<in>X; Inf R X {x, y} \<in> (X-F)\<rbrakk> \<Longrightarrow> (x \<in> (X-F)) \<or> (y \<in> (X-F))"
  proof-
    fix x y assume spr:"sup_prime R X F" and xmem:"x\<in>X" and ymem:"y\<in>X" and imem:"Inf R X {x,y}\<in>(X-F)"
    then show "(x \<in> (X-F)) \<or> (y \<in> (X-F))"
      using lattD31 por fil filter_inf_closed1 DiffD2 DiffI lat by metis
  qed
  show P7:"sup_prime R X F \<Longrightarrow> inf_prime R X (X-F)"
  proof-
    assume "sup_prime R X F"
    then show "inf_prime R X (X-F)"
      using inf_primeI1[of X R "X-F"] P6 by presburger
  qed
qed

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

lemma compact_gen:
  assumes clt:"is_clattice R X" and
          cgn:"compactly_generated R X" and
          por:"pord R X"
  shows compact_gen1:"\<And>x. x \<in> X \<Longrightarrow> x = Sup R X {k \<in> compact_elements R X. (k, x)\<in>R}" and
        compact_gen2:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X;\<not>((y, x)\<in>R)\<rbrakk>\<Longrightarrow>\<exists>k \<in> compact_elements R X. (k, y)\<in>R \<and> \<not>((k,x)\<in>R)"
proof-  
  show P0:"\<And>x. x \<in> X \<Longrightarrow> x = Sup R X {k \<in> compact_elements R X. (k, x)\<in>R}"
  proof-
    fix x assume xmem:"x \<in> X"
    show "x = Sup R X {k \<in> compact_elements R X. (k, x)\<in>R}"
    proof-
      let ?K=" compact_elements R X"  let ?Kd="{k \<in> ?K. (k, x)\<in>R}"
      obtain Kx where kxmem:"Kx \<in> Pow ?K" and xis:"is_sup R X Kx x" 
        using xmem cgn compactly_generatedD1[of R X x] by blast
      obtain ksub:"?K \<subseteq> X" and kdsub:"?Kd \<subseteq> X"
        using compact_elements_sub by fastforce
      obtain B0:"Kx \<subseteq> ?Kd"
        using is_supD1 kxmem xis by fastforce
      obtain B1:"Kx \<subseteq> X"
        using B0 kdsub by auto
      have B2:" Sup R X Kx \<in> ubd R X ?Kd"
        using ubdI1[of "Sup R X Kx" X ?Kd R] CollectD por sup_equality xis xmem by fastforce
      have B3:"(Sup R X ?Kd, Sup R X Kx)\<in>R"
        by (simp add: B2 clatD4 clt kdsub por)
      have B4:" Sup R X Kx = x"
        by (simp add: por sup_equality xis)   
      have B5:"(x, Sup R X ?Kd)\<in>R"
        using B0 B4 clt kdsub por sup_iso1 by blast  
      have B6:"(Sup R X ?Kd, x)\<in>R"
        using B3 B4 by auto
      have B7:" Sup R X ?Kd \<in> X"
        by (simp add: clatD21 clt ex_sup5 kdsub por) 
      show ?thesis
        using B5 B6 B7 antisym_onD por xmem by fastforce 
      qed
    qed
  show P1:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X;\<not>((y, x)\<in>R)\<rbrakk>\<Longrightarrow>\<exists>k \<in> compact_elements R X. (k, y)\<in>R \<and> \<not>((k,x)\<in>R)"
  proof-
    fix x y assume xmem:"x \<in> X" and ymem:"y \<in> X" and nlq:"\<not>((y,x)\<in>R)"
    let ?Kx="{k \<in> compact_elements R X. (k, x)\<in>R}" let ?Ky=" {k \<in> compact_elements R X. (k, y)\<in>R}"
    obtain B0:"x = Sup R X ?Kx" and B1:"y = Sup R X ?Ky" 
      using xmem P0[of x] ymem P0[of y] by blast
    have "\<not> (?Ky \<subseteq> ?Kx)"
    proof(rule ccontr)
      assume c0:"\<not>(\<not>(?Ky \<subseteq> ?Kx))" then obtain "?Ky \<subseteq> ?Kx" 
        by simp
      also obtain "?Kx \<subseteq> X"
        using compact_element_memD2 by fastforce
      then obtain "(Sup R X ?Ky, Sup R X ?Kx)\<in>R"
        using sup_iso1[of X R ?Ky  ?Kx] clt por calculation by fastforce
      then show False
        using B0 B1 nlq by auto
    qed
    then obtain B2:"?Ky - ?Kx \<noteq> {}"
      by simp
    then obtain k where "k \<in> ?Ky - ?Kx"
      by blast
    then show "\<exists>k \<in> compact_elements R X. (k, y)\<in>R \<and> \<not>((k,x)\<in>R)"
      by blast
  qed
qed
      
    
lemma meet_reduction1:
  assumes A0:"is_clattice R X" and
          A1:"antisym R X" and
          A2:"trans R X" and
          A3:"refl R X" and
          A4:"m \<in> X" and
          A5:"meet_reducible R X m"
  shows " m \<in> lbd R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  using A4 ubdI1 by fastforce


lemma meet_representation:
  assumes clat:"is_clattice R X" and por:"pord R X" and mmx:"m \<in> X" and mrd:"meet_reducible R X m"
  shows meet_reduction2:"m = Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}" and
        meet_reduction3:"is_inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x} m"
proof-
  let ?A="{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  obtain A where B0:"A \<in> Pow_ne X" and B1:"m \<notin> A" and  B2:"is_inf R X A m"
    using mrd mredD1[of R X m] by blast
  obtain B3:"A \<subseteq> X" and B4:"A \<noteq> {}"
    using B0 Pow_neD by auto
  obtain cis:"is_cinf_semilattice R X"
    by (simp add: clat clatD2)
  obtain B5:"Inf R X A = m"
    by (simp add: por B2 inf_equality)
  have B6:"\<And>x. x \<in> A \<Longrightarrow> (m, x)\<in>R \<and> m \<noteq> x"
  proof-
    fix x assume A6:"x \<in> A"  show "(m, x)\<in>R \<and> m \<noteq> x"  
      using A6 B1 B2 is_supD1 by fastforce
  qed
  obtain B7:"A \<subseteq> ?A" and B8:"?A \<subseteq> X" and B9:"?A \<noteq> {}"
    using B3 B4 B6 by blast
  obtain B10:"Inf R X ?A \<in> X" and B11:"Inf R X A \<in> X"
    using clat por mmx B5 B8 B9 clatD32 by blast
  have B12:"(m, Inf R X ?A)\<in>R"
    by (simp add: clat por mmx mrd clatD22 ex_inf3 meet_reduction1)
  have B13:"(Inf R X ?A,Inf R X A)\<in>R"
    by (simp add: B7 clat inf_iso1 por)
  have B14:"(Inf R X ?A, m)\<in>R"
    using B13 B5 by blast
  then show P0:"m = Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}" 
    using por mmx B10 B12 antisym_onD by fastforce
  show P1:"is_inf R X ?A m"
    using P0 B8 B9 cis por cinfD4[of X R ?A] by presburger
qed


lemma lbd_lt_sup:
  assumes ne:"A \<noteq> {}" and
          lb:"l \<in> lbd R X A" and
          sp:"is_sup R X A s" and
          tr:"trans R X" and
          sb:"A \<subseteq> X"
  shows "(l,s)\<in>R"
proof-
  obtain a where A0:"a \<in> A"
    using ne by blast
  then obtain "l \<in> X" and "a \<in> X" and "s \<in> X"
    using sp is_supD4[of R X A s] lb sb ubdD1[of l "dual R" X A] subsetD[of A X a] by blast 
  also obtain "(l, a)\<in>R" and "(a,s)\<in>R"
    using A0 converse.cases is_supD3[of R X A s a] lb sp ubdD2[of l "dual R" X A a] by blast
  then show "(l,s)\<in>R"
    using calculation tr trans_onD[of X R l a s] by blast
qed
  
lemma mirred_rep1:
  assumes clt:"is_clattice R X" and
          cpg:"compactly_generated R X" and
          por:"pord R X" and
          a0:"a\<in>X" and
          b0:"b\<in>X " and
          ab0:"(b,a)\<notin>R" and 
          k0:"is_compact R X k" and
          kb0:"(k,b)\<in>R" and 
          ka0:"(k,a)\<notin>R" 
        shows mirr1:"\<And>D. \<lbrakk>D\<subseteq>{q\<in>X. (a,q)\<in>R \<and> (k,q)\<notin>R};is_dir D R;D\<noteq>{}\<rbrakk>\<Longrightarrow>Sup R X D\<in>{q\<in>X. (a,q)\<in>R \<and> (k,q)\<notin> R}" and
              mirr2:"\<exists>m \<in> {q\<in>X. (a,q)\<in>R\<and>(k,q)\<notin> R}. \<forall>q \<in> {q \<in> X. (a,q)\<in>R \<and> (k,q)\<notin> R}.  (m,q)\<in>R \<longrightarrow> q = m" and
              mirr3:"\<And>m. \<lbrakk>m \<in> {q\<in>X. (a,q)\<in>R\<and>(k,q)\<notin>R};(\<And>q. \<lbrakk>q\<in>{q\<in>X. (a,q)\<in>R\<and>(k,q)\<notin>R};(m,q)\<in>R\<rbrakk>\<Longrightarrow>q=m)\<rbrakk>\<Longrightarrow>\<not>(meet_reducible R X m)"
proof-
  let ?Q=" {q\<in>X. (a,q)\<in>R\<and>(k,q)\<notin>R}"
  obtain Q0:"?Q \<subseteq> X"
    by simp
  obtain ssl:"is_sup_semilattice R X"
    using clatD1 clt csup_fsup by auto
  show P0:"\<And>D. \<lbrakk>D\<subseteq>?Q;is_dir D R;D\<noteq>{}\<rbrakk>\<Longrightarrow>Sup R X D\<in>?Q"
  proof-
    fix D assume  D0:"D \<subseteq>?Q" and D1:"is_dir D R" and  D2:"D\<noteq>{}"
    show "Sup R X D \<in>?Q"
    proof-
      obtain j where B1:"is_sup R X D j"
        by (meson Q0 D0 clatD21 clt dual_order.trans por) 
      have B2:"j \<in> X"
        by (meson B1 is_supD1) 
      have B3:"\<And>d. d \<in> D \<Longrightarrow> (a,d)\<in>R"
        using D0 by blast   
      have B4:"a \<in> lbd R X D"
        by (simp add: B3 a0 ubdI1)  
      have B5:"(a, j)\<in>R"
        using B1 B4 D0 D2 Q0 subset_trans[of D ?Q X] lbd_lt_sup[of D a R X j] por by fastforce
      have B6:"\<not> ((k,j)\<in>R)"
      proof(rule ccontr)
        assume P0:"\<not>(\<not> ((k,j)\<in>R))" 
        obtain P1:"(k,j)\<in>R"  
          using P0 by auto
        have B7:"(k,Sup R X D)\<in>R"
          using B1 P1 por sup_equality by force   
        have B8:"D \<in> Pow_ne X"
          by (meson Q0 D0 D2 Pow_neI1 subset_trans)
        obtain d where B10:"d \<in> D \<and> (k,d)\<in>R"
          by (meson B7 B8 ssl D1 compactD3 k0 por)
        show False
          using B10 D0 by auto
      qed
      have B11:"j \<in> ?Q"   
        by (simp add: B2 B5 B6)
      show "Sup R X D \<in> ?Q"
        using B1 B11 por sup_equality by fastforce 
    qed
  qed
  show P1:"\<exists>m \<in> ?Q. \<forall>q \<in>?Q.  (m,q)\<in>R \<longrightarrow> q = m"
  proof(rule predicate_Zorn)
  show "partial_order_on ?Q (relation_of (\<lambda>x y. (x, y) \<in> R) ?Q)"
  proof(rule partial_order_on_relation_ofI)
    show "\<And>aa. aa \<in> ?Q \<Longrightarrow> (aa, aa) \<in> R"
      using por refl_def by fastforce
    show "\<And>aa b c. aa \<in> ?Q \<Longrightarrow> b \<in>?Q \<Longrightarrow> c \<in> ?Q \<Longrightarrow> (aa, b) \<in> R \<Longrightarrow> (b, c) \<in> R \<Longrightarrow> (aa, c) \<in> R"
    proof-
      fix aa b c assume "aa \<in> ?Q" and "b \<in>?Q" and " c \<in> ?Q" and aab:"(aa, b) \<in> R" and bc:"(b, c) \<in> R"
      then obtain "aa \<in> X" and "b \<in> X" and "c \<in> X"
        by fastforce
      then show "(aa, c) \<in> R"
        using por aab bc trans_onD[of X R aa b c] by simp
    qed
    show " \<And>aa b. aa \<in>?Q\<Longrightarrow> b \<in>?Q\<Longrightarrow> (aa, b) \<in> R \<Longrightarrow> (b, aa) \<in> R \<Longrightarrow> aa = b"
      using por antisym_onD by fastforce
  qed
  show P1:"\<And>C. C \<in> Chains (relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q) \<Longrightarrow> \<exists>u\<in>?Q. \<forall>q\<in>C. (q, u)\<in>R"
  proof-
    fix C assume A8:"C \<in> Chains (relation_of (\<lambda>x y. (x, y) \<in> R) ?Q)"
    have B0:"C \<subseteq> X"  
       using A8 Chains_relation_of by blast
     have B1:"\<forall>c. c \<in> C \<longrightarrow> (a, c)\<in>R"  
       using A8 Chains_relation_of by force
     have B2:"\<forall>c. c \<in> C \<longrightarrow> \<not> (k, c)\<in>R"   
       using A8 Chains_relation_of by blast
    show "\<exists>u\<in> ?Q. \<forall>q\<in>C. (q, u)\<in>R"
    proof(cases "C = {}")
      case True
      then show ?thesis  
        using a0 ka0 por reflE1 by force
      next
        case False
        have B3:"C \<noteq> {}"   
          by (simp add: False)
        have B4:"\<And>x y. x \<in> C \<and> y \<in> C \<longrightarrow> (\<exists>z \<in> C. (x,z)\<in>R \<and> (y, z)\<in>R)"
        proof
          fix x y assume A10:"x \<in> C \<and>  y \<in> C"
          have B1:"(x, y) \<in> relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q \<or> (y, x) \<in> relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q" 
            using Chains_def[of " relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q"] A8 A10 by auto
          have B2:"(x, y)\<in>R \<or> (y, x)\<in>R" 
            using B1 relation_of_def[of "((\<lambda>x y. (x, y) \<in> R))" "?Q"] by blast
          show "(\<exists>z \<in> C. (x,z)\<in>R \<and> (y, z)\<in>R)"  
            using A10 B2 B0 reflE1 subset_iff por by metis
      qed
      have B5:"is_dir C R" 
        by (simp add: B4 is_dirI1)
      have B6:"C \<subseteq> ?Q"   
         using A8 Chains_relation_of by blast
      have B7:"Sup R X C \<in> ?Q"
         using clt cpg a0 b0 ab0 k0 kb0 ka0 B3 B5 B6 P0 by presburger
      have B8:"\<forall>c  \<in> C. (c, Sup R X C)\<in>R"
        by (simp add: B0 clatD21 clt ex_sup0 por)
      then show ?thesis   
        using B7 by blast 
      qed
    qed
  qed
  show P2:"\<And>m. \<lbrakk>m \<in> {q\<in>X. (a,q)\<in>R\<and>(k,q)\<notin>R};(\<And>q. \<lbrakk>q\<in>?Q;(m,q)\<in>R\<rbrakk>\<Longrightarrow>q=m)\<rbrakk>\<Longrightarrow>\<not>(meet_reducible R X m)"
  proof-
    fix m assume m0:"m \<in>?Q" and m1:"(\<And>q. \<lbrakk>q\<in>?Q;(m,q)\<in>R\<rbrakk>\<Longrightarrow>q=m)"
    show "\<not>(meet_reducible R X m)"
    proof(rule ccontr)
      assume contr:"\<not>\<not>(meet_reducible R X m)"
      obtain mrd:"meet_reducible R X m"  
        using contr by auto
      have B0:"\<And>x. \<lbrakk>x\<in>X;(m,x)\<in>R;(m\<noteq>x)\<rbrakk>\<Longrightarrow>(k,x)\<in>R"
      proof-
        fix x assume x0:"x\<in>X" and x1:"(m,x)\<in>R" and x2:"m\<noteq>x"
        obtain x3:"x \<notin> ?Q"
          using m1 x1 x2 by blast
        obtain x40:"m \<in> X" and x41:"(a, m)\<in>R" and x42:"(k, m) \<notin> R"
          using m0 by auto
        obtain x4:"(a,x)\<in>R"
          using a0 x40 x0 x41 x1 por trans_onD[of X R a m x] by simp
        show "(k,x)\<in>R"
          using x0 x3 x4 by blast
      qed
      have B1:"m=Inf R X {x \<in> X. (m,x)\<in>R \<and> (m \<noteq> x)}"
        using clt contr m0 meet_reduction2 por by fastforce  
      have B2:"k \<in> lbd R X {x \<in> X.(m,x)\<in>R \<and> (m \<noteq> x)}" 
      proof(rule ubdI1)
        show "k \<in> X"
          using compactD2[of R X k] k0 by simp
        show "\<And>a. a \<in> {x \<in> X. (m, x) \<in> R \<and> m \<noteq> x} \<Longrightarrow> (a, k) \<in> dual R"
          using B0 by blast
      qed
      obtain B3:"m \<in> X"
        using m0 by fastforce
      obtain B4:"is_inf R X  {x \<in> X. (m,x)\<in>R \<and> (m \<noteq> x)} m"
        using clt por B3 mrd meet_reduction3[of R X m]  by blast 
      then obtain B5:"(k,m)\<in>R"
        using B1 B2 ex_inf3 por by fastforce
      then show False
        using m0 by auto 
    qed
  qed
qed


lemma mirred_rep2:
  assumes clt:"is_clattice R X" and
          cpg:"compactly_generated R X" and
          por:"pord R X" and
          a0:"a \<in> X"
  shows mirr4:"\<And>b. \<lbrakk>b \<in>X;(b,a)\<notin>R\<rbrakk> \<Longrightarrow>(\<exists>m. m\<in>X \<and> meet_irr R X m \<and>(a,m)\<in>R \<and>(b,m)\<notin>R)" and
        mirr5:"a = Inf R X {m \<in> X. meet_irr R X m \<and> (a, m)\<in>R}"
proof-
  show P0:"\<And>b. \<lbrakk>b \<in>X;(b,a)\<notin>R\<rbrakk> \<Longrightarrow>(\<exists>m. m\<in>X \<and> meet_irr R X m \<and>(a,m)\<in>R \<and>(b,m)\<notin>R)"
  proof-
    fix b assume b0:"b\<in>X" and ba0:"(b,a)\<notin>R"
    show "(\<exists>m. m\<in>X \<and> meet_irr R X m \<and>(a,m)\<in>R \<and>(b,m)\<notin>R)"
    proof-
      obtain k where k0:"k \<in> compact_elements R X" and  kb1:"(k, b)\<in>R" and ka1: "(k,a)\<notin>R"
        by (meson clt cpg a0 b0 ba0 por compact_gen2) 
      let ?Q=" {q\<in>X. (a,q)\<in>R\<and>(k,q)\<notin>R}"
      obtain k1:"is_compact R X k" and k2:"k \<in> X"
        using k0 compact_element_memD1[of k R X] compact_element_memD2[of k R X]  by blast
      obtain m where B3:"m \<in> ?Q \<and> (\<forall>q \<in> ?Q.  (m,q)\<in>R \<longrightarrow> q = m)" 
        using clt cpg a0 b0 k1 kb1 ka1 mirr2[of R X a b k] ba0 por by blast
      have B4:"\<not>(meet_reducible R X m)" 
        using mirr3[of R X a b k m] B3 a0 b0 ba0 clt cpg k1 ka1 kb1 por by blast
      obtain B5:"m \<in> X" and B6:"(a,m)\<in>R" and B7:"(k,m)\<notin>R"
        using B3 by blast
      have B7:"(b,m)\<notin>R"
      proof(rule ccontr)
        assume contr0:"\<not>(b,m)\<notin>R" 
        then obtain contr1:"(b,m)\<in>R"
          by simp
        then show False
          by (meson B5 B7 b0 k2 kb1 por trans_onD)
      qed        
      then show ?thesis
        using B4 B5 B6 by blast 
    qed
  qed
  show P1:"a = Inf R X {m \<in> X. meet_irr R X m \<and> (a, m)\<in>R}"
  proof-
    let ?M="{m \<in> X. meet_irr R X m \<and> (a, m)\<in>R}" 
     obtain top where top:"is_greatest R X top"
       using clatD1 clt csupD3 by blast
     obtain B0:"?M \<subseteq> X" and B1:"top \<in> ?M" and B2:"?M \<noteq> {}"
       by (metis (no_types, lifting) a0 empty_iff is_greatestD1 mem_Collect_eq mredD2 por subsetI top) 
     obtain b where idef:"is_inf R X ?M b"
       using B0 clatD22 clt por by blast  
     have B4:"(a, b)\<in>R"
       using a0 idef is_infD1 by fastforce
     have B5: "\<not>((a,b)\<in>R \<and> a \<noteq> b)"
     proof(rule ccontr)
       assume B5dneg:"\<not> \<not> ((a,b)\<in>R \<and> a \<noteq> b)" obtain B5neg:"(a,b)\<in>R \<and> a \<noteq> b"  
         using B5dneg by auto
       obtain m where B50:"m \<in> X" and B51:"meet_irr R X m" and  B52:"(a, m)\<in>R" and B53:"\<not> ((b, m)\<in>R)"
         by (meson B5neg P0 a0 antisym_onD idef is_supD4 por)   
       have B54:"m \<in> ?M"   
         by (simp add: B50 B51 B52)
       have B55:"(b, m)\<in>R"   
         using B54 idef is_supD1 by fastforce 
       show False
         using B53 B55 by auto
     qed
     have "a = b"  
       using B4 B5 nless_le by blast
     then show ?thesis
       using idef inf_equality por by force  
   qed
qed

lemma meet_irr_imp_fmeet_irr:
  assumes lat:"is_lattice R X" and m0:"m \<in> X" and por:"pord R X" and mir:"meet_irr R X m"
  shows " fin_inf_irr R X m"
proof(rule fin_inf_irrI1)
  fix a b assume A0:"a \<in> X" and A1:"b \<in> X" and A2:"m = Inf R X {a, b}"
  obtain B0:"{a,b}\<subseteq>X" and B1:"finite {a,b}" and B2:"{a,b} \<noteq> {}"
    by (simp add: A0 A1)
  then obtain B3:"{a,b}\<in>Fpow_ne X" and B4:"is_inf R X {a, b} m"
    by (simp add: A2 Fpow_ne_iff lat lattD31 por)
  then obtain "m \<in> {a,b}"
    by (meson B0 B2 Pow_neI1 meet_reducible_def mir)
  then show "m = a \<or> m = b"
    by blast
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
  proof(rule mirr5)
    show "is_clattice (pwr X) (filters_on R X)"
      by (simp add: B1)
    show "compactly_generated (pwr X) (filters_on R X)"
      using B0 by blast
    show "pord (pwr X) (filters_on R X)"
      by (meson equalityD2 pwr_antisym_sub pwr_refl_sub pwr_trans_sub sub_filters_onD1)
    show "F \<in> filters_on R X"
      by (simp add: B2)
  qed
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
    by (simp add: B0 B1 B2 C1 C2 C3 mirr5) 
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
        by (simp add: A0 bot_filters1 distr_latticeD5 filters_on_def lattD4)
      have B431:"X \<in> ubd ?RX ?FX ?FX"
        by (meson B430 C2 pwr_mem_iff reflE1 ubdI1)  
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
  obtain B0:"?A \<in> Pow(Pow X)"
    using lcroD1 by fastforce 
  obtain B1:"?U \<in> Pow X"
    using B0 by blast
  obtain B2:"pord (pwr X) (Pow X)" and B3:"pord (pwr X) (filters_on R X)"
    by (meson PowI filters_on_iff is_filterD1 powrel3 powrel6 powrel7 refl_def refl_onD subsetI)
  have B4:"\<And>f. f \<in> ?A \<Longrightarrow> is_filter R X f"
    using A3 filters_on_iff[of _ R X] is_filterD1[of R X] lcro_filter[of  X R] por by fastforce
  have B5:"\<And>f. f \<in> ?A \<Longrightarrow> f \<subseteq> X \<and> f \<noteq> {}"
    using B4 is_filterD1 by blast
  have B6:"\<And>f. f \<in> ?A \<Longrightarrow> f \<in> Pow_ne X"
    by (simp add: B5 Pow_neI2)
  have B7:"F \<subseteq> X"
    by (meson A3 filters_on_iff is_filterD1) 
  have B8:"\<And>x. x \<in> F \<Longrightarrow> x \<in> lcro R X x"
    using B7 lcro_memI1[of R X ] por subsetD by blast
  have B9:"{lcro R X x|x. x \<in>F} \<in> Pow_ne (filters_on R X)"
    unfolding filters_on_def 
    proof(rule Pow_neI2)
      show "{lcro R X x |x. x \<in> F} \<in> Pow {F. is_filter R X F}"
        using B4 by blast
      show "{lcro R X x |x. x \<in> F} \<noteq> {}"
        using A3 filters_on_iff is_filterD1 by fastforce
    qed
  obtain s where iss:"is_sup (pwr X) (filters_on R X) ?A s"
    using A0 B9 lattice_filters_isl12 por by blast
  obtain B10:"F \<subseteq> ?U" and B11:"?U \<subseteq> X"
    using B1 B8 by blast
  obtain B12:"?U \<subseteq> s"
    using is_supD3 iss pwr_memD by fastforce
  obtain B13:"s \<in> filters_on R X"
    using B3 is_supD4[of "pwr X" "filters_on R X" ?A s] iss by blast
  obtain B14:"s \<subseteq> X" and B15:"s \<in> Pow X"
    by (meson B13 PowI filters_on_iff is_filterD1)
  have B16:"((\<Union>?A),s)\<in>pwr X"
    by (simp add: B11 B12 B14 pwr_memI)
  have B17:"s = Sup (pwr X) (filters_on R X) ?A"
    using B3 iss sup_equality by fastforce
  have B18:"(F, s)\<in>(pwr X)"
    by (meson B10 B12 B14 dual_order.trans pwr_memI)
  have B19:"s \<in> (filters_on R X)"
    by (meson is_supD1 iss)
  have B20:"is_dir s (dual R)"
    using B19 filters_on_iff is_filterD1 by blast
  have B21:"(\<exists>x \<in> X.  lcro R X x = F ) \<Longrightarrow> is_compact (pwr X) (filters_on R X) F "
  proof-
    assume "(\<exists>x \<in> X. lcro R X x = F)" 
    then obtain x where B22:"x \<in> X" and B23:"lcro R X x = F" 
      by auto
    let ?C="filters_on R X"
    have B24:"is_compact (pwr X) ?C (cl_from_clr (pwr X) ?C {x})"
    proof(rule singleton_closure_compact)
      show "clr (pwr X) (Pow X) ?C"
        using A0 A1 A2 filters_on_lattice_compactgen01[of R X top] por by blast
      show "\<And>A. A \<subseteq> ?C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter> A \<in> ?C"
        using A0 A1 A2 filters_on_lattice_compactgen02[of R X top] por by blast
      show "\<And>D. D \<subseteq> ?C \<Longrightarrow> D \<noteq> {} \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union> D \<in> ?C"
        using A0 A1 A2 filters_on_lattice_compactgen03[of R X top] por by blast
      show "x \<in> X"
        by (simp add: B22)
    qed
    have B25:"lcro R X x \<in> ?C"
      using A3 B23 by blast
    have B26:"\<And>a. a \<in> {{x}} \<Longrightarrow> (a, lcro R X x) \<in> pwr X"
      using B22 B23 B7 lcro_memI1 por pwr_mem_iff by fastforce
    have B27:"lcro R X x \<in> ubd (pwr X) (?C) {{x}}"
      by (simp add: B25 B26 ubd_singleton_mem)
    have B28:"is_least (pwr X) (ubd (pwr X) (?C) {{x}}) (lcro R X x)"
    proof(rule is_greatestI3)
      show " lcro R X x \<in> ubd (pwr X) (?C) {{x}}"
        using B27 by fastforce
      show "\<And>a. a \<in> ubd (pwr X) (?C) {{x}} \<Longrightarrow> (a, lcro R X x) \<in> dual (pwr X)"
      proof-
        fix a assume "a \<in> ubd (pwr X) (?C) {{x}}"
        then obtain E0:"a \<in> filters_on R X" and E1:"({x},a)\<in>pwr X"
          by (simp add: ubd_singleton_mem)  
        then obtain E2:"x \<in> a" and E3:"is_ord_cl X a R"
          by (simp add: filters_on_def is_filterD1 pwr_mem_iff)
        then obtain "(lcro R X x) \<subseteq> a"
          by (meson is_ord_clE1 lcroD1 subsetI)
        then obtain  "(lcro R X x,a)\<in>pwr X"
          by (meson E1 pwr_mem_iff)
        then show "(a, lcro R X x) \<in> dual (pwr X)"
          by auto
      qed
    qed
    have B29:"cl_from_clr (pwr X) ?C {x} = lcro R X x"
      by (meson A0 A1 A2 B28 clr_equality filters_on_lattice_compactgen01 por powrel1)
    have B30:"... = F"
      by (simp add: B23)
    then show "is_compact (pwr X) (filters_on R X) F"
      using B24 B29 by auto
  qed
  have B31:"is_compact (pwr X) (filters_on R X) F \<Longrightarrow>  (\<exists>x \<in> X.  lcro R X x = F )"
  proof-
    assume B32:"is_compact (pwr X) (filters_on R X) F"  
    obtain A0 where B33:"A0 \<in> Fpow_ne ?A " and B34:"(F, Sup (pwr X)(filters_on R X) A0)\<in>pwr X"
      using B17 B18 B32 B9 compactD[of "pwr X" "(filters_on R X)" F] by fastforce
    obtain B35:"A0 \<subseteq> ?A" and B36:"finite A0" and B37:"A0 \<noteq> {}"
      using B33 Fpow_neD by blast
    obtain B38:"A0 \<subseteq> Pow X"
      using B0 B35 by force
    obtain B39:"pord (pwr X) A0"
      by (simp add: B38 pwr_antisym_sub pwr_refl_sub pwr_trans_sub)
    have B40:"\<And>Ai. Ai \<in> A0 \<Longrightarrow> (\<exists>x. x \<in> F \<and> is_least R Ai x)"
    proof-
      fix Ai assume B41:"Ai \<in> A0" 
      obtain B42:"Ai \<subseteq> X" and B43:"pord R Ai"
        by (meson B38 B41 PowD por pord_sub1 subsetD)
      obtain x where B44:"x \<in> F" and B45:"Ai = lcro R X x"
        using B35 B41 by auto
      obtain B46:"is_least R Ai x"
        by (metis B44 B45 B8 is_leastI3 lcroD1)
      then show "(\<exists>x. x \<in> F \<and> is_least R Ai x)"
        using B44 by auto 
    qed
    define S where "S \<equiv> (\<lambda>Ai. THE x. x \<in> F \<and> is_least R Ai x)"
    have B47:"\<And>Ai. Ai \<in> A0 \<Longrightarrow> (S Ai) \<in> F \<and> is_least R Ai (S Ai) \<and> lcro R X (S Ai) = Ai" 
    proof-
      fix Ai assume B48:"Ai \<in> A0" 
      obtain x where B49:"x \<in> F" and B50:"Ai = lcro R X x"
        using B48 B35 by blast
     obtain B51:"Ai \<subseteq> X" and B52:"pord R Ai"
       by (meson B38 B48 PowD por pord_sub1 subsetD)
     obtain B53:"is_least R Ai x"
       by (metis B49 B50 B8 is_leastI3 lcroD1)
     obtain B54:"pord (dual R) Ai"
       by (simp add: B52 refl_dualI)
     have B55:"S Ai = x"
     proof(unfold S_def, rule the_equality)
      show "x \<in> F \<and> is_least R Ai x"
        by (simp add: B49 B53)
      show "\<And>xa. xa \<in> F \<and> is_least R Ai xa \<Longrightarrow> xa = x"
        by (meson B53 B54 greatest_unique)
     qed
     then obtain B56: "(S Ai) \<in>F" and B343:"is_least R Ai (S Ai)"
       by (simp add: B49 B53)
     obtain B57:"lcro R X (S Ai) = Ai"
       using B50 B55 by presburger
     then show "(S Ai) \<in> F \<and> is_least R Ai (S Ai) \<and> lcro R X (S Ai) = Ai"
       by (simp add: B343 B56)
    qed
    then obtain B58:"(S`A0) \<subseteq> F" and B59:"finite (S`A0)"
      using B36 by blast
    then obtain B60:"Inf R X (S`A0) \<in> F"
      by (meson A0 A3 B37 filter_inf_closed3 filters_on_iff image_is_empty lattD4 por)
    then obtain B61:"lcro R X (Inf R X (S`A0)) \<subseteq> F "
      by (meson A3 filters_on_iff is_filterD1 is_ord_clD1 lcroD1 subsetI)
    have B62:"\<And>Ai. Ai \<in> {lcro R X f|f. f \<in>  (S`A0)} \<Longrightarrow> Ai \<in> A0"
      using B47 by force 
    have B63:"\<And>Ai. Ai \<in> A0 \<Longrightarrow>  Ai \<in> {lcro R X f|f. f \<in>  (S`A0)} "
      using B47 by blast 
    have B64:"A0 =  {lcro R X f|f. f \<in>  (S`A0)}"
      using B62 B63 by blast
    have B65:"(S`A0) \<in> Fpow_ne X"
      by (meson B37 B58 B59 B7 Fpow_neI1 image_is_empty subset_trans)
    obtain B66:"lcro R X (Inf R X (S`A0)) = Sup (pwr X) (filters_on R X) A0" 
      using A0 lcro_inter2[of R X "(S`A0)"] B64 B65 por by auto
    then show " (\<exists>x \<in> X.  lcro R X x = F )"
      using B34 B60 B61 B7 powrel8 by blast
  qed
  then show ?thesis
    using B21 by blast
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
  by (meson A0 A1 A2 A3 is_filter_def PowD is_ord_cl_def pwr_mem_iff)

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


lemma filters_on_finite_set:
  assumes fin:"finite X"
  shows "pfilters_on (pwr X) (Pow X) = {lcro (pwr X) (Pow X) A|A. A \<in> Pow_ne X }" (is "?L=?R")
proof-
  have P0:"\<And>F. F \<in> ?L \<Longrightarrow> {} \<notin> F"
    by (simp add: pfilters_on_iff sets_pfilter5)
  have P1:"\<And>F. F \<in> ?L \<Longrightarrow> finite F"
    by (meson fin finite_Pow_iff finite_subset pfilters_on_iff sets_pfilter6)
  have P2:"\<And>F. F \<in> ?L \<Longrightarrow> F \<noteq> {}"
    by (simp add: pfilters_on_iff sets_pfilter1)
  obtain P4:"is_inf_semilattice (pwr X) (Pow X)"
    by (simp add: cinf_sinf clatD2 pow_is_clattice)
  obtain P5:"pord (pwr X) (Pow X)"
    by (simp add: pwr_antisym pwr_refl pwr_trans)
  have P6:"\<And>F. F \<in> ?L \<Longrightarrow> Inf (pwr X) (Pow X) F \<in> F"
  proof-
    fix F assume A0:"F\<in>?L"
    then obtain "finite F" and "F \<subseteq> F" and "F \<noteq> {}"
      by (simp add: P1 P2)
    then show "Inf (pwr X) (Pow X) F \<in> F"
      using P4 P5 A0 filter_inf_closed3 pfilters_on_iff setfilters3 by blast
  qed
  show "?L = ?R"
  proof
    show "?L \<subseteq> ?R"
    proof
      fix F assume A0:"F \<in> ?L"
      then obtain B0:"Inf (pwr X) (Pow X) F \<in>F"
        using P6 by auto
      then obtain B1:"Inf (pwr X) (Pow X) F \<in> Pow_ne X"
        by (metis A0 IntE P0 Pow_neI2 inf.absorb_iff2 pfilters_on_iff sets_pfilter6)
      have B2:"F = lcro (pwr X) (Pow X) (Inf (pwr X) (Pow X) F)"
      proof
        show "F \<subseteq> lcro (pwr X) (Pow X) (Inf (pwr X) (Pow X) F)"
        proof
          fix E assume "E \<in> F"
          then obtain "((Inf (pwr X) (Pow X) F), E)\<in>(pwr X)"
            by (metis A0 Fpow_ne_iff P1 P4 P5 antisym_on_converse empty_iff is_infD1 pfilters_on_iff sets_pfilter6 ssl_fin_sup7 trans_on_converse)
          then show "E \<in> lcro (pwr X) (Pow X) (Inf (pwr X) (Pow X) F)"
            by (simp add: lcroI1 pwr_mem_iff)
        qed
        next
        show "lcro (pwr X) (Pow X) (Inf (pwr X) (Pow X) F) \<subseteq> F"
        proof
          fix E assume "E \<in>  lcro (pwr X) (Pow X) (Inf (pwr X) (Pow X) F)"
          then obtain "E \<in> Pow X" and "((Inf (pwr X) (Pow X) F), E)\<in>(pwr X)"
            by (meson lcroD1)
          then show "E \<in> F"
            by (meson A0 B0 pfilters_on_iff powrel8 sets_pfilter4)
        qed
      qed
      then show "F \<in> ?R"
        using B1 by blast
    qed
    show "?R \<subseteq> ?L"
    proof
      fix F assume A0:"F \<in> ?R"
      then obtain A where B0:"A \<in> Pow_ne X" and B1:"F = lcro (pwr X) (Pow X) A"
        by blast
      then obtain B2:"A \<in> Pow X" and B3:"A \<noteq> {}"
        by (simp add: Pow_neD)
      then obtain B4:"{} \<notin> F"
        by (metis B1 lcroD1 le_bot pwr_mem_iff)
      have pfl:"is_pfilter (pwr X) (Pow X) F"
      proof(rule is_pfilterI1)
        show "is_filter (pwr X) (Pow X) F"
          using B1 B2 P5 lcro_filter by fastforce
        show "Pow X \<noteq> F"
          using B4 by blast
      qed
      then show "F \<in> ?L"
        by (simp add: pfilters_on_iff)
    qed
  qed
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
      using A0 A4 H_def is_pfilterD1[of "pwr X" "Pow X" F] setfilters0[of X F f] by fastforce 
  qed
qed


lemma finer_proper_filter2:
  assumes A0:"is_pfilter (pwr X) (Pow X) F" and A1:"A \<in> Pow X" and A2:"F#{A}"
  defines "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. A \<inter> B \<subseteq> E}" 
  shows "is_pfilter (pwr X) (Pow X) H" and "F \<subseteq> H"
proof-
  obtain A3:"\<forall>B \<in> F. B \<inter> A \<noteq> {}"
    using A2 mesh_def by blast
  show "is_pfilter (pwr X) (Pow X) H"
    using finer_proper_filter[of X F A]  A0 A1 A3 H_def by blast 
  show "F \<subseteq> H"
    using finer_proper_filter[of X F A]  A0 A1 A3 H_def by blast 
qed

lemma principal_ufilter_sets:
  "x \<in> X \<Longrightarrow> is_maximal (pwr (Pow X)) (pfilters_on (pwr X) (Pow X)) (lcro (pwr X) (Pow X) {x})"
proof(rule pmb_filters2)
    show " x \<in> X \<Longrightarrow> is_pfilter (pwr X) (Pow X) (lcro (pwr X) (Pow X) {x})"
      by (simp add: principal_pfilter_sets)
    show "\<And>xa. x \<in> X \<Longrightarrow> xa \<in> Pow X \<Longrightarrow> (xa \<in> lcro (pwr X) (Pow X) {x} \<or> X - xa \<in> lcro (pwr X) (Pow X) {x}) \<and> \<not> (xa \<in> lcro (pwr X) (Pow X) {x} \<and> X - xa \<in> lcro (pwr X) (Pow X) {x})"
      by (simp add: lcro_def pwr_mem_iff)
qed

section GaloisConnections

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

section Grills


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
        by (metis (mono_tags, lifting) B25 PowD calculation is_ord_clE1 pwr_mem_iff)
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
proof
  show "?L \<subseteq> ?R"
  proof
    fix a assume "a \<in> ?L"
    then show "a \<in> ?R"
      unfolding grill_def using assms by(auto simp add:mesh_single_iff)
  qed
  next
  show "?R \<subseteq> ?L"
  proof
    fix a assume "a \<in> ?R"
    then show "a \<in> ?L"
      unfolding grill_def mesh_def using assms by(auto)
  qed
qed


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

lemma lcro_subI1:
  assumes fil:"is_filter R X F" and
          zmem:"z \<in> F"
  shows "(lcro R X z, F) \<in> pwr X"
proof(rule pwr_memI)
  obtain B0:"F \<subseteq> X" and B1:"is_ord_cl X F R"
    using fil is_filterD1 by auto
  show P0:"F \<subseteq> X"
    using B0 by auto
  show P1:"lcro R X z \<subseteq> F"
    using B1 is_ord_clD1[of X F R z] lcroD1[of _ R X z] zmem by blast
  show P2:"lcro R X z \<subseteq> X"
    using P0 P1 by auto
qed

lemma filter_sup_principal_filters:
  assumes A0:"is_lattice R X" and
          A1:"is_greatest R X top" and
          A2:"is_filter R X F" and
          A3:"pord R X"
  shows "F = Sup (pwr X) (filters_on R X) {(lcro R X f)|f. f \<in>F}"
proof-
  from A0 A1 A3 obtain B0:"is_clattice (pwr X) (filters_on R X)" and B1:"compactly_generated (pwr X)(filters_on R X)" 
    using lattice_filters_complete[of X R top] filters_on_lattice_compactgen[of X R top] by blast
  from A1 obtain ne:"X \<noteq> {}"
    using A0 lattD1 by blast
  obtain por1:"pord (pwr X) (filters_on R X)" and por2:"pord (pwr X) ( (Pow X))"
    by (meson Pow_iff filters_on_iff is_filterD1 powrel6 powrel7 pwr_memI refl_def subsetI)
  have B2:"F= Sup (pwr X) (filters_on R X) {k \<in> compact_elements (pwr X) (filters_on R X). (k, F)\<in>pwr X}" 
    using A2 B0 B1 compact_gen1[of "pwr X" "filters_on R X" F] por1 filters_on_iff by blast
  have B3:"\<And>f. f \<in> compact_elements (pwr X) (filters_on R X) \<Longrightarrow> f \<in> {lcro R X x|x. x \<in> X}"
  proof-
    fix f assume C0:"f \<in> compact_elements (pwr X) (filters_on R X)" 
   then obtain "f \<in> filters_on R X" and "is_compact (pwr X) (filters_on R X) f"
     by (simp add: compactD2 compact_elements_mem_iff1)
   then obtain x where "x \<in> X" and "lcro R X x = f"
      using A0 A1 ne A3 principal_filters_compact[of R X top f] by blast
  then show  "f \<in> {lcro R X x|x. x \<in> X}"
    by blast
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
    by (simp add: A2 lcro_subI1)
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

lemma filter_on_set_obtain:
  assumes "\<F> \<in> filters_on (pwr X) (Pow X)"
  obtains A where "A \<in> \<F>"
  using assms filters_onD2 by fastforce


lemma pfilter_on_set_obtain:
  assumes "\<F> \<in> pfilters_on (pwr X) (Pow X)"
  obtains A where "A \<in> \<F>"
  using assms pfilters_on_iff sets_pfilter1 by fastforce

lemma filter_mem_mesh:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); A \<in> \<F>\<rbrakk> \<Longrightarrow> {A}#\<F>"
  by (meson dual_order.refl mesh_def mesh_singleI pfilter_mesh1)

section ConvergenceRelations

lemma ClN_memI1:
  "\<lbrakk>B \<in> Pow X; x \<in> X; {B}#(N``{x})\<rbrakk> \<Longrightarrow> (B, x) \<in> ClN N X"
  by (simp add: ClN_def)

lemma ClN_Im_memI1:
  "\<lbrakk>B \<in> Pow X; x \<in> X; {B}#(N``{x})\<rbrakk> \<Longrightarrow>  x \<in> (ClN N X)``{B}"
  by (simp add: ClN_def)

lemma ClN_memD1:
  "(B, x)\<in>ClN N X \<Longrightarrow> (B \<in> Pow X \<and> x \<in> X \<and> {B}#(N``{x}))"
  by (simp add: ClN_def)

lemma ClN_Im_memD1:
  "x\<in>(ClN N X)``{B} \<Longrightarrow> (B \<in> Pow X \<and> x \<in> X \<and> {B}#(N``{x}))"
  by (simp add: ClN_def)


lemma NCl_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; {A}#(converse Cl)``{x}\<rbrakk> \<Longrightarrow> (x, A) \<in> NCl Cl X"
  by (simp add: NCl_def)

lemma NCl_Im_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; {A}#(converse Cl)``{x}\<rbrakk> \<Longrightarrow> A \<in> (NCl Cl X)``{x}"
  by (simp add: NCl_def)

lemma NCl_memD:
  "(x, A) \<in> NCl Cl X  \<Longrightarrow>(A \<in> Pow X \<and> x \<in> X \<and> {A}#(converse Cl)``{x})"
  by (simp add: NCl_def)

lemma NCl_Im_memD:
  "A \<in> (NCl Cl X)``{x}  \<Longrightarrow>(A \<in> Pow X \<and> x \<in> X \<and> {A}#(converse Cl)``{x})"
  using NCl_memD by force

lemma NAdh_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; (\<And>\<E>. \<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)\<rbrakk> \<Longrightarrow> (x, A)\<in> NAdh Adh X"
  by (simp add: NAdh_def)

lemma NAdh_Im_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; (\<And>\<E>. \<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)\<rbrakk> \<Longrightarrow> A \<in> (NAdh Adh X)``{x}"
  by (simp add: NAdh_def)

lemma NAdh_memD1:
  "(x, A)\<in> NAdh Adh X \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> (\<E>, x) \<in> Adh \<longrightarrow> {A}#\<E>)) "
  by (simp add: NAdh_def)

lemma NAdh_memD2:
  "(x, A)\<in> NAdh Adh X \<Longrightarrow> (\<And>\<E>. \<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X);(\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E> )"
  using NAdh_memD1[of x A Adh X] by presburger

lemma NAdh_Im_memD:
  "A \<in> (NAdh Adh X)``{x} \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> (\<E>, x) \<in> Adh \<longrightarrow> {A}#\<E>))"
  by (simp add: NAdh_def)

lemma AdhN_memI:
  "\<lbrakk>\<E>\<in>pfilters_on (pwr X) (Pow X);x\<in>X;(\<And>A. \<lbrakk>A\<in>Pow X;(x,A)\<in>N\<rbrakk>\<Longrightarrow>{A}#\<E>)\<rbrakk>\<Longrightarrow>(\<E>,x)\<in>AdhN N X"
  by (simp add: AdhN_def)

lemma AdhN_memD:
  "(\<E>,x)\<in>AdhN N X \<Longrightarrow> (\<E>\<in>pfilters_on (pwr X) (Pow X)\<and>x\<in>X\<and>(\<forall>A. A\<in>Pow X \<and> (x,A)\<in>N \<longrightarrow>{A}#\<E>))"
  by (simp add: AdhN_def)

lemma AdhN_Im_memI:
  "\<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> {A}#\<E>)\<rbrakk> \<Longrightarrow> x \<in> (AdhN N X)``{\<E>}"
  by (simp add: AdhN_def)

lemma AdhN_Im_memD:
  "x \<in> (AdhN N X)``{\<E>} \<Longrightarrow> (\<E> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> (x, A) \<in> N \<longrightarrow> {A}#\<E>))"
  by (simp add: AdhN_def)

lemma AdhCl_memI:
"\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl)\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> AdhCl Cl X"
  by (simp add: AdhCl_def)

lemma AdhCl_memD:
  "(\<F>, x) \<in> AdhCl Cl X \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl))"
  by (simp add: AdhCl_def)

lemma AdhCl_Im_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl)\<rbrakk> \<Longrightarrow> x \<in> (AdhCl Cl X)``{\<F>}"
  by (simp add: AdhCl_def)

lemma AdhCl_Im_memD:
  "x \<in> (AdhCl Cl X)``{\<F>} \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl))"
  by (simp add: AdhCl_def)

lemma ClAdh_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> (A, x) \<in> ClAdh Adh X"
  by (simp add: ClAdh_def)

lemma ClAdh_memD:
  "(A, x) \<in> ClAdh Adh X \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Adh))"
  by (simp add: ClAdh_def)

lemma ClAdh_Im_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> x \<in> (ClAdh Adh X)``{A}"
  by (simp add: ClAdh_def)
lemma ClAdh_Im_memD:
  "x \<in> (ClAdh Adh X)``{A} \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Adh))"
  by (simp add: ClAdh_def)

lemma NLim_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; (\<And>\<E>. \<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); (\<E>, x) \<in> Lim\<rbrakk> \<Longrightarrow> A \<in> \<E>)\<rbrakk> \<Longrightarrow> (x, A) \<in> NLim Lim X"
  by (simp add: NLim_def)

lemma NLim_memD:
  "(x, A) \<in> NLim Lim X \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> (\<E>, x) \<in> Lim \<longrightarrow> A \<in> \<E>))"
  by (simp add: NLim_def)

lemma NLim_Im_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; (\<And>\<E>. \<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); (\<E>, x) \<in> Lim\<rbrakk> \<Longrightarrow> A \<in> \<E>)\<rbrakk> \<Longrightarrow> A \<in> (NLim Lim X)``{x}"
  by (simp add: NLim_def)
lemma NLim_Im_memD:
  "A \<in> (NLim Lim X)``{x} \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> (\<E>, x) \<in> Lim \<longrightarrow> A \<in> \<E>))"
  by (simp add: NLim_def)

lemma LimN_memI:
  "\<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> A \<in> \<E>)\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> LimN N X"
  by (simp add: LimN_def)

lemma LimN_memD:
  "(\<E>, x) \<in> LimN N X \<Longrightarrow> (\<E> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A \<in> Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>))"
  by (simp add: LimN_def)

lemma LimCl_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl)\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> LimCl Cl X"
  by (simp add: LimCl_def)

lemma LimCl_memD:
  "(\<F>, x) \<in> LimCl Cl X \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> {A}#\<F> \<longrightarrow> (A, x) \<in> Cl))"
  by (simp add: LimCl_def)

lemma ClLim_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim\<rbrakk> \<Longrightarrow> (A, x) \<in> ClLim Lim X"
  by (simp add: ClLim_def)

lemma ClLim_memD:
  "(A, x) \<in> ClLim Lim X \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim))"
  by (simp add: ClLim_def)

lemma AdhLim_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; \<exists>\<G> \<in> pfilters_on (pwr X) (Pow X). \<G> # \<F> \<and> (\<G>, x) \<in> Lim\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> AdhLim Lim X"
  by (simp add: AdhLim_def)

lemma AdhLim_memD:
  "(\<F>, x) \<in> AdhLim Lim X \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<exists>\<G> \<in> pfilters_on (pwr X) (Pow X). \<G> # \<F> \<and> (\<G>, x) \<in> Lim))"
  by (simp add: AdhLim_def)

lemma LimAdh_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>\<G>. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh)\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> LimAdh Adh X"
  by (simp add: LimAdh_def)

lemma LimAdh_memD:
  "(\<F>, x) \<in> LimAdh Adh X \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters_on (pwr X) (Pow X) \<and> \<G> # \<F> \<longrightarrow> (\<G>, x) \<in> Adh))"
  by (simp add: LimAdh_def)

lemma LimN_Im_memI:
  "\<lbrakk>\<E> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> A \<in> \<E>)\<rbrakk> \<Longrightarrow> x \<in> (LimN N X)``{\<E>}"
  by (simp add: LimN_def)

lemma LimN_Im_memD:
  "x \<in> (LimN N X)``{\<E>} \<Longrightarrow> (\<E> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A \<in> Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>))"
  by (simp add: LimN_def)

lemma LimCl_Im_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl)\<rbrakk> \<Longrightarrow> x \<in> (LimCl Cl X)``{\<F>}"
  by (simp add: LimCl_def)

lemma LimCl_Im_memD:
  "x \<in> (LimCl Cl X)``{\<F>} \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> {A}#\<F> \<longrightarrow> (A, x) \<in> Cl))"
  by (simp add: LimCl_def)

lemma ClLim_Im_memI:
  "\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim\<rbrakk> \<Longrightarrow> x \<in> (ClLim Lim X)``{A}"
  by (simp add: ClLim_def)

lemma ClLim_Im_memD:
  "x \<in> (ClLim Lim X)``{A} \<Longrightarrow> (A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim))"
  by (simp add: ClLim_def)

lemma AdhLim_Im_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; \<exists>\<G> \<in> pfilters_on (pwr X) (Pow X). \<G> # \<F> \<and> (\<G>, x) \<in> Lim\<rbrakk> \<Longrightarrow> x \<in> (AdhLim Lim X)``{\<F>}"
  by (simp add: AdhLim_def)

lemma AdhLim_Im_memD:
  "x \<in> (AdhLim Lim X)``{\<F>} \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<exists>\<G> \<in> pfilters_on (pwr X) (Pow X). \<G> # \<F> \<and> (\<G>, x) \<in> Lim))"
  by (simp add: AdhLim_def)

lemma LimAdh_Im_memI:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X; (\<And>\<G>. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh)\<rbrakk> \<Longrightarrow> x \<in> (LimAdh Adh X)``{\<F>}"
  by (simp add: LimAdh_def)

lemma LimAdh_Im_memD:
  "x \<in> (LimAdh Adh X)``{\<F>} \<Longrightarrow> (\<F> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters_on (pwr X) (Pow X) \<and> \<G> # \<F> \<longrightarrow> (\<G>, x) \<in> Adh))"
  by (simp add: LimAdh_def)

lemma centeredI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (lcro (pwr X) (Pow X) {x}, x) \<in> q) \<Longrightarrow> centered X q"
  by (simp add: centered_def)

lemma centeredD1:
  "centered X q \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (lcro (pwr X) (Pow X) {x}, x)\<in>q)"
  by (simp add: centered_def)

lemma centeredD2:
  "\<lbrakk>centered X q;x\<in>X\<rbrakk> \<Longrightarrow>(converse q)``{x} \<noteq> {}"
  using centered_def by force

lemma isoconvI1:
  "(\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> q;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q) \<Longrightarrow> isoconv X q"
  using isoconv_def by blast 

lemma isoconvD1:
  "isoconv X q \<Longrightarrow> (\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> q;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q)"
  by(simp add:isoconv_def)

lemma isoconvI2:
  "(\<And>\<G> \<F> x. \<lbrakk>is_pfilter (pwr X) (Pow X) \<G>; (\<F>, x) \<in> q;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q) \<Longrightarrow> isoconv X q"
  using isoconv_def pfilters_on_iff by blast

lemma isoconvI3:
  "(\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> q;  (\<F>, \<G>)\<in>pwr (Pow X)\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q) \<Longrightarrow> isoconv X q"
  by (simp add: isoconvI2 pfilters_on_iff pwr_mem_iff sets_pfilter6)

lemma onpconvI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q) \<Longrightarrow> onpconv X q "
  by (simp add: onpconv_def) 

lemma onpconvD1:
  "onpconv X q \<Longrightarrow>(\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q)"
  by (simp add: onpconv_def) 

lemma isconvsI1:
  "(\<And>x \<E>. (\<E>, x) \<in> q \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))) \<Longrightarrow> isconvs X q"
  by (simp add: isconvs_def)

lemma isgconvI2:
  "(\<And>x \<E>. (\<E>, x) \<in> q \<Longrightarrow> x \<in> X \<and>  (is_pfilter (pwr X) (Pow X) \<E> )) \<Longrightarrow> isconvs X q"
  by (simp add: isconvsI1 pfilters_on_iff)

lemma isgconvD1:
  "isconvs X q \<Longrightarrow> (\<And>x \<E>. (\<E>, x) \<in> q \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X)))"
  by (simp add: isconvs_def)

lemma ispsmapD1:
  "ispsmap X N \<Longrightarrow> (\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X)"
  by (simp add: ispsmap_def)

lemma ispsmapD2:
  "ispsmap X N \<Longrightarrow>  (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  by (simp add: ispsmap_def)

lemma ispsmapI1:
  "(\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X) \<Longrightarrow> ispsmap X N"
  using ispsmap_def by blast

lemma isspmapD1:
  "isspmap X Cl \<Longrightarrow>  (\<And>x V. (V, x) \<in> Cl \<Longrightarrow> x \<in> X \<and> V \<in> Pow X)"
  by (simp add: isspmap_def)

lemma isspmapD2:
  "isspmap X Cl \<Longrightarrow>  (V, x) \<in> Cl \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  by (simp add: isspmap_def)

lemma isspmapI1:
  "(\<And>x V. (V, x) \<in> Cl \<Longrightarrow> x \<in> X \<and> V \<in> Pow X) \<Longrightarrow> isspmap X Cl"
  by (simp add: isspmap_def)

lemma ispsmapI2:
  "isspmap X Cl \<Longrightarrow> ispsmap X (dual Cl)" 
  using ispsmapI1[of "dual Cl" X] isspmapD1[of X Cl] by simp

lemma ispmapI2:
  "ispsmap X N \<Longrightarrow> isspmap X (dual N)" 
  using isspmapI1[of "dual N" X] ispsmapD1[of X N] by simp


lemma isspmapI1:
  "Cl \<subseteq> (X \<times> (Pow X)) \<Longrightarrow> ispsmap X Cl"

lemma spmap_isoD1:
  assumes A0:"isspmap X Cl" and
          A1:"iso_spmap X Cl" 
  shows "is_ord_cl (Pow X) ((converse Cl)``{x}) (pwr X)"
proof(rule is_ord_clI1)
  fix A B assume A2:"B \<in> Pow X" and A3:" A \<in> ((converse Cl)``{x})" and A4:"(A, B)\<in>pwr X"
  then obtain B0:"(A, x) \<in> Cl" and B1:"A \<in> Pow X" and B2:"A \<subseteq> B"
    by (simp add: pwr_memD)
  then obtain B3:"Cl``{A} \<subseteq> Cl``{B}"
    using A1 A2 by presburger
  then obtain B4:"(B, x) \<in> Cl"
    using B0 by blast  
  then show "B \<in> ((converse Cl)``{x})" 
    by simp
qed


lemma psmap_isoD1:
  "\<lbrakk>ispsmap X N; "
  assumes A0:"isspmap X Cl" and
          A1:"iso_spmap X Cl" 
  shows "is_ord_cl (Pow X) ((converse Cl)``{x}) (pwr X)"



section \<open>Between Convergence Relations\<close>


lemma contrapos_sub:
  assumes A0:"A \<subseteq> X" and A1:"B \<subseteq> X" and A2:"\<And>x. \<lbrakk>x \<in> X;x \<notin> B\<rbrakk> \<Longrightarrow> x \<notin> A"
  shows "A \<subseteq> B"
  using A0 A2 by blast

lemma Cl_to_Nh:
  assumes xmem:"x \<in> X"
  shows Cl_to_Nh1:"(NCl Cl X)``{x} = grill (Pow X) ((converse Cl)``{x})" and
        Cl_to_Nh2:"\<And>A. (x, A) \<in>(NCl Cl X) \<longleftrightarrow> A \<in>  grill (Pow X) ((converse Cl)``{x})"
proof-
  show P0:"(NCl Cl X)``{x} = grill (Pow X) ((converse Cl)``{x})" 
    using assms unfolding NCl_def grill_def by fastforce
  show P1:"\<And>A. (x, A) \<in>(NCl Cl X) \<longleftrightarrow> A \<in>  grill (Pow X) ((converse Cl)``{x})"
    using P0 by auto
qed

lemma Nh_to_Cl:
  assumes xmem:"x \<in> X"
  shows Nh_to_Cl1:"(converse (ClN N X))``{x} = grill (Pow X) (N``{x})" and
        Nh_to_Cl2:"\<And>A. (A, x) \<in> (ClN N X) \<longleftrightarrow>  A \<in> grill (Pow X) (N``{x})"
proof-
  show P0:"(converse (ClN N X))``{x} = grill (Pow X) (N``{x})"
     using assms unfolding ClN_def grill_def by auto
  show P1:"\<And>A. (A, x) \<in> (ClN N X) \<longleftrightarrow>  A \<in> grill (Pow X) (N``{x})"
    using P0 by auto
qed


lemma Nh_to_Adh:
  assumes A0:"ispsmap X N"
  shows Nh_to_Adh1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow> x\<in>(AdhN N X)``{\<E>} \<longleftrightarrow> (N``{x})#\<E> "  and
        Nh_to_Adh2:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow> (\<E>, x)\<in>(AdhN N X) \<longleftrightarrow> (N``{x})#\<E> " 
proof-
  show P0:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow> x\<in>(AdhN N X)``{\<E>} \<longleftrightarrow> (N``{x})#\<E> " 
    using A0 ispsmapD1[of X N] unfolding AdhN_def mesh_def by auto
  show P1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow> (\<E>, x)\<in>(AdhN N X) \<longleftrightarrow> (N``{x})#\<E> "
    using P0 by force
qed

lemma Adh_to_Nh:
  assumes A0:"isconvs X Adh" 
  shows "\<And>x. \<lbrakk>(converse Adh)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> (NAdh Adh X)``{x} = \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
proof-
  let ?F="pfilters_on (pwr X) (Pow X)"
  fix x assume A1:"x \<in> X" and A2:"(converse Adh)``{x} \<noteq> {}"
  show "(NAdh Adh X)``{x} = \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"(is "?L=?R") 
  proof
    show "?L \<subseteq> ?R"
      using A1 A2  A0 isgconvD1[of X Adh] unfolding NAdh_def grill_def by blast
    next 
    show "?R \<subseteq> ?L"  
    proof-
      let ?S="{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
      obtain B0:"?S \<noteq> {}" 
        using A2 by blast 
      obtain B1:"?S \<subseteq> (Pow (Pow X))"
        using grill_space by blast 
      obtain B2:"?R \<subseteq> Pow X" and B3:"?L \<subseteq> Pow X" 
        using B0 B1 unfolding NAdh_def by blast 
      then show ?thesis
      proof(rule contrapos_sub)
        show "\<And>z. \<lbrakk>z \<in> Pow X; z \<notin>?L\<rbrakk>\<Longrightarrow>z \<notin> ?R"
        proof-
          fix E assume A3:"E \<in> Pow X" and A4:"E \<notin> ?L"
          then show "E\<notin>?R"
            using A1 B0 B1 B2 unfolding NAdh_def grill_def by blast
        qed
      qed
    qed  
  qed
qed


lemma  Nh_to_Lim:
  assumes A0:"ispsmap X N"
  shows Nh_to_Lim1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow>x \<in> (LimN N X)``{\<E>} \<longleftrightarrow> (N``{x}) \<subseteq> \<E>" and
        Nh_to_Lim2:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow>(\<E>, x) \<in> (LimN N X) \<longleftrightarrow> (N``{x}) \<subseteq> \<E>"
proof-
  show P0:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow>x \<in> (LimN N X)``{\<E>} \<longleftrightarrow> (N``{x}) \<subseteq> \<E>" 
    using A0 ispsmapD1[of X N] unfolding LimN_def mesh_def by auto
  show P1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters_on (pwr X) (Pow X)\<rbrakk> \<Longrightarrow>(\<E>, x) \<in> (LimN N X) \<longleftrightarrow> (N``{x}) \<subseteq> \<E>"
    using P0 by auto
qed

lemma Lim_to_Nh: 
  assumes A0:"isconvs X Lim" 
  shows Lim_to_Nh1:"\<And>x. \<lbrakk>(converse Lim)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow>(NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim})" and
        Lim_to_Nh2:"centered X Lim \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim}))"
proof-
  show P0:"\<And>x. \<lbrakk>(converse Lim)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow>(NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim})" 
  proof-
    fix x assume  A1:"(converse Lim)``{x} \<noteq> {}" and A2:"x \<in> X"
    let ?F="pfilters_on (pwr X) (Pow X)"
    let ?L="(NLim Lim X)``{x}" let  ?R= "(\<Inter>{\<E>. (\<E>, x) \<in> Lim})" 
    have LR:"?L \<subseteq> ?R" 
       using A0 A1 A2 isgconvD1[of X Lim] unfolding NLim_def by blast  
    have RL:"?R \<subseteq> ?L" 
    proof-
      have B0:"\<And>A. \<lbrakk>A \<in> Pow X; A \<notin> ?L\<rbrakk> \<Longrightarrow> A \<notin> ?R"
        using A0 A1 A2 unfolding NLim_def by blast
      have B1:"?L \<subseteq> Pow X" 
        using A0 A1 A2 unfolding NLim_def by blast
      obtain ne:"{\<E>. (\<E>, x) \<in> Lim} \<noteq> {}"
        using A1 by blast 
      then obtain B2:"?R \<subseteq> Pow X" 
        using A0  A1 A2 isgconvD1[of X Lim] pfilters_on_iff sets_pfilter6 by fastforce 
      from B1 B2 B0 show ?thesis  
        using contrapos_sub[of ?R "Pow X" ?L]  by fastforce
    qed
    from LR RL show "?L=?R"
      by blast
  qed
  show P1:"centered X Lim \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim}))"
  proof-
    assume cen:"centered X Lim"
    then show "(\<And>x. x \<in> X \<Longrightarrow> (NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim}))"
      by (simp add: P0 centeredD2)
  qed
qed


lemma Lim_to_Nh3: 
  assumes A0:"isconvs X Lim"
  shows "\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (x, V) \<in> (NLim Lim X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X) "
proof-
  fix x V assume vmem:"V \<in> Pow X" and xmem:"x \<in> X"
  have lfil:"\<And>\<F>. \<F> \<in> converse (Lim)``{x} \<Longrightarrow>  \<F>  \<in> Pow (Pow X) \<and> is_ord_cl (Pow X)  \<F> (pwr X)"
    by (meson Image_singleton_iff PowI assms converse.cases is_filterD1 isgconvD1 pfilters_onD1)
  have B0:"(x, V) \<in> (NLim Lim X) \<longleftrightarrow> (\<forall>\<F> \<in> converse (Lim)``{x}. V \<in> \<F>)" 
    using A0 xmem vmem isgconvD1[of X Lim] unfolding NLim_def by  blast
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
    using vmem xmem A0 isgconvD1[of X Lim] unfolding ClLim_def by blast
  finally show "(x, V) \<in> (NLim Lim X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X)" 
    by blast
qed




lemma Cl_to_Adh:
  assumes A0:"isspmap X Cl" 
  shows "\<And>\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<Longrightarrow> (AdhCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}" 
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  show " (AdhCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}" (is "?L=?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix x assume L0:"x \<in> (AdhCl Cl X)``{\<F>}"
      then obtain B0:" x \<in> X" and B1:"\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
        using AdhCl_memD by force
      also obtain B2:"\<And>A. A \<in> \<F> \<Longrightarrow> A \<in> Pow X"
        using A1 pfilters_on_iff sets_pfilter6 by blast
      then obtain "\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Cl``{A}"
        by (simp add: B1)
      then show "x \<in> \<Inter> {Cl `` {A} |A. A \<in> \<F>}"
        by blast
    qed
  next
    show "?R \<subseteq> ?L"
    proof
      fix x assume R0:"x \<in> \<Inter> {Cl `` {A} |A. A \<in> \<F>}"
      then obtain B0:"\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Cl``{A}"
        by blast
      obtain A where "A \<in> \<F>"
        using A1 pfilter_on_set_obtain by blast
      then obtain B1:"x \<in> X"
        using A0 B0 A1 isspmapD1[of X Cl] by blast
      also obtain B2:"\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
        using B0 by auto
      then show "x \<in> (AdhCl Cl X)``{\<F>}"
        unfolding AdhCl_def using A1 calculation by blast
    qed
  qed
qed

lemma Adh_to_Cl:
  assumes A0:"isconvs X Adh" 
  shows "\<And>A. A \<in> Pow X \<Longrightarrow> (ClAdh Adh X)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> A \<in> \<F>}"
proof-
  fix A assume A1:"A \<in> Pow X"
  from A0 obtain B0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"
    using isgconvD1[of X Adh] by auto
  show "(ClAdh Adh X)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> A \<in> \<F>}"
    unfolding ClAdh_def using A1 B0 by auto
qed


lemma Cl_to_Lim:
  assumes A0:"isspmap X Cl"     
  shows "\<And>\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<Longrightarrow>(LimCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A}#\<F>}"
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  show "(LimCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A}#\<F>}" (is "?L=?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix x assume L0:"x \<in> ?L"
      obtain "\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
        using L0 LimCl_memD by fastforce
      then show "x \<in> ?R"
        by blast
    qed
  next
    show "?R \<subseteq> ?L"
    proof
      fix x assume R0:"x \<in> ?R"
      obtain A where B0:"A \<in> \<F>"
        using A1 pfilter_on_set_obtain by auto
      then obtain B1:"A \<in> Pow X" and B2:"{A}#\<F>"
        using A1 filter_mem_mesh pfilters_on_def sets_pfilter6 by fastforce
      then obtain B3:"(A, x)\<in>Cl"
        using R0 by auto
      then obtain B4:"x \<in> X"
        using A0 isspmapD2[of X Cl A x] by blast
      also obtain "\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl" and "\<F> \<in> pfilters_on (pwr X) (Pow X)"
        using R0 A1 by auto
      then show "x \<in> ?L"
        using calculation LimCl_Im_memI[of \<F> X x] by blast
    qed
  qed
qed
  
lemma onpconvD2:
  assumes A0:"onpconv X q" and
          A1:"centered X q" and
          A2:"isconvs X q"
  shows "\<And>x. x \<in> X \<Longrightarrow> ((NLim q X)``{x}, x)\<in>q"
proof-
  fix x assume xmem:"x \<in> X"
  obtain A3:"(converse q)``{x} \<noteq> {}"
    using A1 centeredD2 xmem by fastforce
  have "(NLim q X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> q})"
    by (simp add: A1 A2 Lim_to_Nh2 xmem)
  then show "((NLim q X)``{x}, x)\<in>q"
    using A0 onpconvD1 xmem by fastforce
qed


lemma Lim_to_Cl: 
  assumes A0:"isconvs X Lim"
  shows "\<And>A. \<lbrakk>A \<in> Pow X\<rbrakk> \<Longrightarrow>(ClLim Lim X)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> {A}#\<F>}"
proof-
  fix A assume A1:"A \<in> Pow X"
  from A0 obtain B0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"
    by (simp add: isgconvD1)
  show "(ClLim Lim X)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> {A}#\<F>}"
     unfolding ClLim_def using A1 B0 by auto
qed

lemma Lim_to_Adh: 
  assumes A0:"isconvs X Lim"
  shows "\<And>\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<Longrightarrow> (AdhLim Lim X)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  obtain B0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" 
    using A0 isgconvD1[of X Lim] by blast
  then show "(AdhLim Lim X)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
    unfolding AdhLim_def using B0 A1 by auto
qed


lemma Adh_to_Lim: 
  assumes A0:"isconvs X Adh"
  shows "\<And>\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<Longrightarrow> (LimAdh Adh X)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  obtain B0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" 
    using A0 isgconvD1[of X Adh] by blast
  then show "(LimAdh Adh X)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
    unfolding LimAdh_def using B0 A1 by(auto, metis ImageE pfilter_mesh1 subset_refl)
qed

lemma ClNh_if_iso_cl1:
  assumes A0:"isspmap X Cl" and
          A1:"iso_spmap X Cl"
  shows ClNh_if_iso_cl1:"\<And>x A.  \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))" and
        ClNh_if_iso_cl2:"\<And>x A.  \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow>(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((NCl Cl X)``{x})" and
        ClNh_if_iso_cl3:"\<And>x A.  \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl" 
proof-
  show P0:"\<And>x A.  \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))"
    by (simp add: Cl_to_Nh1)
  show P1:"\<And>x A.  \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow>(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((NCl Cl X)``{x})"
    by (simp add: Nh_to_Cl1) 
  show P2:"\<And>x A.  \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow>(A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl"
  proof-
    fix x A assume A2:"x \<in> X" and aA3mem:"A \<in> Pow X"
    obtain B0:"(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((grill (Pow X) ((converse Cl)``{x})))"
      by (simp add: A2 Cl_to_Nh1 Nh_to_Cl1) 
    have B1:"\<And>E F. \<lbrakk>F \<in> Pow X; E\<in>((converse Cl)``{x}); E\<subseteq>F\<rbrakk> \<Longrightarrow> F\<in>((converse Cl)``{x})"
    proof-
      fix E F assume "F \<in> Pow X" and "E\<in>((converse Cl)``{x})" and "E\<subseteq>F"
        then show "F\<in>((converse Cl)``{x})"
      using A0 A1 spmap_isoD1[of X Cl F E x] by fastforce
    qed
    then obtain B4:"is_ord_cl (Pow X) ((converse Cl)``{x}) (pwr X)"
      by (meson is_ord_cl_def powrel8) 
    obtain B5:"(dual Cl `` {x}) \<in> Pow (Pow X)"
      using A0 isspmapD2[of X Cl]   by blast 
    have B6:"grill (Pow X) ((grill (Pow X) ((converse Cl)``{x}))) = (converse Cl)``{x}" 
        using B4  B5 double_grill21[of "(converse Cl)``{x}" X] by fastforce 
    then obtain B7:"(x, A) \<in> (converse (ClN (NCl Cl X) X)) \<longleftrightarrow> (x, A) \<in> converse Cl"
      using B0 by blast  
    then show "(A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl" 
      by simp
  qed
qed


lemma ClNh_if_iso_cl2:
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"  and  
          upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NCl (ClN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  have ordcl:"is_ord_cl (Pow X) (N``{x}) (pwr X)"        
    using is_ord_cl_def[of "Pow X" "N``{x}" "pwr X"] powrel8[of _ _ X] Image_singleton_iff[of _ N x] upcl[of x] by meson
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
      using Nhoods_to_Lim1_alt[of x X Lim]  centeredI1[of X Lim]  centered is_limit xmem by presburger
    also have B2:"... \<subseteq> \<F>" 
      unfolding NLim_def using B1 B0 L is_limit  by blast
    finally show "(\<F>, x) \<in> Lim" 
      using upclosed smallest pfil by blast 
  next
    assume R:"(\<F>, x) \<in> Lim" then show "?L" 
    unfolding LimN_def NLim_def using pfil xmem by auto
  qed
qed


section \<open>Membership of Convergence Relations\<close>
lemma Nhoods_to_Adh0:
  assumes A0:"\<E> \<in> pfilters_on (pwr X) (Pow X)" and 
          A1:"x \<in> X" and 
          A2:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  shows "x \<in> (AdhN N X)``{\<E>} \<longleftrightarrow> (N``{x})#\<E> " 
  using assms unfolding AdhN_def mesh_def by auto

lemma Nhoods_to_Adh1a: 
  assumes A0:"x \<in> X" and
          A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in>pfilters_on (pwr X) (Pow X)" and 
          A2:"Adh \<noteq> {}"
  shows "(NAdh Adh X)``{x} \<subseteq> \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
  unfolding NAdh_def grill_def mesh_def using assms by blast
  

lemma Cl_to_Nhoods1:
  assumes A0:"x \<in> X" 
  shows "(NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))"
  unfolding NCl_def grill_def using assms by auto

lemma Cl_to_Nhoods2:
    assumes A0:"x \<in> X" 
    shows "(converse (ClN N X))``{x} = grill (Pow X) (N``{x})"
    unfolding ClN_def grill_def using assms by auto
  
lemma Nhoods_to_Adh1b: 
  assumes A0:"x \<in> X" and
          A1:"A \<in> Pow X" and 
          A2:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and
          A3:"Adh \<noteq> {}" and
          A4:"(x, A) \<in> (NAdh Adh X)"
  shows " (\<And>\<E>. \<lbrakk>\<E> \<in> Pow (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)"
proof-
  fix \<E> assume A5:"\<E> \<in> Pow (Pow X)" and A6:"(\<E>, x) \<in> Adh"
  show "{A}#\<E>"
    using assms A6 unfolding NAdh_def by blast
qed

  
lemma Nhoods_to_Adh1c: 
  assumes A0:"x \<in> X" and
          A1:"A \<in> Pow X" and
          A2:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> Pow (Pow X)" and 
          A3:"Adh \<noteq> {}" and
          A4:"(\<And>\<E>. \<lbrakk>\<E> \<in> Pow (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)"
  shows "(x, A) \<in> (NAdh Adh X)"
  unfolding NAdh_def mesh_def using assms by(simp add:mesh_def)

lemma Nhoods_to_Adh1d: 
  assumes A0:"x \<in> X" and 
          A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and 
          A2:"Adh \<noteq> {}"
  shows "\<And>E.  \<lbrakk>E \<in> Pow X; E \<notin> (NAdh Adh X)``{x}\<rbrakk> \<Longrightarrow> E \<notin>  \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
proof-
  fix E assume A3:"E \<in> Pow X" and A4:"E \<notin> (NAdh Adh X)``{x}"
  then show "E\<notin>  \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
    unfolding NAdh_def grill_def mesh_def using assms  by blast
qed

lemma Nhoods_to_Adh1: 
  assumes A0:"x \<in> X" and 
          A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in>pfilters_on (pwr X) (Pow X)" and 
          A2:"Adh \<noteq> {}" and 
          A3:"(converse Adh)``{x} \<noteq> {}"
  shows "(NAdh Adh X)``{x} = \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" using assms Nhoods_to_Adh1a[of x X Adh] by auto
next
  show "?R \<subseteq> ?L"
  proof-
    obtain B0:"{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh} \<noteq> {}" 
      using A3 by blast 
    obtain B1:"{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh} \<subseteq> (Pow (Pow X))"
      using grill_space by blast 
    obtain B2:"?R \<subseteq> Pow X"
      using B0 B1 by auto
    obtain B3:"?L \<subseteq> Pow X" 
      unfolding NAdh_def by blast
    show ?thesis
    proof(rule contrapos_sub)
      show "?R \<subseteq> Pow X"
        using B2 by blast
      show "?L \<subseteq> Pow X"
        using B3 by auto
      show "\<And>z. \<lbrakk>z \<in> Pow X; z \<notin>?L\<rbrakk>\<Longrightarrow>z \<notin> ?R"
        using A0 A1 A2 Nhoods_to_Adh1d[of x X Adh] by presburger
    qed
  qed
qed
 
lemma Nhoods_to_Lim0:
  assumes A0:"\<E> \<in>pfilters_on (pwr X) (Pow X)" and
          A1:"x \<in> X" and
          A2:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  shows "x \<in> (LimN N X)``{\<E>} \<longleftrightarrow> (N``{x}) \<subseteq> \<E> " 
  unfolding LimN_def mesh_def using assms by auto


lemma Nhoods_to_Lim1: 
  assumes A0:"x \<in> X" and
          A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and
          A3:"(converse Lim)``{x} \<noteq> {}"
  shows "(NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim})" (is "?L = ?R")
proof 
  show "?L \<subseteq> ?R" 
    unfolding NLim_def using assms by(auto)
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



lemma Nhoods_to_Lim1_alt: 
  assumes A0:"x \<in> X" and
          A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and
          A2:"centered X Lim"
  shows "(NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim})" 
proof-
  from A0 A2 obtain "(converse Lim)``{x} \<noteq> {}"
    unfolding centered_def by blast
  then show ?thesis
    using A0 A1 Nhoods_to_Lim1[of x X Lim] by presburger
qed

lemma Nhoods_to_Lim1_via_cl: 
  assumes A0:"x \<in> X" and 
          A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)"  
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

lemma Nhoods_to_Lim1_via_cl2:
  assumes con:"isconvs X q" and xmen:"x \<in> X"
  shows nhl1:"\<And>V. V \<in> Pow X \<Longrightarrow> (x, V) \<in> (NLim q X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim q X)" and
        nhl2:"\<And>V. V \<in> Pow X \<Longrightarrow> V \<in> (NLim q X)``{x} \<longleftrightarrow>  x \<notin> (ClLim q X)``{X-V}" and
        nhl3:"\<And>V. V \<in> Pow X \<Longrightarrow> V \<in> (NLim q X)``{x} \<longleftrightarrow> x \<in> X-((ClLim q X)``{X-V})"
proof-
  obtain A1:"\<And>x \<E>. (\<E>, x) \<in>q \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)"
    using con isconvs_def by fastforce  
  show P0:"\<And>V. V \<in> Pow X \<Longrightarrow> (x, V) \<in> (NLim q X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim q X)"
    by (simp add: A1 Nhoods_to_Lim1_via_cl xmen) 
  show P1:"\<And>V. V \<in> Pow X \<Longrightarrow> V \<in> (NLim q X)``{x} \<longleftrightarrow>  x \<notin> (ClLim q X)``{X-V}"
    by (simp add: P0)
  show P2:"\<And>V. V \<in> Pow X \<Longrightarrow> V \<in> (NLim q X)``{x} \<longleftrightarrow> x \<in> X-((ClLim q X)``{X-V})"
    by (simp add: P0 xmen)
qed


lemma Cl_to_Adh1:
  assumes A0:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X" and 
          A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(AdhCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}" (is "?L=?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x assume L0:"x \<in> (AdhCl Cl X)``{\<F>}"
    then obtain B0:" x \<in> X" and B1:"\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
      using AdhCl_memD by force
    also obtain B2:"\<And>A. A \<in> \<F> \<Longrightarrow> A \<in> Pow X"
      using A1 pfilters_on_iff sets_pfilter6 by blast
    then obtain "\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Cl``{A}"
      by (simp add: B1)
    then show "x \<in> \<Inter> {Cl `` {A} |A. A \<in> \<F>}"
      by blast
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix x assume R0:"x \<in> \<Inter> {Cl `` {A} |A. A \<in> \<F>}"
    then obtain B0:"\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Cl``{A}"
      by blast
    obtain A where "A \<in> \<F>"
      using A1 pfilter_on_set_obtain by blast
    then obtain B1:"x \<in> X"
      using A0 B0 by blast
    also obtain B2:"\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
      using B0 by auto
    then show "x \<in> (AdhCl Cl X)``{\<F>}"
      unfolding AdhCl_def using A1 calculation by blast
  qed
qed


lemma Adh_to_Cl:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" and
          A1:"A \<in> Pow X"
  shows "(ClAdh Adh X)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> A \<in> \<F>}"
  unfolding ClAdh_def using assms by auto
   
  
lemma Cl_to_Lim1:
  assumes A0:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X" and
          A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(LimCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A}#\<F>}"
(is "?L=?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x assume L0:"x \<in> ?L"
    obtain "\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
      using L0 LimCl_memD by fastforce
    then show "x \<in> ?R"
      by blast
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix x assume R0:"x \<in> ?R"
    obtain A where B0:"A \<in> \<F>"
      using A1 pfilter_on_set_obtain by auto
    then obtain B1:"A \<in> Pow X" and B2:"{A}#\<F>"
      using A1 filter_mem_mesh pfilters_on_def sets_pfilter6 by fastforce
    then obtain B3:"(A, x)\<in>Cl"
      using R0 by auto
    then obtain B4:"x \<in> X"
      by (simp add: A0)
    also obtain "\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl" and "\<F> \<in> pfilters_on (pwr X) (Pow X)"
      using R0 A1 by auto
    then show "x \<in> ?L"
      using calculation LimCl_Im_memI[of \<F> X x] by blast
  qed
qed

  

lemma onpconvD2:
  assumes A0:"onpconv X q" and
          A1:"centered X q" and
          A2:"isconvs X q"
  shows "\<And>x. x \<in> X \<Longrightarrow> ((NLim q X)``{x}, x)\<in>q"
proof-
  fix x assume xmem:"x \<in> X"
  obtain A3:"(converse q)``{x} \<noteq> {}"
    using A1 centeredD2 xmem by fastforce
  have "(NLim q X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> q})"
    using A0 A2 A3 xmem Nhoods_to_Lim1[of x X q] unfolding isconvs_def by fastforce
  then show "((NLim q X)``{x}, x)\<in>q"
    using A0 onpconvD1 xmem by fastforce
qed

    
  
lemma Cl_to_Lim2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" and 
          A1:"A \<in> Pow X"
  shows "(ClLim Lim X)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> {A}#\<F>}"
  unfolding ClLim_def using assms by(auto)

lemma Adh_to_Lim1:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" and 
          A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(AdhLim Lim X)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
  unfolding AdhLim_def using assms by(auto)


lemma Adh_to_Lim2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" and
          A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(LimAdh Adh X)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
  unfolding LimAdh_def using assms by(auto,metis ImageE pfilter_mesh1 subset_refl)

lemma cl_nh_mono1:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  
          iso:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}" 
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
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"  and  
          upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NCl (ClN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  have ordcl:"is_ord_cl (Pow X) (N``{x}) (pwr X)"        
    using is_ord_cl_def[of "Pow X" "N``{x}" "pwr X"] powrel8[of _ _ X] Image_singleton_iff[of _ N x] upcl[of x] by meson
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
      using Nhoods_to_Lim1_alt[of x X Lim]  centeredI1[of X Lim]  centered is_limit xmem by presburger
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
    by (metis A0 A1 converseI is_greatestI3 lcroD1)
qed


lemma lorc_set_pfilter:
  assumes A0:"A \<in> Pow X" and A1:"A \<noteq> {}" 
  shows "is_pfilter (pwr X) (Pow X) (lcro (pwr X) (Pow X) A)"
proof(rule is_pfilterI1)
  show "is_filter (pwr X) (Pow X) (lcro (pwr X) (Pow X) A)"
    using A0 lcro_filter[of "Pow X" "pwr X" A] pwr_antisym pwr_refl pwr_trans by blast 
  show "Pow X \<noteq> lcro (pwr X) (Pow X) A"
    by (metis A1 Pow_bottom lcroD1 pwr_mem_iff subset_empty)
qed

lemma adh_nh_mono2:
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X \<and> V \<noteq> {}"  and 
          upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" and
          ntr:"\<And>x. x \<in> X \<Longrightarrow> N``{x} \<noteq> {}"
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  let ?PF="pfilters_on (pwr X) (Pow X)"
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X" 
  have "(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (\<forall>\<F> \<in> ?PF. (\<F>, x) \<in> (AdhN N X) \<longrightarrow> {A}#\<F>)"
    unfolding NAdh_def using amem xmem by blast
  also have "... \<longleftrightarrow>  (\<forall>\<F> \<in>?PF. (\<forall>V \<in> Pow X. (x, V) \<in> N \<longrightarrow> {V}#\<F>) \<longrightarrow> {A}#\<F>)"
    unfolding AdhN_def using amem xmem by auto
  also have "... \<longleftrightarrow> (\<forall>\<F> \<in> ?PF. (N``{x})#\<F> \<longrightarrow> {A}#\<F>)" (is "?L \<longleftrightarrow> ?R")
  proof
    assume L0:?L
    have L1:"\<And>\<F>. \<lbrakk>\<F> \<in> ?PF;(N``{x})#\<F>\<rbrakk> \<Longrightarrow> {A}#\<F>"
    proof-
      fix \<F> assume L2:"\<F> \<in> ?PF" and L3:"(N``{x})#\<F>"
      then obtain L4:"x \<in> (AdhN N X)``{\<F>}"
        using is_nh xmem Nhoods_to_Adh0[of \<F> X x] by presburger
      then show "{A}#\<F>"
        using L0 AdhN_Im_memD[of x N X \<F>] by fastforce
    qed
    then show ?R
      by blast
    next
    assume R0:?R
    have R1:"\<And>\<F>.  \<lbrakk>\<F> \<in> ?PF;  (\<forall>V \<in> Pow X. (x, V) \<in> N \<longrightarrow> {V}#\<F>)\<rbrakk> \<Longrightarrow> {A}#\<F>"
    proof-
      fix \<F> assume R2:"\<F> \<in> ?PF" and R3:"(\<forall>V \<in> Pow X. (x, V) \<in> N \<longrightarrow> {V}#\<F>)"
      then obtain R4:"\<And>V. \<lbrakk>V \<in> Pow X; V \<in> N``{x}\<rbrakk> \<Longrightarrow> {V}#\<F>"
        by auto
      then obtain R5:"\<And>V F. \<lbrakk>V \<in> N``{x}; F \<in> \<F>\<rbrakk> \<Longrightarrow> V \<inter> F \<noteq> {}"
        by (meson Image_singleton_iff is_nh mesh_singleE)
      then obtain R6:"(N``{x})#\<F>"
        using meshI by blast
      then show "{A}#\<F>"
        by (simp add: R0 R2)
    qed
    then show ?L
      by auto
  qed
  finally have P0:"(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (\<forall>\<F> \<in> ?PF. (N``{x})#\<F> \<longrightarrow> {A}#\<F>)"  by blast
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
      obtain B1:"\<And>V. \<lbrakk>V \<in> Pow X; (x, V) \<in> N\<rbrakk> \<Longrightarrow> \<not> (V \<subseteq> A)" 
        using upcl amem negr by blast
      have B2:"{(X-A)}#(N``{x})"
      proof-
        have B20:"\<And>B. B \<in> N``{x} \<Longrightarrow> B \<inter> (X-A) \<noteq> {}"
        proof-
          fix B assume "B \<in> N``{x}"
          then show "B \<inter> (X-A) \<noteq> {}"
            by (metis B1 Diff_Diff_Int Diff_empty Image_singleton_iff Int_Diff Pow_iff inf.absorb_iff1 is_nh)
        qed
        then show ?thesis
          by (metis Int_commute mesh_singleI)
      qed
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
  show ?R 
  unfolding LimCl_def ClLim_def
  proof(rule CollectI,rule case_prodI,auto)
    show "\<F> \<in> pfilters_on (pwr X) (Pow X)"
      by (simp add: pfil)
    show "x \<in> X"
      by (simp add: xmem)
    show "\<And>A. A \<subseteq> X \<Longrightarrow> {A} # \<F> \<Longrightarrow> x \<in> X"
      using xmem by auto
    show "\<And>A. A \<subseteq> X \<Longrightarrow> {A} # \<F> \<Longrightarrow> \<exists>\<F>\<in>pfilters_on (pwr X) (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim"
      using L pfil by blast
  qed
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
  assumes prtp:"is_prtop X Lim"
  shows prtp_lim_cleq:"(ClLim Lim X) = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}" and
        prtp_lim_ccl0:"(ClLim Lim X)``{{}}={}" and
        prtp_lim_ccl1:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq>(ClLim Lim X)``{A}" and
        prtp_lim_ccl2:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (ClLim Lim X)``{A \<union> B}=(ClLim Lim X)``{A} \<union> (ClLim Lim X)``{B}" and
        prtp_lim_ccl3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>  (ClLim Lim X)``{A} \<subseteq>  (ClLim Lim X)``{B}"
proof-
  obtain centered:"\<And>x. x \<in> X \<Longrightarrow> (lcro (pwr X) (Pow X) {x}, x) \<in> Lim"
    by (meson centered_def prtp)
  obtain  upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim"
    using isoconv_def prtp by fastforce
  obtain  vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim "
    using onpconv_def prtp by force
  obtain  is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"
    by (metis isconvs_def prtp) 
  show Q0:"(ClLim Lim X) = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}" (is "?L = ?R")
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
    from P1 have P2:"\<And>A x. (A, x) \<in> (ClLim Lim X) \<Longrightarrow>  (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)"
      by (metis (no_types, lifting) ClLim_def CollectD case_prodD)
    from P1 have P3: "\<And>A x.   (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim) \<Longrightarrow> (A, x) \<in> (ClLim Lim X)"
      by (meson PowI is_limit pfilters_on_iff setfilters0 setfilters3) 
    from P2 have P4:"?L\<subseteq>?R"
      by (simp add: ClLim_def Collect_mono_iff) 
    also from P3 have P5:"?R \<subseteq> ?L"
      by blast
    then show ?thesis
      using calculation by fastforce
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
      obtain B0:"(lcro (pwr X) (Pow X) {x}) \<in> pfilters_on (pwr X) (Pow X)"
        using xa amem centered is_limit by auto
      obtain B1:"{A}#(lcro (pwr X) (Pow X) {x})"
        by (meson B0 PowD amem bot.extremum filter_mem_mesh insert_subsetI lcroI1 pwr_mem_iff xa)
      obtain B2:"(lcro (pwr X) (Pow X) {x}, x) \<in> Lim"
        by (meson PowD amem centered in_mono xa)
      then show "x \<in> (ClLim Lim X)``{A}" 
        unfolding ClLim_def using Image_singleton_iff amem case_prodI is_limit B0 B1 B2 by auto 
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
          proof(rule ClLim_Im_memI)
            show " B \<in> Pow X"
              using bmem by auto
            show " x \<in> X"
              using B14 is_limit by blast
              show " \<exists>\<F>\<in>pfilters_on (pwr X) (Pow X). {B} # \<F> \<and> (\<F>, x) \<in> Lim"
                using B13 B14 B14a filter_mem_mesh by blast
          qed
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
        then obtain B0:"x \<in>  (ClLim Lim X)``{A} \<or> x \<in>  (ClLim Lim X)``{B}" 
          by auto
        then obtain G where B1:"G \<in> pfilters_on (pwr X) (Pow X)" and B2:"(G, x) \<in> Lim \<and> (A \<in> G \<or>  B \<in> G)"  
          using ClLim_def Q0 Image_Collect_case_prod mem_Collect_eq singletonD by auto 
        then obtain B1b:"is_pfilter (pwr X) (Pow X) G"
          by (simp add: pfilters_on_iff)
        have B1c:"A \<union> B \<in> Pow X"
          using amem bmem by auto
        then obtain B3:"A \<union> B \<in> G"
          using B1b B2 sets_pfilter4[of X G _ "A \<union> B"]  by blast
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
  show Q4:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>  (ClLim Lim X)``{A} \<subseteq>  (ClLim Lim X)``{B}"
    by (metis Q3 subset_Un_eq)
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
        then obtain "\<exists>c\<in>\<F>. c \<subseteq> a \<and> c \<subseteq> b" 
          using \<F>_def by auto
        then show " \<exists>c\<in>\<F>. (a, c) \<in> dual (pwr X) \<and> (b, c) \<in> dual (pwr X)"
          by (meson PowD amem bmem converseI pwr_mem_iff)
      qed
      show PF04:"is_ord_cl (Pow X) \<F> (pwr X)"
      proof(rule is_ord_clI1)
        fix a b assume a0:"a \<in> \<F>" and b0:"b \<in> Pow X"  and ab0:"(a,b)\<in>pwr X" 
        then obtain a1:"a \<in> Pow X" and  ab1:"a \<subseteq> b" and x1:"x \<notin> Cl``{X-a}"
          by (simp add: \<F>_def powrel8) 
        then show "b \<in> \<F>"  
          unfolding \<F>_def using ab0 b0
          by (metis (no_types, lifting) CCl3 Diff_Int Diff_subset Pow_iff Un_iff inf.absorb_iff2 mem_Collect_eq)
      qed
    qed
    have PF1:"Pow X \<noteq> \<F>"
      by (metis (no_types, lifting) CCl2 CollectD Diff_empty Pow_bottom Pow_top \<F>_def subsetD x0)
    have F0:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
      by (simp add: PF0 PF1 is_pfilterI1 pfilters_on_iff)
    have F1a:"\<And>V. \<lbrakk>V \<in> Pow X; x \<notin> Cl `` {X - V}\<rbrakk>\<Longrightarrow> A \<inter> V \<noteq> {}"
    proof-
      fix V assume vix:"V \<in> Pow X" and xex:"x \<notin> Cl `` {X - V}"
      show "A \<inter> V \<noteq> {}" 
        using cl_lim_prtp2b[of Cl X A x]  CCl1 CCl2 CCl3 vix x0 R is_cl xex by auto
    qed
    have F1:"{A} # \<F> " 
      unfolding \<F>_def mesh_def by (simp add: F1a)
    have F2:"\<And>E. \<lbrakk>E \<in> Pow X; {E}#\<F>\<rbrakk> \<Longrightarrow> (E, x) \<in> Cl"
    proof-
      fix E assume E0:"E \<in> Pow X" and E1:"{E}#\<F>"
      then show "(E, x) \<in> Cl" 
        unfolding mesh_def \<F>_def using CCl1 CCl2 CCl3 is_cl x0 cl_lim_prtp2b[of Cl X E x]
        by (simp add: Int_commute)
    qed
    then show ?L
       unfolding ClLim_def LimCl_def using A0 x0 R F0 F1 F2 by auto
    qed
qed


definition Imfil where
  "Imfil f X Y \<F> \<equiv> {E \<in> Pow Y. \<exists>F \<in> \<F>. f`F \<subseteq> E}"

lemma Imfil_memD:
  "E \<in> Imfil f X Y \<F> \<Longrightarrow> E \<in> Pow Y \<and> (\<exists>F \<in> \<F>. f`F \<subseteq> E)"
  by (simp add: Imfil_def)

lemma Imfil_memI:
  "\<lbrakk>E \<in> Pow Y;  (\<exists>F \<in> \<F>. f`F \<subseteq> E)\<rbrakk>\<Longrightarrow>E \<in> Imfil f X Y \<F>"
  by (simp add: Imfil_def)

lemma im_filter: 
  assumes pfl:"is_pfilter (pwr X) (Pow X) \<F>" and
          ims:"f`X \<subseteq> Y"
  shows "is_pfilter (pwr Y) (Pow Y) (Imfil f X Y \<F>)"
proof(rule is_pfilterI1)
  let ?fF="Imfil f X Y \<F>"
  obtain P0:"is_dir \<F> (dual(pwr X))" and P1:"\<F>\<noteq>{}" and P2:"\<F>\<subseteq>Pow X" and "is_ord_cl (Pow X) \<F> (pwr X)"
    using pfl is_filterD1 is_pfilter_def by blast
  show "is_filter (pwr Y) (Pow Y) ?fF"
  proof(rule is_filterI1)
    show F0:"?fF \<noteq> {}"
      unfolding Imfil_def using pfl ims sets_pfilter1 sets_pfilter6 by fastforce 
    show F1:"?fF \<subseteq> Pow Y" 
      unfolding Imfil_def by blast
    show F2:"is_dir ?fF (dual (pwr Y))"
    proof(rule is_dirI1)
      fix a b assume A0:"a \<in> ?fF" and A1:"b \<in> ?fF" 
      then obtain fa fb where B0:"fa \<in> \<F>"  and B1:"fb \<in> \<F>" and B2:"f`fa \<subseteq> a" and B3:"f`fb \<subseteq> b" 
         unfolding Imfil_def by auto
      then obtain fc where B4:"fc \<in> \<F>" and B5:"fc \<subseteq> fa" and B6:"fc \<subseteq> fb"
        by (meson P0 converseD is_dirE1 powrel8)  
      then obtain B7:"f`fc \<subseteq> f`fc" and B8:"f`fc \<in> Pow Y" and B9:"f`fc \<subseteq> a" and B10:"f`fc \<subseteq> b"
        by (meson B2 B3 P2 PowD PowI equalityD1 image_mono ims in_mono subset_trans)
      obtain B11:"f`fc \<in> ?fF"
        using B4 B7 B8 Imfil_memI[of "f`fc" Y \<F> f X] by blast
      obtain B12:"(a,f`fc)\<in>dual(pwr Y)"
        using A0 B9 Imfil_memD[of a f X Y \<F>] pwr_memI1[of "f`fc" a Y] by blast 
      obtain B13:"(b,f`fc)\<in>dual(pwr Y)"
        using A1 B10 Imfil_memD[of b f X Y \<F>]  pwr_memI1[of "f`fc" b Y] by blast
      then show "\<exists>c \<in> ?fF. (a, c) \<in> dual (pwr Y) \<and> (b, c) \<in> dual (pwr Y)"
        using B11 B12 B13 by blast
    qed
    show " is_ord_cl (Pow Y) ?fF (pwr Y)"
    proof(rule is_ord_clI1)
      fix a b assume A0:"a \<in> ?fF" and A1:"b \<in> Pow Y" and A2:"(a,b)\<in>pwr Y"
      show "b \<in> ?fF"
      proof(rule Imfil_memI)
        show "b \<in> Pow Y"
          using A1 by auto
        show "\<exists>F\<in>\<F>. f ` F \<subseteq> b"
          by (meson A0 A2 Imfil_memD powrel8 subset_trans)
      qed
    qed
  qed
  show "Pow Y \<noteq> ?fF"
  proof-
    obtain ne:"{} \<notin> \<F>"
      using pfl sets_pfilter5 by blast  
    then obtain "{} \<notin> ?fF"  
      unfolding Imfil_def by auto
    then show "Pow Y \<noteq> ?fF" 
      by blast
  qed
qed



lemma cont_at2:
  "cont_at f X q Y p x \<longleftrightarrow> (\<forall>\<F>. (\<F>, x)\<in>q \<longrightarrow> (Imfil f X Y \<F>, f x)\<in>p)"
  by (simp add: Imfil_def cont_at_def)

lemma cont_atD1:
  "cont_at f X q Y p x \<Longrightarrow> (\<And>\<F>. \<lbrakk>\<F>\<in>pfilters_on (pwr X) (Pow X);(\<F>,x)\<in>q\<rbrakk>\<Longrightarrow>(Imfil f X Y \<F>, f x)\<in>p)"
  by (simp add: cont_at2)

lemma cont_atD2:
  "cont_at f X q Y p x \<Longrightarrow> (\<And>\<F>. (\<F>,x)\<in>q\<Longrightarrow>(Imfil f X Y \<F>, f x)\<in>p)"
  by (simp add: cont_at2)

lemma cont_atI2:
  "(\<And>\<F>. (\<F>,x)\<in>q\<Longrightarrow>(Imfil f X Y \<F>, f x)\<in>p) \<Longrightarrow> cont_at f X q Y p x"
  by (simp add: cont_at2)

lemma cont_atI1:
  "\<lbrakk>isconvs X q; (\<And>\<F>. \<lbrakk>\<F>\<in>pfilters_on (pwr X) (Pow X);(\<F>,x)\<in>q\<rbrakk>\<Longrightarrow>(Imfil f X Y \<F>, f x)\<in>p)\<rbrakk> \<Longrightarrow> cont_at f X q Y p x"
  by (simp add: cont_at2 isconvs_def)

lemma continuousD1:
  "\<lbrakk>cont_at f X q Y p x; (\<F>, x) \<in> q\<rbrakk> \<Longrightarrow>({E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E}, f x) \<in> p "
  by (simp add:cont_at_def)


lemma ClLim_mem_iff:
  assumes prtpx:"is_prtop X q" and
          xmem:"x \<in> X" and 
          amem:"A \<in> Pow X"
  shows "x \<in> (ClLim q X)``{A} \<longleftrightarrow> {A}#((NLim q X)``{x})"  (is "?L \<longleftrightarrow> ?R")
proof-
  obtain A0:"\<And>x \<E>. (\<E>, x) \<in> q \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"
    by (meson isgconvD1 prtpx)
  have LR:"?L \<Longrightarrow> ?R"
  proof-
    assume ?L
    then obtain F where B0:"F \<in> pfilters_on (pwr X) (Pow X)" and B1:"(F, x)\<in>q" and B2:"{A}#F"
      using ClLim_memD by force
    have B3:"(NLim q X)``{x} \<subseteq> F"
      using B0 B1 NLim_Im_memD by force
    have B4:"{A}#((NLim q X)``{x})"
      by (meson B2 B3 mesh_singleE mesh_singleI subset_eq)
    then show "?R"
      by auto
  qed
  have RL:"?R \<Longrightarrow> ?L"
    by (meson ClLim_Im_memI amem isgconvD1 onpconvD2 prtpx xmem)
  with LR RL show ?thesis
    by blast
qed


(*
1. "\<And>\<F>. (\<F>,x)\<in>q\<Longrightarrow> (Imfil f X Y \<F>, f x)\<in>p"
2. "\<And>x. x \<in> X \<Longrightarrow> (NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
3. "\<And>A. A \<in> Pow X \<Longrightarrow> f`((ClLim q X)``{A}) \<subseteq> (ClLim p Y)``{f`A}"
4. "\<And>x V. \<lbrakk>x \<in> X; V \<in> (NLim p Y)``{f x}\<rbrakk> \<Longrightarrow> vimage f V \<in> (NLim q X)``{x}"
5. "\<And>x V. \<lbrakk>x \<in> X; V \<in> (NLim p Y)``{f x}\<rbrakk> \<Longrightarrow> \<exists>U \<in> (NLim q X)``{x}. f`U \<subseteq> V"
*)

lemma cont12:
  assumes prtpx:"is_prtop X q" and
          prtpy:"is_prtop Y p" and 
          xmem0:"x \<in> X" and
          cont1:"cont_at f X q Y p x"
  shows "(NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
proof-
  obtain B0:"((NLim q X)``{x}, x)\<in>q"
    by (simp add: onpconvD2 prtpx xmem0)
  then obtain "(Imfil f X Y ((NLim q X)``{x}), f x)\<in>p"
    using cont1 cont_atD2[of f X q Y p x "(NLim q X)``{x}"]  by blast
  then show "(NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
    using NLim_Im_memD isgconvD1 prtpy by fastforce
qed

lemma cont12_global:
  assumes prtpx:"is_prtop X q" and
          prtpy:"is_prtop Y p" and 
          cont1:"\<And>x. x \<in> X \<Longrightarrow> cont_at f X q Y p x "
  shows "\<And>x. x \<in> X \<Longrightarrow> (NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
proof-
  fix x assume xmem:"x \<in> X"
  then show "(NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
    using xmem assms cont12[of X q Y p x f] by blast
qed

lemma cont21:
  assumes prtpx:"is_prtop X q" and
          prtpy:"is_prtop Y p" and 
          map:"f`X \<subseteq> Y" and
          cont2:"\<And>x. x \<in> X \<Longrightarrow> (NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
  shows "cont_at f X q Y p x" (*(\<F>, x)\<in>q implicitly yields x \<in> X *)
proof(rule cont_atI1)
  show P0:"isconvs X q"
    by (simp add: prtpx)
  show "\<And>\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<Longrightarrow> (\<F>, x) \<in> q \<Longrightarrow> (Imfil f X Y \<F>, f x) \<in> p"
  proof-
    fix \<F> assume A0:" \<F> \<in> pfilters_on (pwr X) (Pow X)" and A1:"(\<F>, x) \<in> q"
    then obtain B0:"(NLim q X)``{x} \<subseteq> \<F>"
      using NLim_Im_memD by fastforce
    have B1:"(NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
      by (meson A1 P0 cont2 isgconvD1)
    have B2:"... \<subseteq>  Imfil f X Y \<F>"
    proof
      fix E assume L0:"E \<in> Imfil f X Y (NLim q X `` {x})"
      then obtain L1:"E \<in> Pow Y" 
        using Imfil_memD[of E f X Y ] by presburger
      obtain F where L2:"F \<in> (NLim q X `` {x})" and L3:"f`F \<subseteq> E"
        using B0 L0 Imfil_memD[of E f X Y " (NLim q X `` {x})"]  by auto
      then have L4:"F \<in> \<F>"
        using B0 by auto 
      show "E \<in> Imfil f X Y \<F>"
        using L1 L4 L3 Imfil_memI[of E Y \<F> f X]  by blast
    qed
    have B3:"((NLim p Y)``{f x}, f x)\<in>p"
      using A1 P0 isgconvD1 map onpconvD2 prtpy by fastforce
    have B4:"Imfil f X Y \<F> \<in> pfilters_on (pwr Y) (Pow Y)"
      by (meson A0 im_filter map pfilters_on_iff)
    have B5:"(NLim p Y)``{f x}  \<subseteq> Imfil f X Y \<F> "
      using B1 B2 by auto
    show "(Imfil f X Y \<F>, f x) \<in> p"
      using B3 B4 B5 isoconvD1[of Y p "Imfil f X Y \<F>" "(NLim p Y)``{f x}" "f x"]  prtpy by blast
  qed
qed


lemma cont21_global:
  assumes prtpx:"is_prtop X q" and
          prtpy:"is_prtop Y p" and 
          map:"f`X \<subseteq> Y" and
          cont2:"\<And>x. x \<in> X \<Longrightarrow> (NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
  shows "\<And>x. x \<in> X \<Longrightarrow> cont_at f X q Y p x "
proof-
  fix x assume xmem:"x \<in> X"
  then show "cont_at f X q Y p x" 
    using assms cont21[of X q Y p f] by auto
qed
  


lemma cont23:
  assumes prtpx:"is_prtop X q" and
          prtpy:"is_prtop Y p" and 
          cont2:"\<And>x. x \<in> X \<Longrightarrow> (NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})" and
          fmap:"f`X \<subseteq> Y" and
          amem:"A \<in> Pow X"
  shows "f`((ClLim q X)``{A}) \<subseteq> (ClLim p Y)``{f`A}" (is "?L \<subseteq> ?R")
proof
  fix y assume A0:"y \<in> ?L"
  then obtain x where B0:"x \<in> (ClLim q X)``{A}" and B1:"y = f x"
    by blast
  then obtain B2:"{A}#((NLim q X)``{x})"
    using ClLim_Im_memD[of x q X A] NLim_Im_memD[of _ q X x] mesh_singleE mesh_singleI[of "(NLim q X)``{x}" "A"] by metis
  have B3:"{f`A}#(Imfil f X Y ((NLim q X)``{x}))"
  proof(rule mesh_singleI)
    fix a assume B4:"a \<in> Imfil f X Y (NLim q X `` {x})"
    then have B5:"a \<in> Pow Y"
      by (simp add: Imfil_def)
    obtain F where B6:"F \<in> NLim q X `` {x}" and B7:"f`F \<subseteq> a"
      using B4 Imfil_memD[of a f X Y "NLim q X `` {x}"] by blast
    have B8:"F \<inter> A \<noteq> {}"
      by (metis B2 B6 inf_sup_aci(1) mesh_singleE)
    then show "f ` A \<inter> a \<noteq> {}"
      using B7 by blast
  qed
  have B9:"{f`A}#((NLim p Y)``{f x})"
  proof(rule mesh_singleI)
    fix a assume "a \<in> (NLim p Y``{f x})"
    then obtain "a \<in>  Imfil f X Y ((NLim q X)``{x})"
      using B0 ClLim_Im_memD cont2 by fastforce
    then show "(f`A) \<inter> a \<noteq> {}"
      using B3 mesh_singleE by auto
  qed
  have B10:"(f x) \<in> (ClLim p Y)``{f`A}"
    by (meson B0 B9 ClLim_Im_memD ClLim_mem_iff fmap image_Pow_mono image_eqI in_mono prtpy)
  then show "y \<in> ?R"
    using B1 by blast
qed


lemma cont34:
 assumes prtpx:"is_prtop X q" and
         prtpy:"is_prtop Y p" and 
         fmap1:"f`X \<subseteq> Y" and 
         fmap2:"vimage f Y \<subseteq> X" and 
         cont3:"\<And>A. A \<in> Pow X \<Longrightarrow> f`((ClLim q X)``{A}) \<subseteq> (ClLim p Y)``{f`A}"
 shows "\<And>x V. \<lbrakk>x \<in> X; V \<in> (NLim p Y)``{f x}\<rbrakk> \<Longrightarrow> vimage f V \<in> (NLim q X)``{x}"
proof-
  fix x V assume xmem:"x \<in> X" and vmem:" V \<in> (NLim p Y)``{f x}"
  then show "vimage f V \<in> (NLim q X)``{x}"
  proof-
    have "\<And>V. \<lbrakk>V \<in> Pow Y; vimage f V \<notin>  (NLim q X)``{x}\<rbrakk> \<Longrightarrow> V \<notin> (NLim p Y)``{f x}"
    proof-
      fix V assume A0:"V \<in> Pow Y" and A1:"vimage f V \<notin>  (NLim q X)``{x}"
      obtain A2:"vimage f V \<in> Pow X"
        using A0 fmap2 by auto
      let ?A="X-(vimage f V)"
      obtain A3:"?A \<in> Pow X"
        by simp
      obtain A4:"f`(?A) \<subseteq> (Y-V)"
        using fmap1 by blast
      obtain A5:"f`(?A) \<in> Pow Y" and A6:"Y-V \<in> Pow Y"
        using fmap1 by fastforce
      obtain B0:"x \<in> (ClLim q X)``{X-(vimage f V)}"
        using A1 A2 nhl2 prtpx xmem by fastforce
      then obtain B1:"f x \<in>  f`((ClLim q X)``{?A})"
        by blast
      then obtain B2:"f x \<in> (ClLim p Y)``{f`(?A)}"
        by (meson A3 cont3 in_mono)
      have B3:"(ClLim p Y)``{f`(?A)} \<subseteq>  (ClLim p Y)``{Y-V}"
        by (meson A4 A5 A6 prtp_lim_ccl3 prtpy)
      then obtain B4:"f x \<in> (ClLim p Y)``{Y-V}"
        using B2 by blast
      then show "V \<notin> (NLim p Y)``{f x}"
        by (meson NLim_Im_memD nhl2 prtpy)
    qed
  then show ?thesis
    by (meson NLim_Im_memD vmem)
  qed
qed


lemma cont45:
   assumes prtpx:"is_prtop X q" and
           prtpy:"is_prtop Y p" and  
           fmap1:"f`X \<subseteq> Y" and 
           fmap2:"vimage f Y \<subseteq> X" and
           cont4:"\<And>x V. \<lbrakk>x \<in> X; V \<in> (NLim p Y)``{f x}\<rbrakk> \<Longrightarrow> vimage f V \<in> (NLim q X)``{x}"
  shows  "\<And>x V. \<lbrakk>x \<in> X; V \<in> (NLim p Y)``{f x}\<rbrakk> \<Longrightarrow> \<exists>U \<in> (NLim q X)``{x}. f`U \<subseteq> V"
proof-
  fix x V assume xmem:"x \<in> X" and vmem:"V \<in> (NLim p Y)``{f x}"
  show "\<exists>U \<in> (NLim q X)``{x}. f`U \<subseteq> V"
  proof-
  let ?U="vimage f V"
  obtain B0:"?U \<in> (NLim q X)``{x}"
    using cont4 vmem xmem by auto
  also obtain B1:"f`?U \<subseteq> V"
    by blast
  then show ?thesis
    using calculation by blast
  qed
qed
  

lemma cont52:
  assumes prtpx:"is_prtop X q" and
          prtpy:"is_prtop Y p" and 
          cont5:"\<And>x V. \<lbrakk>x \<in> X; V \<in> (NLim p Y)``{f x}\<rbrakk> \<Longrightarrow> \<exists>U \<in> (NLim q X)``{x}. f`U \<subseteq> V" and
          fmap1:"f`X \<subseteq> Y" and 
          fmap2:"vimage f Y \<subseteq> X" 
  shows "\<And>x. x \<in> X \<Longrightarrow> (NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})"
proof-
  fix x assume xmem:"x \<in> X"
  show "(NLim p Y)``{f x} \<subseteq> Imfil f X Y ((NLim q X)``{x})" (is "?L \<subseteq> ?R")
  proof
    fix V assume A0:"V \<in> ?L"
    then have B0:"\<exists>U \<in> (NLim q X)``{x}. f`U \<subseteq> V"
      by (simp add: cont5 xmem)
    then obtain U where "U \<in> (NLim q X)``{x}" and "f`U \<subseteq> V"
      by blast
    then show "V \<in> ?R"
      by (meson A0 Imfil_memI NLim_Im_memD)
  qed
qed

(*
so 2\<longrightarrow>3\<longrightarrow>4\<longrightarrow>5\<longrightarrow>2 and 1\<longrightarrow>2\<longrightarrow>1 which is 1\<longleftrightarrow>2\<longleftrightarrow>3\<longleftrightarrow>4\<longleftrightarrow>5 
*)
print_options

end