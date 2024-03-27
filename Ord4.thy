theory Ord4
  imports Main
begin

no_notation List.list.Nil ("[]") and Cons (infixr "#" 65)  and less_eq  ("\<le>") and 
                 less  ("<") and greater_eq (infix "\<ge>" 50) and greater  (infix ">" 50) 
no_notation less_eq  ("'(\<le>')") and less_eq  ("(_/ \<le> _)"  [51, 51] 50) and  less  ("'(<')") and  less  ("(_/ < _)"  [51, 51] 50) and greater_eq (infix "\<ge>" 50) and greater  (infix ">" 50)

hide_const top bot inf Inf Sup sup  List.list.Nil rev less_eq
hide_type list
print_options
declare [[show_consts,show_sorts,show_types, show_results]]

lemma image_p: "(\<And>a. a \<in> A \<Longrightarrow> P (f a)) \<Longrightarrow> (\<forall>y \<in> f ` A.  P(y))"  by blast
lemma un_to_ind_un: "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Union>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Union>i \<in> I. f i))"  by simp
lemma int_to_ind_int:"(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Inter>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Inter>i \<in> I. f i))" by simp
lemma ex_to_space:  " \<exists>x. x \<in> X \<and> Q x \<Longrightarrow>  \<exists>x \<in> X. Q x"  by blast
section Pow_ne
definition Pow_ne :: "'a set \<Rightarrow> 'a set set" where "Pow_ne A = {B. B \<subseteq> A \<and> B \<noteq> {}}"
lemma Pow_ne_iff [iff]: "A \<in> Pow_ne B \<longleftrightarrow> A \<subseteq> B \<and> A \<noteq> {}"  by (simp add: Pow_ne_def)
lemma Pow_neI: "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<in> Pow_ne B"  by (simp add: Pow_def)
lemma Pow_neD1: "A \<in> Pow_ne B \<Longrightarrow> A \<subseteq> B"   by (simp add: Pow_ne_def)
lemma Pow_neD2: "A \<in> Pow_ne B \<Longrightarrow> A \<noteq> {}"  by (simp add: Pow_ne_def)
lemma Pow_neD: "A \<in> Pow_ne B \<Longrightarrow> A \<subseteq> B \<and> A \<noteq> {}"  by (simp add: Pow_ne_def)
lemma Pow_nebottom: "{} \<notin> Pow_ne B"by simp
lemma Pow_ne_top: "A \<noteq> {} \<Longrightarrow> A \<in> Pow_ne A" by simp
lemma Pow_not_empty: "A \<noteq> {} \<Longrightarrow> Pow_ne A \<noteq> {}"  using Pow_ne_top by blast
lemma Pow_ne_empty [simp]: "Pow_ne {} = {}"  by (auto simp add: Pow_ne_def)
lemma Pow_ne_iso:"A \<subseteq> B \<Longrightarrow> Pow_ne A \<subseteq> Pow_ne B" by blast

definition Fpow_ne :: "'a set \<Rightarrow> 'a set set" where "Fpow_ne A = {B \<in> Fpow A. B \<noteq> {}}"
lemma Fpow_ne_iff1[iff]: "A \<in> Fpow_ne B \<longleftrightarrow> A \<in> Fpow B \<and> A \<noteq> {}"  by (simp add: Fpow_ne_def)
lemma Fpow_ne_iff2[iff]: "A \<in> Fpow_ne B \<longleftrightarrow> A \<subseteq> B \<and> finite A \<and> A \<noteq> {}" by (simp add: Fpow_Pow_finite) 

lemma Fpow_neI: "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<in> Fpow_ne B"  by (simp add: Fpow_def)
lemma Fpow_neD0:"A \<in> Fpow_ne B \<Longrightarrow> A \<in> Fpow B" by simp
lemma Fpow_neD1:"A \<in> Fpow_ne B \<Longrightarrow> A \<subseteq> B"  by blast
lemma Fpow_neD2:"A \<in> Fpow_ne B \<Longrightarrow> A \<noteq> {}" by blast
lemma Fpow_neD3:"A \<in> Fpow_ne B \<Longrightarrow> finite A" by blast
lemma Fpow_nebottom: "{} \<notin> Fpow_ne B"by simp
lemma Fpow_ne_top: "A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<in> Fpow_ne A" by blast
lemma Fpow_not_empty: "A \<noteq> {} \<Longrightarrow> Fpow_ne A \<noteq> {}"  by (metis Fpow_ne_iff2 empty_subsetI ex_in_conv finite.simps insert_subset)
lemma Fpow_ne_empty [simp]: "Fpow_ne {} = {}"  by (auto simp add: Pow_ne_def)
lemma Fpow_ne_iso:"A \<subseteq> B \<Longrightarrow> Fpow_ne A \<subseteq> Fpow_ne B" by blast

section RelationalBounds

abbreviation qoset where "qoset R X \<equiv> (refl_on X R) \<and> (trans_on X R)"
abbreviation poset where "poset R X \<equiv> (refl_on X R) \<and> (trans_on X R) \<and> (antisym_on X R)"

definition ub::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "ub R A b\<equiv> (\<forall>a. a \<in> A \<longrightarrow> (a, b) \<in> R)"
lemma ubI1:"(\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> ub R A b"  by(simp add:ub_def)
lemma ubE1:"ub R A b \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> R)"  by(simp add:ub_def)
lemma ub_empty:"ub R {} b" by (simp add: ub_def)
lemma ub_iff1: "ub R A x \<longleftrightarrow> (\<forall>a \<in> A. (a, x) \<in> R)"  by(auto simp add:ub_def)
lemma bd_iso:"A \<subseteq> B \<Longrightarrow> ub R B b \<Longrightarrow> ub R A b"  by (simp add: subset_eq ub_def)
lemma ub_iso1: "\<lbrakk>(x, y) \<in> R; ub R A x; y \<in> X; x \<in> X;trans_on X R; A \<subseteq> X\<rbrakk> \<Longrightarrow>ub R A y" by (meson subset_iff trans_onD ub_iff1) 
lemma ub_singleton:"(x, x) \<in> R \<Longrightarrow> ub R {x} x"  by (simp add: ub_def)
lemma ub_singletonI: "ub R {y} x \<Longrightarrow> (y, x) \<in> R"  by (simp add: ubE1)
lemma ub_singletonD: "(y, x) \<in> R \<Longrightarrow> ub R {y} x" by(simp add:ub_def)
lemma ub_singleton_simp: "ub R {y} x \<longleftrightarrow> (y, x) \<in> R" by (simp add: ub_def)
lemma ub_insert:"\<lbrakk>ub R F c; (x, c) \<in> R\<rbrakk> \<Longrightarrow> ub R (insert x F) c" by (simp add: ub_def)
lemma ub_unI:"(\<And>A. A \<in> S \<Longrightarrow> ub R A x) \<Longrightarrow> ub R (\<Union>S) x"  by (simp add: ub_iff1)

lemma ub_unD: "ub R (\<Union>S) x \<Longrightarrow> A \<in> S \<Longrightarrow> ub R A x" by (metis Union_upper bd_iso)
lemma ub_imageI:  "(\<And>a. a \<in> A \<Longrightarrow> (f a, x) \<in> R) \<Longrightarrow> ub R (f`A) x"  by (simp add: ub_iff1)

lemma bdsingle:"ub R A b \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> ub R {a} b)"  by (simp add: ub_def)  
lemma bdinsert1:"ub R (insert a A) b \<Longrightarrow> ub R {a} b" by(rule ubI1, erule ubE1,simp)
lemma bdinsert2:"ub R (insert a A) b \<Longrightarrow> ub R A b" by(rule ubI1, simp add: ubE1)
lemma bdinsert3:"ub R {a} b \<Longrightarrow> ub R A b \<Longrightarrow> ub R (insert a A) b" by(rule ubI1, auto intro:ubE1)
lemma bdinsert4:"ub R (insert a A) b \<longleftrightarrow> ub R {a} b \<and> ub R A b" by(auto, erule bdinsert1, erule bdinsert2, erule bdinsert3, simp)
lemma fbdE1:"ub R (f`I) b \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i, b) \<in> R)" by(auto intro: ubE1)
lemma ubD1:"ub R A b \<Longrightarrow> a \<in> A \<Longrightarrow> ub R {a} b" by(rule ubI1, simp add:ubE1)

definition ubd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "ubd R X A \<equiv> {b \<in> X. ub R A b}"
lemma ubdI: "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> R); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"by(simp add: ubd_def ubI1)
lemma ubdI2: "\<lbrakk>ub R A b; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A" by (simp add: ubdI ub_def) 
lemma ubdD1: "\<lbrakk>b \<in> ubd R X A; x \<in> A\<rbrakk> \<Longrightarrow> (x, b) \<in> R"  by (simp add: ubd_def ub_def)
lemma ubdD2: "b \<in> ubd R X A \<Longrightarrow> b \<in> X"  by (simp add: ubd_def)
lemma ubdD3:  "b \<in> ubd R X A \<Longrightarrow> ub R A b"   by (simp add: ubd_def)
lemma ubd_D31:"b \<in> ubd R X A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> R)" by (simp add: ubdD1)
lemma ubd_mem_iff:   "b \<in> ubd R X A \<longleftrightarrow> (b \<in> X \<and> ub R A b)"    by(simp add: ubd_def)
lemma ubd_mem_iff2:  "b \<in> ubd R X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  (a, b) \<in> R))"   by (simp add: ubd_mem_iff ub_def)
lemma ubd_mem_iff3:  "b \<in> ubd R X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. (a, b) \<in> R))"   by (simp add: ubd_mem_iff ub_iff1)
lemma ubd_sub:  "ubd R X A \<subseteq> X" by(simp add: ubd_def)
lemma ubd_ant1:"A \<subseteq> B \<Longrightarrow> ubd R X B \<subseteq> ubd R X A"  by (simp add: subset_eq ubd_mem_iff2)
lemma ubd_ant1b: "\<lbrakk>A \<subseteq> B; b \<in> ubd R X B\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"  using ubd_ant1 by blast
lemma ubd_iso2:  "Y \<subseteq> X \<Longrightarrow> ubd R Y A \<subseteq> ubd R X A"   by (simp add:subset_iff ubd_def)
lemma ubd_iso2b:  "\<lbrakk>Y \<subseteq> X; x \<in> ubd R Y A \<rbrakk> \<Longrightarrow> x \<in> ubd R X A" by (simp add: ubd_mem_iff in_mono)
lemma ubd_emptyI:  "x \<in> X \<Longrightarrow> x \<in> ubd R X {}" by (simp add: ubd_mem_iff3)
lemma ubd_empty: "ubd R X {} = X" by(simp add: set_eq_iff ubd_mem_iff ub_def)
lemma ubd_singleton:  "(x, x) \<in> R \<Longrightarrow> x \<in> X  \<Longrightarrow> x \<in> ubd R X {x}" by (simp add: ubd_def ub_singleton)
lemma ubd_singleton2: "\<lbrakk>x \<in> X; (y, x) \<in> R \<rbrakk> \<Longrightarrow>  x \<in> ubd R X {y}" by (simp add: ub_singletonD ubdI2)
lemma ubd_singleton_iff:  "x \<in> ubd R X {y} \<longleftrightarrow> (x \<in> X \<and> (y, x) \<in> R)"by (simp add: ubd_mem_iff ub_singleton_simp)
lemma ubd_singleton3:"ubd R X {a} = {x \<in> X. (a, x) \<in> R}"  by (simp add: set_eq_iff ubd_singleton_iff)
lemma ubd_mem_insert: "\<lbrakk>c \<in> ubd R X F; (x, c) \<in> R\<rbrakk> \<Longrightarrow> c \<in> ubd R X (insert x F)" by (simp add: ubd_mem_iff ub_insert)
lemma ubd_unI:  "x \<in> X \<Longrightarrow> (\<And>A. A \<in> S \<Longrightarrow> x \<in> ubd R X A) \<Longrightarrow> x \<in> ubd R X (\<Union>S)"  by (simp add: ubd_mem_iff3)
lemma ubd_unD: "x \<in> X \<Longrightarrow> x \<in> ubd R X (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x \<in> ubd R X A"  by (meson Union_upper ubd_ant1b)
lemma ubd_imageI:  "x \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (f a, x) \<in> R) \<Longrightarrow> x \<in> ubd R X (f`A)" by (simp add: ub_imageI ubdI2)
lemma ubd_eqI1: "(\<And>x. x \<in> X \<Longrightarrow> ub R A x \<Longrightarrow> ub R B x) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> ub R B x \<Longrightarrow> ub R A x) \<Longrightarrow> ubd R X A = ubd R X B" by(auto simp add:set_eq_iff ubd_mem_iff)

lemma lubd_comp1:  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ubd (converse R) X (ubd R X A)"  by (simp add: ubdI  ubdD1 subset_iff) 
lemma lubd_comp1b:"A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. ubd (converse R) X E) \<circ> (\<lambda>E. ubd R X E)) A" by (simp add: ubdI ubdD1 subset_iff) 
lemma ulbd_comp1: "A \<subseteq> X \<Longrightarrow> A \<subseteq> ubd R X (ubd (converse R) X A)" by (metis converse_converse lubd_comp1) 
lemma ulbd_comp1b: "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. ubd R X E) \<circ> (\<lambda>E. ubd (converse R) X E)) A" by (simp add: ulbd_comp1)
lemma lubd_comp2:  "A \<subseteq> B \<Longrightarrow> ubd (converse R) X (ubd R X A) \<subseteq> ubd(converse R) X (ubd R X B)"  by (simp add: ubd_ant1)
lemma lubd_comp2b: "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. ubd (converse R) X E) \<circ> (\<lambda>E. ubd R X E)) A  \<subseteq> ((\<lambda>E. ubd (converse R) X E) \<circ> (\<lambda>E. ubd R X E)) B"by (simp add: ubd_ant1)
lemma ulbd_comp2:  "A \<subseteq> B  \<Longrightarrow> ubd R X (ubd (converse R) X A) \<subseteq> ubd R X (ubd (converse R) X B)" by (simp add: ubd_ant1)
lemma ulbd_comp2b:"A \<subseteq> B \<Longrightarrow> ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. ubd (converse R) X E)) A  \<subseteq> ((\<lambda>E. ubd R X E) \<circ> (\<lambda>E. ubd (converse R) X E)) B"  by (simp add: ubd_ant1)
lemma lubd_comp3: "ubd (converse R) X (ubd R  X A) = ubd (converse R) X (ubd R X (ubd (converse R) X (ubd R X A)))"   by (simp add: lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1) 
lemma lubd_comp3b:"((\<lambda>E. ubd (converse R) X E) \<circ> (\<lambda>E. ubd R X E)) A  = ((\<lambda>E. ubd (converse R) X E) \<circ> (\<lambda>E. ubd R X E) \<circ> (\<lambda>E. ubd (converse R) X E) \<circ> (\<lambda>E. ubd R X E)) A"  using lubd_comp3 by fastforce 
lemma ulbd_comp3: "ubd R X (ubd (converse R) X A) = ubd R X (ubd (converse R) X (ubd R X (ubd (converse R) X A)))"  by (simp add: lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1) 
lemma ulbd_comp3b: "((\<lambda>E. ubd R X E) \<circ> (\<lambda>E. ubd (converse R) X E)) A  = ((\<lambda>E. ubd R X E) \<circ> (\<lambda>E. ubd(converse R) X E) \<circ> (\<lambda>E. ubd R X E) \<circ> (\<lambda>E. ubd (converse R) X E)) A"  using ulbd_comp3 by force 

definition greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where  "greatest R A m \<equiv> m \<in> ubd R A A"

lemma greatestI1:"m \<in> ubd R A A \<Longrightarrow> greatest R A m"  by (simp add: greatest_def)
lemma greatestI2:"\<lbrakk>ub R A m; m \<in> A\<rbrakk> \<Longrightarrow> greatest R A m" by (simp add: ubd_mem_iff greatest_def)
lemma greatestI3:"\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> (a, m) \<in> R); m \<in> A\<rbrakk> \<Longrightarrow> greatest R A m" by (simp add: ubI1 greatestI2)
lemma greatestI4:"\<lbrakk>m \<in> ubd R X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> greatest R A m"  by (simp add: ubdD3 greatestI2)
lemma greatestD1:"greatest R A m \<Longrightarrow> (m \<in> A \<and> ub R A m)"by (simp add: ubd_mem_iff greatest_def)
lemma greatestD11: "greatest R A m \<Longrightarrow> m \<in> A"  by (simp add: greatestD1)
lemma greatestD12:"greatest R A m \<Longrightarrow> ub R A m"  by (simp add: greatestD1)
lemma greatestD2: "\<lbrakk>greatest R A m; a \<in> A\<rbrakk> \<Longrightarrow> (a, m) \<in> R "by (meson greatestD1 ubE1) 
lemma greatest_iff: "greatest R A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> (a, m) \<in> R))"  by (simp add: ubd_mem_iff greatest_def ub_def)
lemma greatest_unique:"antisym_on X R \<Longrightarrow> A \<subseteq> X \<Longrightarrow> greatest R A m1 \<Longrightarrow> greatest R A m2 \<Longrightarrow> m1 =m2" by (simp add: antisym_onD greatest_iff subset_iff)
lemma greatest_unique2:"antisym_on A R  \<Longrightarrow> greatest R A m1 \<Longrightarrow> greatest R A m2 \<Longrightarrow> m1 =m2" by (simp add: antisym_onD greatest_iff subset_iff)
lemma is_greatest_iso2:"A \<subseteq> B \<Longrightarrow> greatest R A ma \<Longrightarrow> greatest R B mb \<Longrightarrow> (ma, mb) \<in> R"by (simp add: greatestD1 greatestD2 subset_eq)
lemma greatest_singleton:"(x, x) \<in> R \<Longrightarrow> greatest R {x} x" by (simp add: greatestI2 ub_singleton)
lemma greatest_insert1:"(x, x) \<in> R \<Longrightarrow> ub R A x \<Longrightarrow> greatest R (insert x A) x"  by (simp add: greatestI2 ub_insert)
lemma greatest_insert2:"greatest R A m \<Longrightarrow> (x, m) \<in> R \<Longrightarrow> greatest R (insert x A) m"by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)
lemma greatest_insert3:"trans_on (insert x A) R \<Longrightarrow> refl_on (insert x A) R \<Longrightarrow> greatest R A m \<Longrightarrow> (m, x) \<in> R  \<Longrightarrow> greatest R (insert x A) x" by (meson greatestD12 greatest_insert1 insertCI refl_onD refl_onD1 subset_insertI ub_iso1)


definition Greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a" where "Greatest R A \<equiv> (THE m. greatest R A m)"

lemma greatest_equality:"\<lbrakk>antisym_on A R; (\<And>a. a \<in> A \<Longrightarrow> (a, m) \<in> R); m \<in> A\<rbrakk> \<Longrightarrow> Greatest R A = m"by (simp add: Greatest_def greatestI3 greatest_unique2 the_equality) 
lemma greatest_equality2:"\<lbrakk>antisym_on A R; greatest R A m\<rbrakk> \<Longrightarrow> Greatest R A = m" by (simp add: greatest_equality greatest_iff)
lemma greatest_equality3:"\<lbrakk>antisym_on A R; m \<in> ubd R A A\<rbrakk> \<Longrightarrow> Greatest R A = m"by (simp add: greatest_equality2 greatest_def)

abbreviation least where "least R A x \<equiv> greatest (converse R) A x"
abbreviation lb where "lb R A x \<equiv> ub (converse R) A x"
abbreviation lbd where "lbd R X A \<equiv> (ubd (converse R) X A)"

lemma lb_single_greatest1:"\<lbrakk>antisym_on X R; refl_on X R; x \<in> X\<rbrakk> \<Longrightarrow> greatest R (lbd R X {x}) x"by (simp add: greatest_iff refl_onD ubd_singleton_iff)
lemma lb_single_greatest2:"\<lbrakk>antisym_on X R; refl_on X R;  x \<in> X\<rbrakk> \<Longrightarrow> Greatest R (lbd R X {x}) = x" by (meson antisym_on_subset greatest_equality2 lb_single_greatest1 ubd_sub)

definition is_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "is_sup R X A x \<equiv> (least R (ubd R X A) x)"
abbreviation is_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "is_inf R X A x \<equiv> (is_sup (converse R) X A x)"

lemma is_supI1:"(least R (ubd R X A) x) \<Longrightarrow> is_sup R X A x" by(simp add:is_sup_def)
lemma is_supD1:"is_sup R X A x \<Longrightarrow> (least R (ubd R X A) x)"  by (simp add: is_sup_def)
lemma is_supI2:"x \<in> lbd R (ubd R X A) (ubd R X A) \<Longrightarrow> is_sup R X A x" by (simp add: greatestI1 is_supI1)
lemma is_supD2:"is_sup R X A x \<Longrightarrow> x \<in> lbd R (ubd R X A) (ubd R X A)"  by (simp add: greatest_def is_sup_def)
lemma is_supI3:"\<lbrakk>lb R (ubd R X A) x; x \<in> (ubd R  X A)\<rbrakk> \<Longrightarrow> is_sup R X A x" by (simp add: greatestI2 is_supI1)
lemma is_supD31:"is_sup R X A x \<Longrightarrow> lb R (ubd R X A) x" by (simp add: greatestD12 is_supD1)
lemma is_supD32:"is_sup R X A x \<Longrightarrow> x \<in>  (ubd R X A)" by (simp add: greatest_iff is_sup_def)
lemma is_supI4:"\<lbrakk>lb R (ubd R X A) x; x \<in> X;ub R A x\<rbrakk> \<Longrightarrow> is_sup R X A x" by (simp add: is_supI3 ubdI2)
lemma is_supE1:"is_sup R X A x \<Longrightarrow> x \<in> X" by (meson is_supD32 ubd_mem_iff) 
lemma is_supI5: "\<lbrakk>(\<And>a. a \<in> (ubd R X A) \<Longrightarrow> (x, a) \<in> R); x \<in> (ubd R X A)\<rbrakk> \<Longrightarrow> is_sup R X A x"  by (simp add: is_supI2 ubdI)
lemma is_supI6:"\<lbrakk>x \<in> X; ub R A x; (\<And>a. a \<in> (ubd R X A) \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x" by (simp add: is_supI5 ubdI2)
lemma is_supI7:"\<lbrakk>x \<in> X; ub R A x; (\<And>a. a \<in> X \<Longrightarrow> ub R A a \<Longrightarrow>  (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x" by (meson is_supI6 ubdD2 ubdD3)
lemma is_supI8:"\<lbrakk>refl_on X R; x \<in> X; (\<And>z. z \<in> ubd R X A \<longleftrightarrow>  (x, z) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"by (simp add: greatestI2 is_supI1 refl_onD ub_def)
lemma is_supI9:"\<lbrakk>refl_on X R; x \<in> X; (\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z))\<rbrakk> \<Longrightarrow> is_sup R X A x"by (meson is_supI7 refl_onD)
lemma is_supE2:"is_sup R X A x \<Longrightarrow> ub R A x"by (meson is_supD32 ubdD3) 
lemma is_supE3: "\<lbrakk>is_sup R X A x; y \<in> ubd R X A\<rbrakk> \<Longrightarrow> (x, y) \<in> R "using greatestD2 is_sup_def by fastforce                     
lemma is_supE4:"\<lbrakk>is_sup R X A x; y \<in> X; ub R A y\<rbrakk> \<Longrightarrow> (x, y) \<in> R "by (simp add: ubd_mem_iff is_supE3)    
lemma is_supE5:"\<lbrakk>refl_on X R; trans_on X R; is_sup R X A x; z \<in> X;  (x, z) \<in> R\<rbrakk> \<Longrightarrow> z \<in> ubd R X A"  by (meson is_supE2 refl_onD1 trans_on_def ub_def ubdI)
lemma is_supD1121: "\<lbrakk>is_sup R X A x; a \<in> A\<rbrakk> \<Longrightarrow> (a, x) \<in> R"by (meson is_supE2 ubE1)
lemma is_supE6:"\<lbrakk>refl_on X R; trans_on X R; is_sup R X A x;  (x, z) \<in> R\<rbrakk> \<Longrightarrow> ub R A z"by (meson is_supE5 refl_onD2 ubd_mem_iff)
lemma is_supE7:"\<lbrakk>refl_on X R; trans_on X R; is_sup R X A x;  (x, z) \<in> R; a \<in> A\<rbrakk> \<Longrightarrow> (a, z) \<in> R" by (meson is_supE6 ubE1)
lemma is_supD41:"\<lbrakk>refl_on X R; trans_on X R; is_sup R X A x\<rbrakk> \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> (x, z) \<in> R \<Longrightarrow> ub R A z)" by (simp add: is_supE6)
lemma is_supD42:"is_sup R X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  ub R A z \<Longrightarrow> (x, z) \<in> R)"by (simp add: is_supE4)
lemma is_supD5:"\<lbrakk>refl_on X R; trans_on X R; is_sup R X A x\<rbrakk> \<Longrightarrow> (\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z))"by (meson is_supE4 is_supE6)
lemma is_sup_iff1:"\<lbrakk>x \<in> X; A \<subseteq> X;refl_on X R; trans_on X R\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z)) \<longleftrightarrow> is_sup R X A x)"by (meson is_supD5 is_supI9)
lemma sup_iff2: "\<lbrakk>refl_on X R; trans_on X R\<rbrakk> \<Longrightarrow> is_sup R X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  (s, z) \<in> R \<longleftrightarrow> z \<in> ubd R X A)"by (metis is_supD32 is_supE3 is_supE5 is_supI5 refl_onD ubdD2)
lemma is_sup_unique:"\<lbrakk>antisym_on X R; is_sup R X A m1; is_sup R X A m2\<rbrakk>  \<Longrightarrow> m1 = m2" by (simp add: antisym_on_def is_supD42 is_supE1 is_supE2)
lemma is_sup_iso1:"\<lbrakk> A \<subseteq> B; is_sup R X A ma; is_sup R X B mb\<rbrakk> \<Longrightarrow> (ma, mb) \<in> R "by (simp add: is_supD32 is_supE3 ubd_ant1b)
lemma is_sup_iso2: "\<lbrakk>A \<subseteq> Y;Y \<subseteq> X; is_sup R Y A my;  is_sup R X A mx\<rbrakk> \<Longrightarrow> (mx, my) \<in> R" by (simp add: in_mono is_supD42 is_supE1 is_supE2)
lemma sup_maxI1:"\<lbrakk>is_sup R X A x; x \<in> A\<rbrakk> \<Longrightarrow> (greatest R A x)"by (simp add: greatestI2 is_supE2)
lemma sup_maxE1:"\<lbrakk>(greatest R A x); x \<in> X\<rbrakk> \<Longrightarrow> is_sup R X A x"  by (simp add: greatestD11 greatestD12 is_supI6 ubdD1)
lemma sup_maxE2:"\<lbrakk>(greatest R A x); A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup R X A x" by (simp add: greatestD11 in_mono sup_maxE1)
lemma sup_in_subset:"\<lbrakk>A \<subseteq> B;  B \<subseteq> X;  is_sup R X A s;  s \<in> B\<rbrakk> \<Longrightarrow> is_sup R B A s" by (meson is_supE2 is_supE3 is_supI6 ubd_iso2b)
lemma sup_singleton:"\<lbrakk>(s, s) \<in> R;s \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {s} s"by (simp add: greatest_singleton sup_maxE1)
lemma sup_emptyI: "least R X i \<Longrightarrow> is_sup R X {} i" by (simp add: is_sup_def ubd_empty)
lemma sup_emptyD:"is_sup R X {} i \<Longrightarrow> least R X i "by (simp add: is_sup_def ubd_empty)
lemma sup_empty: "is_sup R X {} i \<longleftrightarrow> (least R X i)" by (simp add: ubd_empty is_sup_def)
lemma sup_insert1:"\<lbrakk>(x, x) \<in> R;  ub R A x; x \<in> X\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) x"by (simp add: greatest_insert1 sup_maxE1)
lemma sup_insert2:"\<lbrakk>is_sup R X A m;  (x, m) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) m" by (metis bdinsert2 is_supD42 is_supE1 is_supE2 is_supI7 ub_insert)
lemma sup_insert3:"\<lbrakk>refl_on X R; trans_on X R; is_sup R X A m; (x, x) \<in> R; (m,x) \<in> R; x \<in> X\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) x"by (simp add: is_supD41 sup_insert1)
lemma sup_insert61:"\<lbrakk>trans_on X R; refl_on X R; is_sup R X A s1; is_sup R X {s1, x} s2\<rbrakk> \<Longrightarrow> ub R A s2"by (simp add: is_supD1121 is_supE6)
lemma sup_insert62:"\<lbrakk>trans_on X R; refl_on X R;is_sup R X A s1; is_sup R X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> ubd R X A"by (simp add: is_supE1 sup_insert61 ubd_mem_iff)
lemma sup_insert7:"\<lbrakk>is_sup R X A s1; is_sup R X {s1, x} s2; u \<in> ubd R X (insert x A)\<rbrakk> \<Longrightarrow>  (s2, u) \<in> R"by (simp add: ubd_mem_iff2 is_supE3)
lemma ub_eq_sup_eq: "(\<And>x. ub R A x \<longleftrightarrow> ub R B x) \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"by (meson is_supE1 is_supE2 is_supE4 is_supI7)
lemma sup_inf_ub:"A \<subseteq> X \<Longrightarrow> is_inf R X (ubd R X A) s \<longleftrightarrow> is_sup R X A s"  by (metis bd_iso converse_converse is_supD1 is_supD2 is_supI3 lubd_comp1 sup_maxE2 ubd_mem_iff ubd_sub)
lemma inf_sup_lb:"A \<subseteq> X \<Longrightarrow> is_sup R X (lbd R X A) s \<longleftrightarrow> is_inf R X A s"  by (metis bd_iso converse_converse is_supD1 is_supD2 is_supI3 lubd_comp1 sup_maxE2 ubd_mem_iff ubd_sub)
lemma Upper_eq_sup_eq: "ubd R X A = ubd R X B \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"  by (simp add: is_sup_def)

lemma inf_in_subset: "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_inf R X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_inf R B A s" by (simp add: sup_in_subset)

lemma sup_families1:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i. i \<in> I \<longrightarrow> is_sup R X (A i) (s i)" and
          A2:"trans_on X R" and A3:"refl_on X R"
  shows "is_sup R X (\<Union>(A`I)) t \<longleftrightarrow> is_sup R X (s`I) t"
proof(rule Upper_eq_sup_eq)
  show "ubd R X (\<Union> (A ` I)) = ubd R X (s ` I)" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix u assume L:"u \<in> ?L"  show "u \<in> ?R" by (metis A1 L image_eqI is_supE3 ubdD2 ubd_imageI ubd_unD)
    qed
    next show "?R \<subseteq> ?L"
    proof
      fix u assume R:"u \<in> ?R" show "u \<in> ?L" 
      apply(rule ubd_unI, meson R ubdD2)
        using A1 A2 A3 R fbdE1 is_supE5 ubdD2 ubdD3 by fastforce
    qed
  qed
qed   



lemma binary_supI1: "\<lbrakk>a \<in> X; b \<in> X; (b, b) \<in> R; (a, b) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X {a, b} b"by (simp add: sup_insert2 sup_singleton)
lemma binary_supI2:"\<lbrakk>a \<in> X; b \<in> X; (a, a) \<in> R; (b, a) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X {a, b} a" by (simp add: greatest_insert1 sup_maxE1 ub_singleton_simp)
lemma binary_supD21:"\<lbrakk>trans_on X R; refl_on X R; a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup R X {a, b} s; (c, a) \<in> R\<rbrakk> \<Longrightarrow>  (c, s) \<in> R"by (meson insertI1 is_supD1121 trans_onD)
lemma binary_supD22:"\<lbrakk>trans_on X R; refl_on X R; a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup R X {a, b} s; (c, b) \<in> R\<rbrakk> \<Longrightarrow>  (c, s) \<in> R" by (simp add: binary_supD21 insert_commute)
lemma binary_supD31:"\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow>  (a,s) \<in> R" by (simp add: is_supD1121)
lemma binary_supD32:"\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow>  (b, s) \<in> R"by (simp add: is_supD1121)
lemma binary_supD4:"\<lbrakk>trans_on X R; refl_on X R;a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> ((s, c) \<in> R \<longleftrightarrow> (a, c) \<in> R \<and> (b, c) \<in> R)"by (meson insertI1 insertI2 is_supD42 is_supE7 ub_insert ub_singletonD)

lemma sup_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b \<in> X. is_sup R  X {a1, a2} b" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"trans_on X R" and
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
    show "\<And>a. a \<in> ubd R X (insert x F)  \<Longrightarrow> (s2, a) \<in> R"  by (meson B0(2) B2(2) sup_insert7) 
    show "s2 \<in> ubd R X (insert x F)" by (metis A4 B0(1) B0(2) B2(1) B2(2) binary_supD31 binary_supD32 insert.prems insert_subset is_supE2 ub_iso1 ubd_mem_iff ubd_mem_insert) 
  qed
  then show ?case
    using B2(1) by blast
qed
lemma bsup_commute:"is_sup R X {a, b} c \<longleftrightarrow> is_sup R X {b, a } c "by (simp add: insert_commute)

lemma sup_ge1:"\<lbrakk>trans_on X R; c \<in> X; a \<in> X;b \<in> X; (c, a) \<in> R; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (c, s) \<in> R " by (meson binary_supD31 is_supE1 trans_onD) 
lemma sup_ge2:"\<lbrakk>trans_on X R; c \<in> X; a \<in> X;b \<in> X; (c, b) \<in> R; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (c, s) \<in> R " by (meson binary_supD32 is_supE1 trans_onD)
lemma sup_ge3:"\<lbrakk>trans_on X R; c \<in> X; a \<in> X;b \<in> X; (b, c) \<in> R; (a, c) \<in> R;is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (s, c) \<in> R " by (simp add: is_supD42 ub_insert ub_singleton_simp)
lemma sup_ge4:"\<lbrakk>trans_on X R; x \<in> X; y \<in> X;z \<in> X; (x, y) \<in> R; is_sup R X {y, z} syz; is_sup R X {x, z} sxz\<rbrakk>  \<Longrightarrow> (sxz, syz) \<in> R " by (metis sup_ge1 binary_supD32 is_supE1 sup_ge3)
lemma sup_ge5:"\<lbrakk>trans_on X R;is_sup R X {x1, x2} sx; is_sup R X {y1, y2} sy; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;(x1,y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow>(sx, sy) \<in> R"by (metis sup_ge1 sup_ge2 is_supE1 sup_ge3)
lemma ge_sup_iff:"\<lbrakk>trans_on X R; is_sup R X {a, b} s; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((s, c) \<in> R \<longleftrightarrow> (a, c) \<in> R \<and> (b, c) \<in> R)"by (meson binary_supD31 binary_supD32 is_supE1 sup_ge3 trans_onD)
lemma sup_assoc1:"\<lbrakk>trans_on X R; antisym_on X R; is_sup R X {a, b} sab; is_sup R X {sab, c} sab_c; is_sup R X {b, c} sbc; is_sup R X {a, sbc} sbc_a;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sbc_a = sab_c"  by (smt (verit, best) Ord4.sup_ge1 antisym_onD binary_supD32 bsup_commute is_supE1 sup_ge3)
lemma sup_assoc2:"\<lbrakk>trans_on X R; antisym_on X R; is_sup R X {b, c} sbc; is_sup R X {a, sbc} sbc_a; is_sup R X {a, c} sac; is_sup R X {b, sac} sac_b;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sac_b = sbc_a" by (meson bsup_commute sup_assoc1)
lemma sup_idem2:"\<lbrakk>a \<in> X; b \<in> X; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> is_sup R X {a, s} s"by (simp add: binary_supD31 binary_supI1 is_supD42 is_supE1 is_supE2)
lemma sup_idem3:"\<lbrakk>a \<in> X; b \<in> X; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> is_sup R X {b, s} s"by (simp add: bsup_commute sup_idem2)
lemma sup_upper_bounds:"\<lbrakk>is_sup R X A s; trans_on X R; refl_on X R\<rbrakk> \<Longrightarrow>  ubd R X {s} = ubd R X A"by (meson is_supD41 is_supE4 ub_singletonD ub_singletonI ubd_eqI1)
definition Sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where "Sup R X A \<equiv> (THE m. is_sup R X A m)"
abbreviation Inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where "Inf R X A \<equiv> Sup (converse R) X A"

lemma sup_equality:"\<lbrakk>trans_on X R; antisym_on X R;is_sup R X A m \<rbrakk>  \<Longrightarrow> Sup R X A = m" by (simp add: Sup_def is_sup_unique the_equality) 
lemma sup_exI: "\<lbrakk> trans_on X R; antisym_on X R;\<exists>s. is_sup R X A s\<rbrakk> \<Longrightarrow> (\<And>s. is_sup R X A s \<Longrightarrow> P s) \<Longrightarrow> P (Sup R X A)"  using sup_equality by fastforce

definition is_sup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_sup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup R X {a, b} x))"

abbreviation is_inf_semilattice where "is_inf_semilattice R X \<equiv> is_sup_semilattice (converse R) X"


lemma sup_families1b:"\<lbrakk>poset R X; A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si); x \<in> X\<rbrakk> \<Longrightarrow> ub R (Sup R X ` A) x \<Longrightarrow> ub R (\<Union> A) x"  by (metis fbdE1 is_supD41 sup_equality ub_unI)

lemma sup_families2b:"\<lbrakk>poset R X; A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si); x \<in> X; ub R (\<Union>A) x\<rbrakk>   \<Longrightarrow>  ub R ((Sup R X) ` A) x" by (metis is_supD5 sup_equality ub_imageI ub_unD)

lemma sup_families:"\<lbrakk>poset R X; A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si)\<rbrakk> \<Longrightarrow>(is_sup R X ((\<lambda>Ai. Sup R X Ai)`A) s) \<longleftrightarrow> (is_sup R X (\<Union>A) s)"  by(rule Upper_eq_sup_eq, rule ubd_eqI1,simp add: sup_families1b,simp add: sup_families2b) 


lemma ssupD1:"\<lbrakk>is_sup_semilattice R X\<rbrakk> \<Longrightarrow> (\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b \<in> X. is_sup R  X {a1, a2} b)"  by (meson is_supE1 is_sup_semilattice_def)
lemma ssupD2:"\<lbrakk>is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X {a, b} x) " by (simp add: is_sup_semilattice_def)
lemma ssupD3:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {a, b} (Sup R X {a, b}) " by (simp add: ssupD2 sup_exI)
lemma ssupD4:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  (Sup R X {a, b}) \<in> X" by (meson is_supE1 ssupD3)
lemma ssupD5:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;finite A; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  \<exists>b \<in> X. is_sup R X A b"  by (simp add: ssupD1 sup_finite)

lemma bsup_geI1:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (c, a) \<in> R\<rbrakk>  \<Longrightarrow> (c, Sup R X {a, b}) \<in> R"by (meson sup_ge1 ssupD3)
lemma bsup_geI2:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (c, b) \<in> R\<rbrakk>  \<Longrightarrow> (c, Sup R X {a, b}) \<in> R"by (meson sup_ge2 ssupD3)
lemma bsup_geI3:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (a,c) \<in> R; (b, c) \<in> R\<rbrakk> \<Longrightarrow> (Sup R X {a, b}, c) \<in> R"  by (meson ge_sup_iff ssupD3)
lemma bsup_geI4: "\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; x \<in> X; y \<in> X; z \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (Sup R X {x, z}, Sup R X {y, z}) \<in> R"  by (simp add: binary_supD32 bsup_geI1 bsup_geI3 ssupD3 ssupD4) 
lemma bsup_geI5: "\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;(x1, y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow> (Sup R X {x1, x2}, Sup R X {y1, y2}) \<in> R" by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)
lemma bsup_iff:  "\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((Sup R X {a, b}, c) \<in> R \<longleftrightarrow>  (a, c) \<in> R\<and>  (b, c) \<in> R)"  by (meson ge_sup_iff ssupD3)

lemma bsupI:  "\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; (\<And>s. is_sup R X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Sup R X {a, b})"by (simp add: ssupD3)

lemma bsup_commute1:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, b} = Sup R X {b, a}"by (simp add: insert_commute)

lemma bsup_assoc1:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a, b}, c} =Sup R X {a, Sup R X {b, c}}" using sup_assoc1[of X R a b "Sup R X {a, b}" c "Sup R X {Sup R X {a, b}, c}" "Sup R X {b, c}" "Sup R X {a, Sup R X {b, c}}"] by (simp add: ssupD3 ssupD4)
lemma bsup_assoc2: "\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, Sup R X {b, c}} = Sup R X {b, Sup R X {a, c}}" using sup_assoc2[of X R b c "Sup R X {b, c}" "Sup R X {a, Sup R X {b, c}}" "Sup R X {a, c}" "Sup R X {b, Sup R X {a, c}}"]by (metis bsup_assoc1 doubleton_eq_iff)

lemma bsup_idem2:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {a, Sup R X {a, b}} =  Sup R X {a, b}" by (simp add: ssupD3 sup_equality sup_idem2)
lemma bsup_idem3:"\<lbrakk>trans_on X R; antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {Sup R X {a, b}, b} =  Sup R X {a, b}" by (metis bsup_idem2 doubleton_eq_iff)

lemma binf_geI1:"\<lbrakk>trans_on X R; antisym_on X R; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (a, c) \<in> R\<rbrakk>  \<Longrightarrow> (Inf R X {a, b}, c) \<in> R" by (meson antisym_on_converse bsup_geI1 converseD converseI refl_on_converse trans_on_converse) 
lemma binf_geI2:"\<lbrakk>trans_on X R; antisym_on X R; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (b, c) \<in> R\<rbrakk>  \<Longrightarrow> (Inf R X {a, b}, c) \<in> R" by (meson antisym_on_converse bsup_geI2 converse.simps refl_on_converse trans_on_converse)
lemma binf_geI3:"\<lbrakk>trans_on X R; antisym_on X R; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (c,a) \<in> R; (c, b) \<in> R\<rbrakk> \<Longrightarrow> (c, Inf R X {a, b}) \<in> R" by (metis antisym_on_converse bsup_iff converseD converseI  trans_on_converse) 
lemma binf_geI4:"\<lbrakk>trans_on X R; antisym_on X R; is_inf_semilattice R X; x \<in> X; y \<in> X; z \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (Inf R X {x, z}, Inf R X {y, z}) \<in> R"by (meson antisym_on_converse bsup_geI4 converseD converseI refl_on_converse trans_on_converse) 
lemma binf_geI5:"\<lbrakk>trans_on X R; antisym_on X R; is_inf_semilattice R X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;(x1, y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow> (Inf R X {x1, x2}, Inf R X {y1, y2}) \<in> R"by (simp add: binf_geI1 binf_geI2 binf_geI3 ssupD4)
lemma binf_iff: "\<lbrakk>trans_on X R; antisym_on X R; is_inf_semilattice R X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((c, Inf R X {a, b}) \<in> R \<longleftrightarrow>  (c, a) \<in> R\<and>  (c, b) \<in> R)" by (metis antisym_on_converse bsup_iff converseD converseI trans_on_converse)  


lemma binfI:  "\<lbrakk>poset R X; is_inf_semilattice R X; (\<And>s. is_inf R X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Inf R X {a, b})"by (simp add: ssupD3)

lemma binf_commute1:"\<lbrakk>poset R X; is_inf_semilattice R X;a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {a, b} = Inf R X {b, a}"by (simp add: insert_commute)

lemma binf_assoc1:"\<lbrakk>poset R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, c} =Inf R X {a, Inf R X {b, c}}" by (simp add: bsup_assoc1) 
lemma binf_assoc2: "\<lbrakk>poset R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {a, Inf R X {b, c}} = Inf R X {b, Inf R X {a, c}}" by (simp add: bsup_assoc2) 

lemma binf_idem2:"\<lbrakk>poset R X; is_inf_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  Inf R X {a, Inf R X {a, b}} =  Inf R X {a, b}" by (simp add: ssupD3 sup_equality sup_idem2)
lemma binf_idem3:"\<lbrakk>poset R X; is_inf_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  Inf R X {Inf R X {a, b}, b} =  Inf R X {a, b}" by (simp add: bsup_idem3) 



definition maximal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "maximal R A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> (x, a) \<in> R \<longrightarrow> a = x)"
lemma maximalD1:"maximal R A x \<Longrightarrow> x \<in> A"  by(simp add:maximal_def)
lemma maximalD2:"maximal R A x \<Longrightarrow> (\<forall>a. a \<in> A \<and> (x, a) \<in> R \<longrightarrow> a = x)"by(simp add:maximal_def)
lemma maximalD3:"maximal R A x \<Longrightarrow> a \<in> A \<Longrightarrow> (x, a) \<in> R \<Longrightarrow> a = x" by(simp add:maximal_def)
lemma maximalI1:"\<lbrakk>x \<in> A; (\<And>a. \<lbrakk>a \<in> A; (x, a) \<in> R\<rbrakk> \<Longrightarrow> a = x)\<rbrakk> \<Longrightarrow> maximal R A x" by(simp add:maximal_def)
lemma maximalI3:"\<lbrakk>refl_on X R; trans_on X R; antisym_on X R;greatest R A x\<rbrakk> \<Longrightarrow> maximal R A x" by (meson antisym_onD greatestD11 greatestD12 maximalI1 refl_onD1 ubE1)

definition is_lattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where "is_lattice R X \<equiv> ((X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf R X {a, b} x) \<and>  (\<exists>x. is_sup R X {a, b} x)))"

lemma lattice_ssup:"is_lattice R X \<Longrightarrow> is_sup_semilattice R X"  by (simp add: is_lattice_def is_sup_semilattice_def)
lemma lattice_sinf:"is_lattice R X \<Longrightarrow> is_inf_semilattice R X"  by (simp add: is_lattice_def is_sup_semilattice_def)

lemma latt_iff:"is_lattice R X \<longleftrightarrow> (is_inf_semilattice R X) \<and> (is_sup_semilattice R X)" by (metis is_lattice_def is_sup_semilattice_def)

lemma lattice_absorb1: "\<lbrakk>poset R X; is_lattice R X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x,Inf R X {x, y}} = x"
proof-
  assume A0:"poset R X" "is_lattice R X"  "x \<in> X" "y \<in> X"
  obtain A1:" (is_inf_semilattice R X) \<and> (is_sup_semilattice R X)"  by (simp add: A0(2) lattice_sinf lattice_ssup)
  obtain B0:"(Inf R X {x, y}, x) \<in> R"  by (meson A0(1) A0(3) A0(4) A1 antisym_on_converse bsup_geI1 converseD refl_onD refl_on_converse trans_on_converse) 
  obtain B1:"(x, Sup R X {x,Inf R X {x, y}}) \<in> R"  by (meson A0(1) A0(3) A1 B0 bsup_geI1 refl_onD refl_onD1)
  obtain B2:"(Sup R X {x,Inf R X {x, y}}, x) \<in> R"  by (meson A0(1) A0(3) A1 B0 bsup_geI3 refl_onD refl_onD1)
  show "Sup R X {x,Inf R X {x, y}} = x"  by (meson A0(1) B1 B2 antisym_onD refl_onD2)
qed

lemma lattice_absorb2: "\<lbrakk>poset R X; is_lattice R X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x,Sup R X {x, y}} = x"
proof-
  assume A0:"poset R X" "is_lattice R X"  "x \<in> X" "y \<in> X"
  obtain A1:" (is_inf_semilattice R X) \<and> (is_sup_semilattice R X)"  by (simp add: A0(2) lattice_sinf lattice_ssup)
  obtain B0:"(x, Sup R X {x, y}) \<in> R"by (meson A0(1) A0(3) A0(4) A1 bsup_geI1 refl_onD)  
  obtain B1:"(Inf R X {x,Sup R X {x, y}}, x) \<in> R" by (meson A0(1) A0(3) A0(4) A1 antisym_on_converse bsup_geI1 converseD refl_onD refl_on_converse ssupD4 trans_on_converse)
  obtain B2:"(x, Inf R X {x,Sup R X {x, y}}) \<in> R"by (meson A0(1) A0(3) A0(4) A1 B0 antisym_on_converse bsup_geI3 converseD converseI refl_onD refl_on_converse ssupD4 trans_on_converse) 
  show " Inf R X {x,Sup R X {x, y}} = x" by (meson A0(1) B1 B2 antisym_onD refl_on_domain) 
qed

lemma distrib_sup_le: "\<lbrakk>poset R X; is_lattice R X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {x, Inf R X {y, z}},  Inf R X {Sup R X {x, y}, Sup R X {x, z}}) \<in> R"  by (meson antisym_on_converse binf_geI3 binf_geI5 bsup_geI1 bsup_geI2 bsup_geI3 latt_iff refl_onD refl_on_converse ssupD4 trans_on_converse)
lemma distrib_inf_le: "\<lbrakk>poset R X; is_lattice R X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {Inf R X {x, y}, Inf R X {x, z}}, Inf R X {x, Sup R X {y, z}}) \<in> R" by (metis distrib_sup_le antisym_on_converse converseD converse_converse latt_iff refl_on_converse trans_on_converse)

lemma bsup_finite2:"\<lbrakk>poset R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup R X A (Sup R X A)" by (metis ssupD5 sup_equality)
lemma fsup_ub: "\<lbrakk>poset R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> ub R A (Sup R X A)"  by (meson bsup_finite2 is_supE2)
lemma fsup_lub:"\<lbrakk>poset R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> ubd R X A\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R" by (meson bsup_finite2 is_supE3)
lemma fsup_lub2:"\<lbrakk>poset R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> X;ub R A b\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R"  by (simp add: fsup_lub ubdI2)
lemma fsup_lub3:"\<lbrakk>poset R X; is_sup_semilattice R X;  A \<in> Fpow_ne X; b \<in> ubd R X A\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R"  by (metis Fpow_ne_iff2 fsup_lub)


lemma distibD1:
  assumes A0:"is_lattice R X" "poset R X" and
          A1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" and
          A2:" x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  obtain A3:"is_sup_semilattice R X" and A4:"is_inf_semilattice R X" by (simp add: assms(1) lattice_sinf lattice_ssup)
  have B0:"Sup R X {x, Inf R X {y, z}} = Sup R X {Sup R X {x, Inf R X {x, z}}, Inf R X {y, z}}"
    by (metis A2 A4 antisym_on_converse assms(2) binary_supI2 bsup_geI1 converse_iff refl_onD  ssupD4 sup_equality trans_on_converse)
  have B1:"... = Sup R X {x, Inf R X {z, Sup R X {x, y}}}"
    by (simp add: A1 A2 A3 A4 assms(2) bsup_assoc2 bsup_commute1 ssupD4)
  have B2:"... = Sup R X {Inf R X {Sup R X {x, y}, x}, Inf R X {Sup R X {x, y}, z}}"
    by (simp add: A0 A2 insert_commute lattice_absorb2)
  have B3:"... = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    by (simp add: A1 A2 A3 assms(2) ssupD4)
  show ?thesis
    by (simp add: B0 B1 B2 B3)
qed
  
lemma distribD2:
  assumes A0: "is_lattice R X" "poset R X"  and
          A1: "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" and
          A2: "x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
proof -
  obtain A3:"is_sup_semilattice R X" and A4:"is_inf_semilattice R X" by (simp add: assms(1) lattice_sinf lattice_ssup)
  have B0:"Inf R X {x, Sup R X {y, z}} = Inf R X {Inf R X {x, Sup R X {x, z}}, Sup R X {y, z}}"
    by (simp add: A0 A2 lattice_absorb2)
  have B1:"... = Inf R X {x, Sup R X {z, Inf R X {x, y}}}"
    by (smt (verit, best) A1 A2 A3 A4 assms(2) binf_assoc1 insert_commute ssupD4)
  have B2:"... = Inf R X {Sup R X {Inf R X {x, y}, x}, Sup R X {Inf R X {x, y}, z}}"
    by (simp add: A0 A2 insert_commute lattice_absorb1)
  have B3:"... = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    by (simp add: A1 A2 A4 assms(2) ssupD4)
  show ?thesis
    by (simp add: B0 B1 B2 B3)
qed



definition distributive_lattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where "distributive_lattice R X \<equiv> (is_lattice R X) \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<forall>z \<in> X. Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}})"
lemma distr_latticeD5:"distributive_lattice R X \<Longrightarrow> is_lattice R X" by (simp add: distributive_lattice_def)


definition is_cinf_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where  "is_cinf_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup (converse R) X A x))"

definition is_csup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where  "is_csup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup R X A x))"
definition is_clattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where "is_clattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>s. is_sup R X A s))"

lemma clatticeD1:
  assumes A0:"is_clattice R X"
  shows "(\<And>A. A \<subseteq> X \<Longrightarrow> (\<exists>i. is_inf R X A i))"
proof-
  fix A assume A1:"A \<subseteq> X" let ?L="lbd R X A"
  have B0:"?L \<subseteq> X"   by (simp add: ubd_sub)
  obtain i where B1:"is_sup R X ?L i"  by (meson B0 assms is_clattice_def)
  have B2:"is_inf R X A i"  by (metis A1 B1 bd_iso converse_converse is_supD31 is_supE1 is_supE2 is_supI4 ulbd_comp1)
  show "(\<exists>i. is_inf R X A i)"  using B2 by blast
qed
lemma clatticeD2:"is_clattice R X \<Longrightarrow> is_cinf_semilattice R X" by (simp add: clatticeD1 is_cinf_semilattice_def is_clattice_def)
lemma clatticeD3:"is_clattice R X \<Longrightarrow> is_csup_semilattice R X"  by (simp add: is_clattice_def is_csup_semilattice_def) 
lemma csuplatticeD1:"is_csup_semilattice R X \<Longrightarrow> is_sup_semilattice R X" by (simp add: is_csup_semilattice_def is_sup_semilattice_def) 
lemma cinflatticeD1:"is_cinf_semilattice R X \<Longrightarrow> is_inf_semilattice R X"by (simp add: csuplatticeD1 is_cinf_semilattice_def is_csup_semilattice_def) 

definition is_dir::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where "is_dir X R \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X.  (a, c) \<in> R \<and>  (b, c) \<in> R))"

definition is_ord_cl::"'a set \<Rightarrow> 'a set\<Rightarrow> 'a rel \<Rightarrow> bool" where "is_ord_cl X A R \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and>  (a, b) \<in> R \<longrightarrow> b \<in> A )"
definition is_filter::"'a rel \<Rightarrow> 'a set\<Rightarrow> 'a set \<Rightarrow> bool" where "is_filter R X F \<equiv> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (converse R)) \<and> is_ord_cl X F R"
definition is_ideal ::"'a rel \<Rightarrow> 'a set\<Rightarrow> 'a set \<Rightarrow> bool" where "is_ideal  R X I \<equiv> I \<noteq> {} \<and> I \<subseteq> X \<and> (is_dir I R) \<and> is_ord_cl X I (converse R)"

definition is_pfilter::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "is_pfilter R X A \<equiv> (is_filter R X A) \<and> X \<noteq> A"
definition is_pideal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "is_pideal R X A \<equiv> (is_ideal R X A) \<and> X \<noteq> A"

definition filter_closure::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where"filter_closure R X A \<equiv> if A={} then {Greatest R X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"

definition binary_filter_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow>'a set\<Rightarrow> 'a set \<Rightarrow> 'a set" where "binary_filter_sup R X A B = {x \<in> X. \<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x) \<in> R}"

definition lorc::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where "lorc R X a \<equiv> {y \<in> X. (a, y) \<in> R} "
abbreviation rolc where "rolc R X a \<equiv> lorc (converse R) X a"
definition ord_cl_sets::"'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set set" where "ord_cl_sets X R \<equiv> {A. A \<subseteq> X \<and> is_ord_cl X A R}"

definition up_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "up_cl R X A = {x \<in> X. \<exists>a \<in> A. (a, x) \<in> R}"

definition is_compact::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where"is_compact R X c \<equiv> c \<in> X \<and> (\<forall>A. A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R))"

definition compact_elements::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set" where "compact_elements R X \<equiv> {c. is_compact R X c}"

definition compactly_generated::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where "compactly_generated R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x))"

definition join_dense::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "join_dense R X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_sup R X Dx x)"
definition meet_dense::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "meet_dense R X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_inf R X Dx x)"

definition sup_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "sup_prime R X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup R X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"
definition inf_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "inf_prime R X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Inf R X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"


definition elem_sup_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "elem_sup_prime R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (x, Sup R X {a, b}) \<in> R \<longrightarrow> ((x,  a) \<in> R \<or> (x, b) \<in> R))"
definition elem_inf_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "elem_inf_prime R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (x, Inf R X {a, b}) \<in> R \<longrightarrow> ((a, x) \<in> R \<or> (b, x) \<in> R))"

definition fin_sup_irr::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where  "fin_sup_irr R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Sup R X {a, b} \<longrightarrow> (x = a \<or> x = b))" 
definition fin_inf_irr::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where   "fin_inf_irr R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Inf R X {a, b} \<longrightarrow> x = a \<or> x =b)"

definition meet_reducible::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where "meet_reducible R X x \<equiv> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf R X A x)"
abbreviation meet_irr where "meet_irr R X x \<equiv> \<not>(meet_reducible R X x)"

definition isotone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where "isotone Rx X Ry f \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1, x2) \<in> Rx \<longrightarrow> (f x1, f x2) \<in> Ry)"
abbreviation antitone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where "antitone Rx X Ry f \<equiv> isotone Rx X (converse Ry) f"

lemma isotoneI1:"(\<And>x1 x2. x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, x2) \<in> Rx \<Longrightarrow> (f x1, f x2) \<in> Ry) \<Longrightarrow> isotone Rx X Ry f" by (simp add: isotone_def)
lemma isotoneD1:"isotone Rx X Ry f \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, x2) \<in> Rx \<Longrightarrow> (f x1, f x2) \<in> Ry" by (simp add: isotone_def)
lemma isotone_sub:"isotone Rx X Ry f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> isotone Rx A Ry f"  by (simp add: isotone_def subset_iff) 
lemma isotone_emp:"isotone Rx {} Ry f" by(blast intro:isotoneI1)


definition extensive::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where "extensive R X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, f x) \<in> R)"
lemma extensiveI1:"(\<And>x. x \<in> X \<longrightarrow> (x, f x) \<in> R) \<Longrightarrow> extensive R X f" by (simp add:extensive_def)
lemma extensiveD1:"extensive R X f \<Longrightarrow> x \<in> X \<Longrightarrow> (x, f x) \<in> R" by (simp add:extensive_def)
lemma extensive_sub:"extensive R X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> extensive R A f" by (simp add: extensive_def in_mono) 
lemma extensive_emp:"extensive R {} f"  by (simp add: extensive_def) 

definition idempotent::"'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where "idempotent X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x)"

lemma idempotentI1[intro!]:"(\<And>x. x \<in> X \<longrightarrow> f (f x) = f x) \<Longrightarrow> idempotent X f" by (simp add:idempotent_def)


definition closure::" 'a rel \<Rightarrow> 'a set  \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow>  bool" where  "closure R X f \<equiv> extensive R X f \<and> idempotent X f \<and> isotone R X R f \<and> (f`X \<subseteq> X)"

definition closure_cond::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "closure_cond R X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<longrightarrow> x2 \<in> X \<longrightarrow> (x1, f x2) \<in> R \<longrightarrow> (f x1, f x2) \<in> R)"

lemma isotoneD31:  "\<lbrakk>isotone R X R f; ub R A b; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> ub R (f`A) (f b)  "  by (simp add: isotone_def subsetD ubE1 ub_imageI)

lemma isotoneD41:  "\<lbrakk>isotone R X R f; b \<in>ubd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> ubd R (f`X) (f`A)" by (simp add: isotoneD31 ubd_mem_iff)
lemma isotoneD51:  "\<lbrakk>isotone R  X R f; greatest R A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> greatest R (f`A) (f x)"  by (meson greatestD11 greatestD12 greatestI2 image_eqI isotoneD31 isotone_sub order_refl) 
lemma isotoneD61:  "\<lbrakk>isotone R  X R f; is_sup R X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> ub R (f`A) (f x)" by (simp add: is_supE1 is_supE2 isotoneD31) 
lemma extensiveD2:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f; ub R (f`X) b\<rbrakk> \<Longrightarrow> ub R X b" by(auto simp add:ub_def, meson extensiveD1 imageI refl_on_domain trans_onD)
lemma extensiveD3:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f; x \<in> X; y \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x, f y) \<in> R "  by (meson extensiveD1 refl_on_domain trans_onD)
lemma extensiveD4:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f;  x1 \<in> X; x2 \<in> X; (f x2) \<in> X; ( f x1, f x2) \<in> R\<rbrakk> \<Longrightarrow>( x1 , (f x2)) \<in> R"   by (meson extensiveD1 refl_onD1 trans_onD)
lemma extensive_ub_imp:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd R (f`X) (f`A) \<rbrakk> \<Longrightarrow> b \<in> ubd R X A" by(auto simp add:ubd_def ub_def, meson extensiveD4 imageI subset_eq)
lemma extensive_ub_imp2: "\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd R X (f`A)\<rbrakk> \<Longrightarrow> b \<in> ubd R X A" by(auto simp add:ubd_def ub_def,meson extensiveD1 extensive_sub imageI refl_on_domain trans_onD)
lemma is_iso_extD1:  "\<lbrakk>isotone R X R f; trans_on X R; antisym_on X R; refl_on X R; extensive R X f ; (f`X \<subseteq> X); x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x)) \<in> R"by (simp add: extensiveD1 image_subset_iff)
lemma is_iso_ebd:  "\<lbrakk>isotone R X R f; trans_on X R; antisym_on X R;  A \<subseteq> X; is_sup R X A x;  is_sup R (f`X) (f`A) y \<rbrakk> \<Longrightarrow> (y, f x) \<in> R"by (simp add: is_supD42 is_supE1 isotoneD61) 
lemma idempotentD1:  "\<lbrakk>idempotent X f; x \<in> X \<rbrakk> \<Longrightarrow>  f (f x) = f x" by (simp add: idempotent_def)
lemma idempotentD3:  "\<lbrakk>idempotent X f; y \<in> f`X \<rbrakk> \<Longrightarrow>  f y = y" by (auto simp add: idempotent_def)
lemma iso_idemD1:  "\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; isotone R X R f; idempotent X f; x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x)) \<in> R"  by (simp add: idempotentD1 isotoneD1 refl_onD)
lemma iso_idemD2: "\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; isotone R X R f; idempotent X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  (x1, f x2) \<in> R\<rbrakk> \<Longrightarrow> (f x1 , (f x2)) \<in> R"  by (metis (full_types) idempotent_def isotoneD1)
lemma iso_idemD3:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; isotone R X R f; idempotent X f; f`X \<subseteq> X; x1 \<in> X; x2 \<in> X;  (x1 ,f x2) \<in> R\<rbrakk> \<Longrightarrow> (f x1 , f x2) \<in> R"  by (simp add: image_subset_iff iso_idemD2)
lemma idemp_iff:  "idempotent X f \<longleftrightarrow> (\<forall>x \<in> X. (f \<circ> f) x = f x)"  using idempotent_def  by (metis comp_apply) 
lemma idempotentI2:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f; isotone R X R f;  f`X \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (f (f x), f x) \<in> R)\<rbrakk> \<Longrightarrow> idempotent X f" by (simp add: antisym_onD idempotentI1 image_subset_iff is_iso_extD1)
lemma idempotent_isotoneD1:  "\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; idempotent X f; isotone R X R f;  f`X \<subseteq> X;  y \<in> f`X;  x \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow>( f x, y) \<in> R"  by (metis idempotentD3 iso_idemD2 refl_onD2)
lemma isotoneI2: "\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f; closure_cond R X f\<rbrakk> \<Longrightarrow> isotone R X R f" by (simp add: closure_cond_def extensiveD3 isotone_def)
lemma idempotentI3:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; extensive R X f;  f`X \<subseteq> X; closure_cond R X f\<rbrakk> \<Longrightarrow> idempotent X f" by(rule_tac ?X="X" and  ?R="R" in idempotentI2, simp+, rule_tac ?X="X" and  ?R="R" in isotoneI2, simp+,simp add: closure_cond_def image_subset_iff refl_onD)
lemma closureI3:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R;extensive R X f; f`X \<subseteq> X;  closure_cond R X f\<rbrakk> \<Longrightarrow> closure R X f"  by (simp add: closure_def idempotentI3 isotoneI2)
lemma closureD1:"\<lbrakk>closure R X f;  x \<in> X\<rbrakk> \<Longrightarrow> f x \<in> X" by (simp add: image_subset_iff closure_def)
lemma closureD2:  "\<lbrakk>closure R X f;  y \<in> f`X\<rbrakk> \<Longrightarrow> y \<in> X" by (meson closure_def in_mono)
lemma closureD3:"\<lbrakk>trans_on X R; antisym_on X R; refl_on X R; closure R X f\<rbrakk> \<Longrightarrow> closure_cond R X f" apply(auto simp add:closure_cond_def)
proof-
  show " \<And>x1 x2.  trans_on X R \<Longrightarrow> antisym_on X R \<Longrightarrow> refl_on X R \<Longrightarrow> closure R X f \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, f x2) \<in> R \<Longrightarrow> (f x1, f x2) \<in> R"
  proof-
    fix x1 x2 assume A:"trans_on X R" "antisym_on X R"  "refl_on X R""closure R X f" "x1 \<in> X" "x2 \<in> X" "(x1, f x2) \<in> R" 
    show "(f x1, f x2) \<in> R"by (meson A closureD1 closure_def iso_idemD2)
  qed
qed


definition closure_range::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "closure_range R X C\<equiv> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. least R  (ubd R C {x}) c))"
abbreviation clr where "clr R X C \<equiv> closure_range R X C"

lemma clrI1:"C \<subseteq> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. least R (ubd R C {x}) c)) \<Longrightarrow> clr R X C" by(simp add:closure_range_def)
lemma clrI2:"C \<subseteq> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_sup R C {x} c)) \<Longrightarrow> clr R X C"by (simp add: closure_range_def is_sup_def) 
lemma clrD1: "clr R X C \<Longrightarrow> C \<subseteq> X"  by(simp add:closure_range_def) 
lemma clrD2:"clr R X C \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. least R (ubd R C {x}) c))"by (simp add:closure_range_def)
lemma clrD3:"clr R X C \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_sup R C {x} c))"  by (simp add: clrD2 is_sup_def)
lemma clrD4:"clr R X C \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow>(ubd R C {x}) \<noteq> {})"  by (metis clrD2 empty_iff greatestD11) 
lemma clrD5:"clr R X C \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c \<in> C. (x, c) \<in> R))" by (meson clrD3 is_supD1121 is_supE1 singletonI) 
definition closure_from_closure_range::"'a rel \<Rightarrow> 'a set \<Rightarrow>('a \<Rightarrow> 'a)" where"closure_from_closure_range R C \<equiv> (\<lambda>x. THE c.  least R  (ubd R C {x}) c)"
abbreviation cl where "cl R C \<equiv> closure_from_closure_range R C"
lemma cl_ex:"antisym_on X R \<Longrightarrow> clr R X C \<Longrightarrow> x \<in> X \<Longrightarrow>  least R  (ubd R C {x}) ((cl R C) x)"
proof-
  assume A:"antisym_on X R" " clr R X C" "x \<in> X "
  obtain c where B:"least R (ubd R C {x}) c" by (meson A(2,3) clrD2)
  have B1:"cl R C x = c"  by (metis A(1,2) B Ord4.Greatest_def antisym_on_converse antisym_on_subset closure_from_closure_range_def clrD1 greatest_equality2 ubd_sub) 
  show "least R  (ubd R C {x}) ((cl R C) x)"  using B B1 by blast 
qed

lemma cl_extensive:"antisym_on X R \<Longrightarrow> trans_on X R \<Longrightarrow> clr R X C \<Longrightarrow> extensive R X (cl R C)"by (meson cl_ex extensive_def greatestD11 ub_singletonI ubdD3) 


lemma cl_lt_ub1:"antisym_on X R \<Longrightarrow> trans_on X R \<Longrightarrow>  clr R X C \<Longrightarrow> x \<in> X \<Longrightarrow>c \<in> (ubd R C {x}) \<Longrightarrow> ((cl R C) x,  c) \<in> R" by (meson cl_ex is_supE3 is_supI1) 
lemma cl_lt_ub2:"antisym_on X R \<Longrightarrow> trans_on X R \<Longrightarrow>  clr R X C \<Longrightarrow> x \<in> X \<Longrightarrow>c \<in> C \<Longrightarrow> (x, c) \<in> R \<Longrightarrow> ((cl R C) x,  c) \<in> R" by (simp add: cl_lt_ub1 ubd_singleton2)  

lemma cl_isotone:"antisym_on X R \<Longrightarrow> trans_on X R \<Longrightarrow> refl_on X R \<Longrightarrow> clr R X C \<Longrightarrow> isotone R X R (cl R C)"  by(auto simp add:isotone_def,meson cl_ex cl_extensive cl_lt_ub2 extensiveD3 is_supE1 is_supI1)

lemma subdiag:"refl_on X R \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, a) \<in> R)" by (simp add: in_mono refl_onD)

definition refl where "refl X R \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, x) \<in> R)"

lemma reflI:"(\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> R) \<Longrightarrow> refl X R" by (simp add:refl_def)
lemma reflE:"refl X R\<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> R)" by (simp add:refl_def)


lemma cl_idempotent:"antisym_on X R \<Longrightarrow> trans_on X R \<Longrightarrow> refl_on X R \<Longrightarrow> clr R X C \<Longrightarrow> idempotent X (cl R C)"  
  apply(auto simp add: idempotent_def)
proof-
  show "\<And>x. antisym_on X R \<Longrightarrow> trans_on X R \<Longrightarrow> refl_on X R \<Longrightarrow> clr R X C \<Longrightarrow> x \<in> X \<Longrightarrow> cl R C (cl R C x) = cl R C x"
  proof-
    fix x assume A:"antisym_on X R" "trans_on X R" "refl_on X R" "clr R X C" "x \<in> X" 
    obtain B0:"antisym_on C R"  and B1:"cl R C x \<in> C"  by (meson A(1,4,5) antisym_on_subset cl_ex clrD1 is_supE1 is_supI1)
    then have B2:"least R (ubd R C {(cl R C x)}) (cl R C x)"   by (meson A(1,2,4,5) cl_extensive cl_lt_ub2 extensiveD1 is_supD1 sup_singleton)
    then show "cl R C (cl R C x) = cl R C x"  by (meson A(1,3,4) B0 antisym_on_converse antisym_on_subset cl_ex greatestD11 greatest_unique2 refl_on_domain ubd_singleton_iff ubd_sub)
  qed
qed

lemma cl_ext1:"\<lbrakk>antisym_on X R; trans_on X R;  clr R X C; x \<in> X\<rbrakk> \<Longrightarrow> (x, (cl R C) x) \<in> R"  by (meson cl_extensive extensiveD1)


lemma cl_lt_ub:"\<lbrakk>closure R X f; x \<in> X; y \<in> ubd R (f`X) {x}\<rbrakk> \<Longrightarrow> (f x, y) \<in> R"  by (metis closureD2 closure_def idempotentD3 isotoneD1 ubd_singleton_iff) 
lemma cl_lt_cl:"\<lbrakk>closure R X f; x \<in> X\<rbrakk> \<Longrightarrow> least R (ubd R (f`X) {x}) (f x)" by(rule greatestI3, simp add: cl_lt_ub, simp add: closure_def extensive_def ubd_singleton2)
lemma clinduce:"\<lbrakk>closure R X f; X \<noteq> {}\<rbrakk> \<Longrightarrow> clr R X (f`X)"   by (meson cl_lt_cl closure_def clrI1)
lemma ind_clid:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; f`X \<subseteq> X; closure R X f; X \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> (cl R (f`X)) x = f x" by (meson antisym_on_subset cl_ex cl_lt_cl clinduce is_sup_unique sup_emptyI ubd_sub)
lemma extensiveI4:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; (\<And>A s. \<lbrakk>A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> (s, f s) \<in> R); f`X \<subseteq> X\<rbrakk> \<Longrightarrow> extensive R X f" by (meson extensive_def lb_single_greatest1 sup_maxE2 ubd_sub) 
lemma idempotentI4:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; (\<And>A s1 s2. \<lbrakk>A \<subseteq> X; is_sup R X A s1; is_sup R X (f`A) s2\<rbrakk> \<Longrightarrow> f s1 = f s2); f`X \<subseteq> X\<rbrakk> \<Longrightarrow> idempotent X f"   apply(rule idempotentI1)
proof
  fix x assume A0:"antisym_on X R" "trans_on X R" "refl_on X R"  "(\<And>A s1 s2. \<lbrakk>A \<subseteq> X; is_sup R X A s1; is_sup R X (f`A) s2\<rbrakk> \<Longrightarrow> f s1 = f s2)" "f`X \<subseteq> X" "x \<in> X"
  let ?A="{x}"
  obtain B0:"?A \<subseteq> X" and B1:"is_sup R X ?A x" and B2:"is_sup R X (f`?A) (f x)" by (metis A0(3,5,6) empty_subsetI image_empty image_insert image_subset_iff insert_subsetI refl_onD sup_singleton)  
  show "f (f x) = f x"  by (metis A0(4) B0 B1 B2)  
qed

lemma isotoneI4:
    assumes A0:"antisym_on X R" "trans_on X R" "refl_on X R" and A1:"f`X \<subseteq> X" and A2:"(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s))"
    shows "isotone R X R f"  apply(rule isotoneI1)
proof-
  fix x1 x2 assume A3:"x1 \<in> X" "x2 \<in> X" "(x1, x2) \<in> R"
  have B0:"{x1, x2} \<subseteq> X"  by (simp add: A3)
  obtain B0:"is_sup R X {x1, x2} x2" by (meson A3 A0(3) binary_supI1 refl_onD) 
  obtain B1:"is_sup R (f`X) (f`{x1, x2}) (f x2)" by (meson A2 A3(1,2) B0 empty_subsetI insert_subsetI) 
  show "(f x1, f x2) \<in> R"by (meson B1 fbdE1 insertI1 is_supE2) 
qed

lemma clrD8:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R;clr R X C; A \<subseteq> C; is_inf R X A i\<rbrakk> \<Longrightarrow> (cl R C) i \<in> lbd R X A" by(auto simp add:ubd_def,meson cl_extensive extensiveD1 is_supE1 refl_on_domain,meson cl_lt_ub2 converse.cases converseI is_supD1121 is_supE1 subsetD ubI1)
lemma clrD9:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R;clr R X C; A \<subseteq> C; is_inf R X A i\<rbrakk> \<Longrightarrow> (cl R C i, i) \<in> R" by (meson clrD8 converse.simps is_supE3) 
lemma clrD10:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R;clr R X C; A \<subseteq> C; is_inf R X A i\<rbrakk> \<Longrightarrow> cl R C i = i" by (meson antisym_on_def cl_extensive clrD9 extensiveD1 is_supE1 refl_onD1)
lemma clrD11:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R;clr R X C; A \<subseteq> C; is_inf R X A i\<rbrakk> \<Longrightarrow> i \<in> C" by (metis cl_ex clrD10 greatest_iff is_supE1 ubd_mem_iff) 

definition powrel where "powrel X \<equiv> {(A, B). A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B}"
lemma powrel1:"antisym_on (Pow X) (powrel X)"  by(auto simp add:antisym_on_def powrel_def)
lemma powrel2:"trans_on (Pow X) (powrel X)"  by(auto simp add:trans_on_def powrel_def)
lemma powrel3:"refl_on (Pow X) (powrel X)"  by(auto simp add:refl_on_def powrel_def)
lemma powrel4:"A \<subseteq> Pow X \<Longrightarrow> is_inf (powrel X) (Pow X) A (X \<inter>(\<Inter>A))"  apply(auto simp add:is_sup_def greatest_def ubd_def ub_def)  using powrel_def apply fastforce  by (simp add: Inf_greatest powrel_def)
lemma powrel5:"A \<subseteq> Pow X \<Longrightarrow> is_sup (powrel X) (Pow X) A (\<Union>A)" by(auto simp add:is_sup_def greatest_def ubd_def ub_def powrel_def)
lemma powrel6:"C \<subseteq> Pow X \<Longrightarrow> antisym_on C (powrel X)"  by (meson antisym_on_subset powrel1)
lemma powrel7:"C \<subseteq> Pow X \<Longrightarrow> trans_on C (powrel X)"  by (meson powrel2 trans_on_subset)  
lemma powrel8:"(x, y) \<in> powrel X \<Longrightarrow> x \<subseteq> y"  by (simp add: powrel_def) 

lemma uni_sup_fam:"\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Union>A \<in> S\<rbrakk> \<Longrightarrow> is_sup (powrel X) S A (\<Union>A)" by(auto simp add:is_sup_def greatest_def ubd_def ub_def powrel_def)

lemma moore_clI1:"\<lbrakk>C \<subseteq> Pow X;(\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C); x \<in> Pow X\<rbrakk> \<Longrightarrow> least (powrel X) (ubd (powrel X) C {x}) (X \<inter> (\<Inter>(ubd (powrel X) C {x})))"by(auto simp add:greatest_def ubd_def ub_def powrel_def)
  
lemma moore_clI2:"\<lbrakk>C \<subseteq> Pow X;(\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C)\<rbrakk> \<Longrightarrow> clr (powrel X) (Pow X) C"  by (meson clrI1 moore_clI1)
lemma moore_clI3:"\<lbrakk>C \<subseteq> Pow X; X \<in> C;(\<And>E. E \<subseteq> C \<Longrightarrow> E \<noteq> {}  \<Longrightarrow> (\<Inter>E) \<in> C)\<rbrakk> \<Longrightarrow> clr (powrel X) (Pow X) C" by (metis Inter_insert empty_not_insert insert_subsetI moore_clI2)
lemma cl_sup_bds:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; closure R X f; is_sup R X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s \<in> ubd R (f`X) (f`A)"  by (simp add: closure_def is_supD32 isotoneD41) 
lemma cl_inf_bds:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; closure R X f; is_inf R X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s \<in> lbd R (f`X) (f`A)" by (simp add: closure_def is_supD32 isotoneD41 isotone_def) 
lemma cl_sup_lbd:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; closure R X f; is_sup R X A s; A \<subseteq> X; b \<in> ubd R (f`X) (f`A)\<rbrakk> \<Longrightarrow> (f s, b) \<in> R" by (meson closure_def extensive_ub_imp idempotent_isotoneD1 is_supE1 is_supE3 ubdD2) 
lemma cl_sup_sup:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; closure R X f; is_sup R X A s; A \<subseteq> X; b \<in> ubd R (f`X) (f`A)\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s)"by (simp add: cl_sup_bds cl_sup_lbd is_supI5)  
lemma cl_sup_eq1:"\<lbrakk>antisym_on X R; trans_on X R; refl_on X R; closure R X f;  A \<subseteq> X; is_sup R X A s1; is_sup R X (f`A) s2 \<rbrakk> \<Longrightarrow> f s1 = f s2" 
proof-
  assume A0:"antisym_on X R" "trans_on X R" "refl_on X R" "closure R X f" " A \<subseteq> X" "is_sup R X A s1"  "is_sup R X (f`A) s2"
  obtain B0:"(s1, s2) \<in> R" by (meson A0  closure_def extensive_ub_imp2 is_supD32 is_supE3)  
  obtain B1:"(s2, f s1) \<in> R" by (meson A0(4-7)  closureD1 closure_def is_supE1 is_supE2 is_supE4 isotoneD31)  
  obtain B2:"(f s2, f s1) \<in> R" by (meson A0(1-4) B0 B1 closure_def iso_idemD2 refl_onD1 refl_onD2)
  obtain B3:"(f s1, f s2) \<in> R" by (meson A0(3-4) B0 closure_def isotoneD1 refl_onD1 refl_onD2)
  then show "f s1 = f s2" by (meson A0(1,3) B2 antisym_onD refl_onD2)
qed


definition filters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where "filters_on R X \<equiv> {F. is_filter R X F}"

definition pfilters::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where "pfilters R X \<equiv> {F. is_pfilter R X F}"


lemma clr_cinf_semilattice1:"\<lbrakk>clr R X C; is_cinf_semilattice R X; poset R X\<rbrakk> \<Longrightarrow>(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R C A x \<and> is_inf R X A x))" by (meson  clrD1 clrD11 is_cinf_semilattice_def subset_trans sup_in_subset)


lemma clr_clattice1:
  assumes A0:"clr R X C" and A1:"is_clattice R X" and A2:"poset R X"
  shows "\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"
proof-
  fix A assume A3:"A \<subseteq> C" obtain B0:"A \<subseteq> X" using A0 A3 clrD1 by blast
  have B1:"ubd R C A \<subseteq> C" by (simp add: ubd_sub)
  have B2:"ubd R C A \<subseteq> X"  using A0 B1 clrD1 by blast
  have B3:"is_cinf_semilattice R X" by (simp add: A1 clatticeD2)
  obtain x where B4:" is_inf R C (ubd R C A) x \<and> is_inf R X (ubd R C A) x"   by (meson A0 A1 A2 B1 B2 clatticeD1 clrD1 clrD11 sup_in_subset) 
  have B5:"is_sup R C A x"  by (meson A3 B4 sup_inf_ub) 
  show "(\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"  using B4 B5 by blast
qed

lemma clr_is_clattice:"\<lbrakk>poset R X; clr R X C; is_clattice R X\<rbrakk> \<Longrightarrow> is_clattice R C" by (metis clrD5 clr_clattice1 empty_iff is_clattice_def subsetI sup_iff2)

lemma closure_range_is_clattice: "\<lbrakk>poset R X; closure R X f; is_clattice R X\<rbrakk> \<Longrightarrow> is_clattice R (f`X)" using clinduce clr_is_clattice is_clattice_def by blast

lemma is_dirE1:"is_dir X R  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. (a, c) \<in> R \<and> (b, c) \<in> R) "  by (simp add: is_dir_def)
lemma is_dirI1: "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. (a, c) \<in> R \<and> (b, c) \<in> R)) \<Longrightarrow> is_dir X R" by (simp add: is_dir_def)
lemma is_dirD1: "\<lbrakk>is_dir X R ;a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. ub R {a, b} c)"by (metis bdinsert4 is_dirE1 ub_singletonD)
lemma is_dir_empty: "is_dir {} R"  by (simp add: is_dir_def)
lemma is_dir_singleton: "(x, x) \<in> R \<Longrightarrow> is_dir {x} R"  by (simp add: is_dir_def)

lemma updir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. (a1, c) \<in>R \<and> (a2, c) \<in> R)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"poset R X"
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> (a, c) \<in> R)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 by auto 
next
  case (insert x F) 
  obtain c where B0:"c \<in> X" "\<forall>a. a \<in> F \<longrightarrow> (a, c) \<in> R"  using insert.hyps(4) insert.prems by blast
  obtain d where B1:"d \<in> X" "(c, d) \<in> R" "(x, d) \<in> R"    by (meson A0 \<open>(c::'a::type) \<in> (X::'a::type set)\<close> insert.prems insert_subset)
  have B2:"\<And>a. a \<in> (insert x F) \<Longrightarrow> (a, d) \<in> R"
  proof-
    fix a assume A5: "a \<in> (insert x F)" 
    show "(a, d) \<in> R"
    proof(cases "a \<in> F")
      case True then show ?thesis  by (meson A4 B0 B1 A5 in_mono insert.prems trans_onD)
    next
      case False then have B20:"a=x" using A5 by fastforce then show ?thesis    by (simp add: B1(3)) 
    qed
  qed
  then show ?case  using B1(1) by blast 
qed

lemma updir_finite2: "\<lbrakk>poset R X; is_dir X R; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c)" by (metis is_dir_def ubI1 updir_finite1)
lemma updir_finite3: "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c)) \<Longrightarrow> is_dir X R"apply(auto simp add:ub_def is_dir_def) by (metis bot_least finite.simps insert_iff insert_not_empty insert_subset)
lemma updir_finite: "poset R X \<Longrightarrow> is_dir X R \<longleftrightarrow> (\<forall>A. A \<subseteq> X \<and> finite A \<and> A \<noteq> {} \<longrightarrow>  (\<exists>c \<in> X. ub R A c))"by (meson updir_finite2 updir_finite3)
lemma ssup_pair_ub: "\<lbrakk>poset R X; is_sup_semilattice R X; a \<in> X; b \<in> X\<rbrakk>  \<Longrightarrow>\<exists>c. c \<in> X \<and> (a, c) \<in> R \<and>  (b, c) \<in> R"  by(rule_tac ?x="Sup R X {a, b}" in exI, simp add:bsup_geI1 bsup_geI2 ssupD4,metis bsup_geI1 bsup_geI2 refl_onD)
lemma sup_dir:"\<lbrakk>poset R X; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> is_dir X R"using is_dir_def ssup_pair_ub by fastforce

lemma updir_finite_obtain:  assumes A0:"is_dir X R" and A1:"A \<in> Fpow_ne X" and A2:"poset R X"   obtains c where "c \<in> X \<and> ub R A c"   by (metis A0 A1 A2 Fpow_ne_iff2 updir_finite2)


lemma is_ord_clE1:"is_ord_cl X A R  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> (a, b) \<in> R \<Longrightarrow> b \<in> A " by (simp add:is_ord_cl_def)
lemma is_ord_clI1: "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; (a, b) \<in> R\<rbrakk> \<Longrightarrow> b \<in> A ) \<Longrightarrow> is_ord_cl X A R"  by (auto simp add:is_ord_cl_def)
lemma is_ord_empty:"is_ord_cl X {} R " by (simp add: is_ord_cl_def)
lemma is_ord_cl_space: "is_ord_cl X X R "  by (simp add: is_ord_cl_def)
lemma is_ord_cl_comp1:"is_ord_cl X  A R \<Longrightarrow> is_ord_cl X(X-A) (converse R)" by(auto simp add:is_ord_cl_def)
lemma is_ord_cl_comp2:  "A \<subseteq> X \<Longrightarrow> is_ord_cl X (X-A) (converse R) \<Longrightarrow> is_ord_cl X A R" by(auto simp add:is_ord_cl_def)
lemma is_ord_cl_iff_comp: "A \<subseteq> X \<Longrightarrow> is_ord_cl X A R \<longleftrightarrow> is_ord_cl X (X-A) (converse R) " using is_ord_cl_comp1 is_ord_cl_comp2 by blast
lemma is_ord_cl_un: "A \<in> (Pow (Pow (X::'a set))) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a R) \<Longrightarrow>  is_ord_cl X (\<Union>A) R "  apply(simp add:is_ord_cl_def) by metis
lemma is_ord_cl_in:  "A \<in> (Pow (Pow (X::'a set))) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a R) \<Longrightarrow>  is_ord_cl X (\<Inter>A) R "  apply(simp add:is_ord_cl_def) by metis
lemma is_ord_cl_un2: "A \<in> (Pow (Pow (X::'a set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a R) \<Longrightarrow>  is_ord_cl X (\<Union>A) R "  by (simp add: is_ord_cl_un)
lemma is_ord_cl_in2:  "A \<in> (Pow (Pow (X::'a set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a R) \<Longrightarrow>  is_ord_cl X (\<Inter>A) R "  by (simp add: is_ord_cl_in)

lemma is_ord_cl_un3: "(f`I)\<in> (Pow (Pow (X::'a set))) \<and> (\<forall>i. i \<in> I \<longrightarrow> is_ord_cl X (f i) R) \<Longrightarrow>  is_ord_cl X (\<Union>i \<in> I. f i) R " apply (rule un_to_ind_un[of "(\<lambda>A. A \<in> (Pow (Pow (X::'a set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a R))"  "\<lambda>B. is_ord_cl X B R" "f" "I"]) apply (simp add: is_ord_cl_un)  by blast
lemma is_ord_cl_in3:  "(f`I)\<in> (Pow (Pow (X::'a set))) \<and> (\<forall>i. i \<in> I \<longrightarrow> is_ord_cl X (f i) R) \<Longrightarrow>  is_ord_cl X (\<Inter>i \<in> I. f i) R "  apply (rule int_to_ind_int[of "(\<lambda>A. A \<in> (Pow (Pow (X::'a set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a R))"  "\<lambda>B. is_ord_cl X B R" "f" "I"]) apply (simp add: is_ord_cl_in)  by blast
lemma ord_cl_memI1:  "is_ord_cl (X::'a set) A R \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a. a \<in> A \<and>  (a, x) \<in> R) \<Longrightarrow> x \<in> A"  by(auto simp add:is_ord_cl_def)

lemma ord_cl_dwdir_inf:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A (converse R)" and A2:"is_ord_cl X A R"
  shows "\<And>a b. (a \<in> A \<and> b \<in> A \<and>  is_inf R X {a, b} i) \<longrightarrow> (i \<in> A)"
proof
  fix a b assume A3:" (a \<in> A \<and> b \<in> A \<and> is_inf R X {a, b} i)"
  obtain c where B0:"c \<in> A \<and> (c, a) \<in> R \<and> (c, b) \<in> R" by (meson A1 A3 converseD is_dirE1)
  have B1:"lb R {a, b} c"  by (simp add: B0 ub_def)
  have B2:"(c, i) \<in> R"    by (meson A0 A3 B0 B1 converseD in_mono is_supE4)
  show "i \<in> A"    by (meson A2 A3 B0 B2 is_ord_clE1 is_supE1)
qed


lemma ord_cl_updir_sup:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A R" and A2:"is_ord_cl X A (converse R)"
  shows "\<And>a b. (a \<in> A \<and> b \<in> A \<and>  is_sup R X {a, b} i) \<longrightarrow> (i \<in> A)"
  by (metis A0 A1 A2 converse_converse ord_cl_dwdir_inf)

lemma up_cl_bot:
  "\<lbrakk>least R X bot; A \<subseteq>X; is_ord_cl X A R; bot \<in> A\<rbrakk> \<Longrightarrow> A=X"
  by (meson converseD greatestD12 is_ord_cl_def subset_antisym subset_eq ubE1)


lemma compactI:"\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R))\<rbrakk> \<Longrightarrow> is_compact R X c"  by(simp add:is_compact_def)

lemma compactD: "\<lbrakk>is_compact R X c; A \<in> Pow_ne X; (c, Sup R X A) \<in> R\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R)" by(simp add:is_compact_def)

lemma compact_element_memD1:"x \<in> compact_elements R X  \<Longrightarrow> is_compact R X x" by (simp add: compact_elements_def)
lemma compactD2:"is_compact R X x \<Longrightarrow> x \<in> X" by (simp add: is_compact_def)
lemma compact_element_memD2:"x \<in> compact_elements R X  \<Longrightarrow> x \<in> X" by (meson compactD2 compact_element_memD1) 
lemma compact_elements_sub:"compact_elements R X \<subseteq> X"  by (simp add: compact_element_memD2 subsetI) 
lemma compact_elements_mem_iff1: "x \<in> compact_elements R X \<longleftrightarrow> is_compact R X x" by (simp add: compact_elements_def)
lemma compactly_generatedD1: "compactly_generated R X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x)"  by(simp add:compactly_generated_def)

lemma compactly_generatedI1:  "(\<And>x. x \<in> X \<Longrightarrow>  (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x)) \<Longrightarrow> compactly_generated R X"  by(simp add:compactly_generated_def)


lemma join_denseD1:"\<lbrakk>join_dense R X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_sup R X Dx x)" by (simp add:join_dense_def)
lemma meet_denseD1:"\<lbrakk>meet_dense R X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_inf R X Dx x)" by (simp add:meet_dense_def)

lemma cjoin_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice R X; poset R X\<rbrakk> \<Longrightarrow> (join_dense R X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Sup R X Dx))" 
 apply(auto) using join_denseD1 sup_equality apply metis by(auto simp add:join_dense_def, metis PowD Pow_mono in_mono is_clattice_def sup_equality)

lemma cmeet_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice R X; poset R X\<rbrakk> \<Longrightarrow> (meet_dense R X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Inf R X Dx))"  
 apply(auto) using meet_denseD1 sup_equality  apply (metis antisym_on_converse  trans_on_converse) by(auto simp add:meet_dense_def, metis PowD antisym_on_converse clatticeD1  subset_trans sup_equality trans_on_converse)

lemma join_denseD2:"\<lbrakk>poset R X; join_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Sup R X (rolc R D x))"
proof-
  assume P:"poset R X" "join_dense R X D" "D \<subseteq> X" 
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

lemma join_denseI2:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X (rolc R D x) x) \<rbrakk> \<Longrightarrow> join_dense R X D"  by (metis (no_types, lifting) Pow_iff join_dense_def lorc_def mem_Collect_eq subset_eq) 
lemma meet_denseD2:"\<lbrakk>poset R X; meet_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf R X (lorc R D x))" by (metis antisym_on_converse converse_converse join_denseD2 join_dense_def meet_dense_def refl_on_converse trans_on_converse)
lemma meet_denseI2:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf R X (lorc R D x) x) \<rbrakk> \<Longrightarrow> meet_dense R X D" by (simp add: join_denseD1 join_denseI2 meet_dense_def) 
lemma compactly_generated_iff:"compactly_generated R X \<longleftrightarrow> join_dense R X (compact_elements R X)" by(auto simp add:compactly_generated_def join_dense_def)

lemma sub_antisym:"antisym_on X R \<Longrightarrow> A \<subseteq> X \<Longrightarrow> antisym_on A (R \<inter> (A \<times> A))" by (meson IntD1 antisym_on_def in_mono)
lemma sub_trans:"trans_on X R \<Longrightarrow> A \<subseteq> X \<Longrightarrow> trans_on A (R \<inter> (A \<times> A))" by(auto simp add:trans_on_def)
lemma sub_refl:"refl_on X R \<Longrightarrow> A \<subseteq> X \<Longrightarrow> refl_on A (R \<inter> (A \<times> A))" by(auto simp add:refl_on_def)


lemma subposet1:"poset R A \<Longrightarrow> poset (R \<inter> (A \<times> A)) A" by(auto,simp add: refl_on_def, simp add: le_iff_inf refl_on_def,simp add: le_iff_inf refl_on_def)
lemma subposet2:"poset R X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> poset (R \<inter> (A \<times> A)) A" by (metis sub_antisym sub_refl sub_trans) 
lemma sub_dir:"is_dir A R \<Longrightarrow> is_dir A (R \<inter> (A \<times> A))" by (simp add: is_dir_def)

(*
  in a csup semilattice an element is compact iff directed coverings contain an upper bound
*)


lemma compactD1: "\<lbrakk>poset R X; is_compact R X c; A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>A0. \<exists>a. a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"
proof-
  assume A0:"poset R X" "is_compact R X c" "A \<in> Pow_ne X" "(c, Sup R X A) \<in> R" "is_dir A R"
  obtain A0 where B0:"A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"  by (meson A0(2) A0(3) A0(4) compactD)
  have B1:"A \<subseteq> X"  using A0(3) by auto
  have B2:"poset (R \<inter> (A \<times> A)) A"  using A0(1) B1 subposet2 by blast 
  have B3:"is_dir A (R \<inter> (A \<times> A))"   by (simp add: A0(5) sub_dir)
  obtain a where B4:"a \<in> A \<and> ub ((R \<inter> (A \<times> A))) A0 a"  using B0 B2 B3 updir_finite_obtain by blast
  show "(\<exists>A0. \<exists>a. a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"
    by (meson B0 Int_iff \<open>\<And>thesis::bool. (\<And>a::'a::type. a \<in> (A::'a::type set) \<and> ub (Restr (R::('a::type \<times> 'a::type) set) A) (A0::'a::type set) a \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> ub_iff1)
qed

lemma ccompact0:
  assumes A0:"is_sup_semilattice R X" and
          A1:"is_compact R X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"(c, Sup R X A) \<in> R" and
          A4:"is_dir A R" and 
          A5:"poset R X"
  shows "\<exists>a \<in> A. (c, a) \<in> R"
proof-
  obtain A0 a where A5:"a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"  by (meson A1 A2 A3 A4 A5 compactD1)
  have A7:"a \<in> ubd R X A0" by (meson A4 A5 assms(6) is_dirE1 refl_on_domain ubdI2)
  have B0:"(Sup R X A0, a) \<in> R" by (meson A0 A2 A5 A7 Fpow_ne_iso Pow_ne_iff assms(6) fsup_lub3 in_mono) 
  have B1:"(c, a) \<in> R" by (meson A5 B0 assms(6) refl_onD1 refl_onD2 trans_onD)
  show ?thesis using A5 B1 by blast
qed


definition fne_sup_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow>  'a set" where
  "fne_sup_cl R X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x}"


lemma fne_sup_cl_imp1: "x \<in> fne_sup_cl R X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x)" by (simp add: fne_sup_cl_def)
lemma fne_sup_cl_obtains:  assumes "x \<in> fne_sup_cl R X A"  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup R X F x"  by (meson assms fne_sup_cl_imp1)

lemma fne_sup_cl_extensive:"\<lbrakk>A \<subseteq> X; poset R X\<rbrakk> \<Longrightarrow> A \<subseteq> fne_sup_cl R X A"
proof-
  assume A0:"A \<subseteq> X" "poset R X"
  show "A \<subseteq> fne_sup_cl R X A"
  proof
  fix a assume A1: "a \<in> A"
  have B0: "is_sup R X {a} a" by (meson A0 A1 refl_on_domain subdiag sup_singleton)
  have B2: "{a} \<in> Fpow A"  by (simp add: A1 Fpow_def)
  show "a \<in> fne_sup_cl R X A"
    apply(auto simp add:fne_sup_cl_def)
    using A0(1) A1 apply blast
    using B0 B2 by blast
  qed
qed


lemma fne_sup_cl_ext:
  "poset R X \<Longrightarrow> extensive (powrel X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
  apply(auto simp add:extensive_def powrel_def)
  apply (meson fne_sup_cl_imp1 is_supE1)
  using fne_sup_cl_extensive by blast

lemma fne_sup_cl_isotone:
  "\<lbrakk>poset R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X B"
  apply(auto simp add:fne_sup_cl_def) by (metis Fpow_mono empty_iff subsetD)
           

lemma fne_sup_cl_iso:
  "poset R X \<Longrightarrow> isotone (powrel X) (Pow X) (powrel X) (\<lambda>A. fne_sup_cl R X A)"
  apply(auto simp add:isotone_def powrel_def)
  apply (meson fne_sup_cl_imp1 is_supE1)
  apply (meson fne_sup_cl_imp1 is_supE1)
  using fne_sup_cl_isotone by blast

lemma fne_sup_cl_if1:"\<lbrakk>poset R X; x \<in> X; (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_sup R X F x)\<rbrakk> \<Longrightarrow> x \<in> fne_sup_cl R X A" by (simp add: fne_sup_cl_def)



lemma fne_sup_cl_idempotent0: "\<lbrakk>poset R X; s \<in> fne_sup_cl R X (fne_sup_cl R X A)\<rbrakk> \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_sup_cl R X A) \<and> E \<noteq> {} \<and> is_sup R X E s)"  by (meson fne_sup_cl_imp1)
lemma fne_sup_cl_idempotent1:  "\<lbrakk>poset R X; E \<in> Pow (fne_sup_cl R X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_sup R X Ex x)" by (meson PowD in_mono fne_sup_cl_imp1)
lemma fne_sup_cl_idempotent2:  "poset R X \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X (fne_sup_cl R X A)"  by (metis fne_sup_cl_extensive fne_sup_cl_imp1 subsetI sup_iff2)


lemma fne_sup_cl_idempotent:
  assumes A0:"poset R X"
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
      have B00:"((\<lambda>Ai. Sup R X Ai)`?fE) = ?S" apply(auto)   by (metis (mono_tags, lifting) B0 assms is_supE1 someI_ex sup_equality)
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
            fix s assume B6A1:"s \<in> E" show "s \<in> ?S"  by (metis (no_types, lifting) B00 B1 B6A1 assms image_eqI sup_equality)
        qed
      qed
      obtain se where B11A0:"is_sup R X E se"   using P1 by blast
      obtain ss where B11A1:"is_sup R X ?S ss"   using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup R X Ai si)"  using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup R X Ai ti)"   using B1 by blast
      have B13:"is_sup R X ((\<lambda>Ai. Sup R X Ai)`?fE) ss"     using B00 B11A1 by presburger
      have B14:"is_sup R X (\<Union>?fE) ss" by (metis (no_types, lifting) B11 B13 P1 assms image_is_empty sup_families)
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

lemma fne_sup_cl_ide:"poset R X \<Longrightarrow> idempotent (Pow X) (\<lambda>A. fne_sup_cl R X A)" by (simp add: fne_sup_cl_idempotent idempotentI1)
lemma fne_sup_cl_range: "(\<lambda>A. fne_sup_cl R X A)`(Pow X) \<subseteq> Pow X"  by (simp add: fne_sup_cl_def image_subset_iff)

lemma fne_sup_cl_is_cl:  "poset R X \<Longrightarrow> closure (powrel X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"  by (simp add: fne_sup_cl_ext fne_sup_cl_ide fne_sup_cl_iso fne_sup_cl_range closure_def)

lemma fne_sup_cl_dir:
  assumes A0:"is_sup_semilattice R X" and A1:"A \<subseteq> X" and A2:"antisym_on X R" "trans_on X R"
  shows  "is_dir (fne_sup_cl R X A) R"
proof-
  have B0:"\<And>a b. a \<in> fne_sup_cl R X A \<and> b \<in> fne_sup_cl R X A \<longrightarrow> (\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"
  proof
    fix a b assume A2:"a \<in> fne_sup_cl R X A \<and> b \<in> fne_sup_cl R X A "
    obtain Ea where A3:"Ea \<in> Fpow A \<and> Ea \<noteq> {} \<and> is_sup R X Ea a"by (meson A2 fne_sup_cl_imp1)
    obtain Eb where A4:"Eb \<in> Fpow A \<and> Eb \<noteq> {} \<and> is_sup R X Eb b" by (meson A2 fne_sup_cl_imp1)
    have B1:"Ea \<union> Eb \<in> Fpow A \<and> Ea \<union> Eb \<noteq> {}"      by (metis A3 A4 Fpow_Pow_finite Int_Collect Pow_iff Un_empty Un_subset_iff finite_UnI)
    have B2:"(Ea \<union> Eb) \<subseteq> X"   by (metis A1 A3 A4 Fpow_Pow_finite Int_Collect Pow_iff dual_order.trans sup.boundedI)
    have B2b:"finite (Ea \<union> Eb)" by (meson B1 Fpow_neD3 Fpow_ne_iff1)
    obtain c where A5:"is_sup R X (Ea \<union> Eb) c"   by (metis A0 B1 B2 B2b assms(3) assms(4) ssupD5) 
    have B3:"c \<in> fne_sup_cl R X A \<and> (a, c) \<in> R \<and> (b, c) \<in> R"   by (smt (verit, best) A3 A4 A5 B1 fne_sup_cl_def is_supE1 is_sup_iso1 mem_Collect_eq semilattice_sup_class.sup_ge1 sup.cobounded2) 
    show "(\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"   using B3 by blast
  qed
  show ?thesis   by (simp add: B0 is_dirI1)
qed
  

lemma ccompact1:
  assumes A0:"is_csup_semilattice R X" and A0b:"poset R X" and
          A1:"c \<in> X" and
          A2:"(\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>a \<in> A. (c, a) \<in> R))"
  shows "is_compact R X c"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R))"
  proof
    fix A assume A3:"A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R"
    let ?C="fne_sup_cl R X A"
    have B0:"is_dir ?C R"  using A0 A3 assms(2) assms(3) csuplatticeD1 fne_sup_cl_dir by fastforce
    have B1:"A \<subseteq> ?C"   using A0b A3 fne_sup_cl_extensive by auto 
    have B2:"A \<subseteq> X \<and> ?C \<subseteq> X"  by (meson A3 Pow_ne_iff fne_sup_cl_imp1 is_supE1 subsetI)
    have B2:"(Sup R X A, Sup R X ?C) \<in> R" by (metis A0 A0b A3 B1 B2 Pow_ne_iff bot.extremum_uniqueI is_csup_semilattice_def is_sup_iso1 sup_equality)
    have B3:"(c, Sup R X ?C) \<in> R"  by (meson A0b A3 B2 refl_onD1 refl_onD2 trans_onD)
    obtain d where B4:"d \<in> ?C \<and> (c, d) \<in> R" by (metis A0b A2 A3 B0 B1 B3 Pow_ne_iff empty_iff fne_sup_cl_imp1 is_dirI1 subset_iff sup_iff2)
    obtain Fd where B5:"Fd \<in> Fpow_ne A \<and> Sup R X Fd = d"by (meson A0b B4 Fpow_ne_iff1 fne_sup_cl_imp1 sup_equality)
    have B6:"Fd \<in> Fpow_ne A \<and> (c, Sup R X Fd) \<in> R" using B4 B5 by fastforce
    show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"     using B6 by blast
  qed
  show ?thesis by (metis A1 P0 compactI)
qed

lemma bot_compact:
  assumes A3:"poset R X" and A1:"bot \<in> X" and A2:"(\<And>x. x \<in> X \<Longrightarrow> (bot, x) \<in> R)"
  shows "is_compact R X bot"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> (bot, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (bot, Sup R X A0) \<in> R))" 
    proof
      fix A assume A3:"A \<in> Pow_ne X \<and> (bot, Sup R X A) \<in> R" obtain a where A4:"a \<in> A"  using A3 by blast
      have B0:"{a} \<in> Fpow_ne A \<and> (bot, Sup R X {a}) \<in> R"    by (smt (verit, best) A2 A3 A4 Fpow_neI Pow_neD1 assms(1) bot.extremum finite.emptyI finite_insert in_mono insert_not_empty insert_subset refl_onD sup_equality sup_singleton) 
      show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> (bot, Sup R X A0) \<in> R)"  using B0 by auto
    qed
  show ?thesis  by (metis A1 P0 compactI)
qed

lemma dir_set_closure_subset:
  assumes A0:"clr (powrel X) (Pow X) C" and
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (powrel X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"(cl  (powrel X) C) {x} \<subseteq> Sup  (powrel X) C A" and 
          A6:"is_dir A (powrel X)"
  shows "\<exists>a \<in> A. (cl (powrel X) C) {x} \<subseteq> a"
proof-
  let ?R="powrel X"  let ?f="cl ?R C"
  have B0:"C \<subseteq> Pow X" by (meson A0 A4 Pow_neD clrD1 order.trans)
  have B1:"A \<subseteq> C"    using A4 by auto
  have B2:"\<Union>A \<in> C"  using A2 A4 A6 by blast
  have B3:"is_sup ?R C A (\<Union>A)"   by (simp add: B0 B1 B2 uni_sup_fam)
  have B4:"Sup ?R C A = \<Union>A"  by (simp add: B0 B3 powrel6 powrel7 sup_equality)
  have B5:"({x}, ?f {x}) \<in> powrel X" by (meson A0 A3 PowD PowI Pow_bottom cl_ext1 insert_subsetI powrel1 powrel2)
  have B6:"{x} \<subseteq> ?f {x}"   using B5 powrel8 by blast
  have B7:"... \<subseteq> \<Union>A"   using A5 B4 by auto
  have B8:"{x} \<subseteq> \<Union>A"  using B6 B7 by blast
  obtain a where B5:"a \<in> A \<and> x \<in> a"   using B8 by auto
  have B9:"({x}, a) \<in> powrel X"  using B0 B1 B5 powrel_def by fastforce
  have B10:"a \<in> ubd (powrel X) C {{x}}" by (meson B1 B5 B9 in_mono ubd_singleton_iff)
  have B11:"?f {x} \<subseteq> a"   by (meson A0 A3 B10 Pow_iff cl_lt_ub1 empty_subsetI insert_subsetI powrel1 powrel2 powrel8)
  show "(\<exists>a\<in>A. ?f {x} \<subseteq> a)"  using B11 B5 by blast
qed

      

lemma singleton_closure_compact:
  assumes A0:"clr (powrel X) (Pow X) C" and
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (powrel X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X"
  shows "is_compact (powrel X)  C (cl (powrel X) C {x})"


lemma closed_compgen:
  assumes A0:"clr (powrel X) (Pow X) C" and
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (powrel X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"E \<in> C"
  shows "(\<exists>A \<in> Pow (compact_elements (powrel X) C). is_sup (powrel X) C A E)"
proof-
  let ?R="powrel X"  let ?f="cl ?R C"
   let ?A="{y. (\<exists>x \<in> E. y= ?f {x})}"
  have B0:"is_clattice ?R C"  by (meson A0 Set.Pow_not_empty clr_is_clattice is_clattice_def powrel1 powrel2 powrel3 powrel5)
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact ?R C (?f {x})"
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

lemma filters_on_lattice_compactgen:
  "\<lbrakk>is_lattice R X; greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> compactly_generated (powrel X) (filters_on R X)" 
  apply(rule_tac ?X="X" in clr_compgen2)
  apply (simp add: filter_is_clr lattD41)
  apply (simp add: filter_inter_closed2 lattD41)
  by (simp add: filters_on_iff lattice_filter_dunion9)


lemma pfilters_metofprimes2:
  assumes A0:"distributive_lattice R X" and A1:"greatest R X top" and A2:"F \<in> pfilters R X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on R X \<and> sup_prime R X Fm " and "F = Inf (powrel X) (filters_on R X) M"
proof-
  let ?FX="(filters_on R X)"
  have B0:"compactly_generated (powrel X) ?FX"   using A0 A1 distr_latticeD5 filters_on_lattice_compactgen lattD1 by auto
  have B1:"is_clattice (powrel X) ?FX"  using A0 A1 distr_latticeD5 lattice_filters_complete by auto
  have B2:"F \<in> ?FX" by (simp add: A2 filters_on_iff pfilters_memD1)
  have B3:"F = Inf (powrel X) ?FX {Fm \<in> ?FX. meet_irr (powrel X) ?FX Fm \<and> (F, Fm) \<in> (powrel X)}"   by (simp add: B0 B1 B2 mirred_temp3)
  have B4:"\<And>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm} \<Longrightarrow> Fm \<in> ?FX \<and> sup_prime X Fm " 
  proof-
    fix Fm assume A3:"Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}" 
    have B40:"Fm \<in> ?FX \<and> meet_irr ?FX Fm"  using A3 by blast
    have B41:"fin_inf_irr ?FX Fm"  using A0 B40 distr_lattice_filters meet_irr_imp_fmeet_irr by blast
    have B43:"is_greatest ?FX X"   by (meson A0 distr_latticeD5 filterD2 filters_is_clr1b filters_on_iff greatest_iff lattD41)
    have B44:"sup_prime X Fm"
    proof(cases "pfilter X Fm")
      case True then show ?thesis   using A0 B40 B41 filters_on_iff prime_filter_irr3_converse sup_prime_def by blast
    next
      case False obtain B45:"Fm = X"  using B40 False filters_on_iff by blast
      then show ?thesis using sup_primeI1 by blast
    qed
    show "Fm \<in> ?FX \<and> sup_prime X Fm"  by (simp add: B40 B44)
  qed
  then show ?thesis  using B3 that by blast
qed



end