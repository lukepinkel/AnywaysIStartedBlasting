theory Posets9
  imports Main
begin

hide_const top bot
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev sup inf Sup Inf trans refl Greatest asym
declare[[show_consts, show_results]]
declare[[show_abbrevs=true]]

abbreviation dual where
  "dual R \<equiv> (converse R)"

definition ubd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "ubd R X A = {b \<in> X. \<forall>a\<in>A. (a, b) \<in> R}"

definition is_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_sup R X A s \<longleftrightarrow> s \<in> ubd R X A \<and> (\<forall>b \<in> ubd R X A. (s, b) \<in> R)"

abbreviation lbd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "lbd R X \<equiv> ubd (dual R) X"

abbreviation is_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_inf R X \<equiv> is_sup (dual R) X"


definition is_greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_greatest R A m \<longleftrightarrow> m \<in> A \<and> (\<forall>a\<in>A. (a, m) \<in> R)"

abbreviation is_least::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_least R \<equiv> is_greatest (dual R)"

definition is_maximal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_maximal R A m \<longleftrightarrow> m \<in> A \<and> (\<forall>a\<in>A. (m, a) \<in> R \<longrightarrow> a = m)"

abbreviation is_minimal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_minimal R \<equiv> is_maximal (dual R)"

definition Sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "Sup R X A = (THE s. is_sup R X A s)"

definition Inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "Inf R X = Sup (dual R) X"

definition sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "sup R X a b = Sup R X {a, b}"

definition inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "inf R X = sup (dual R) X"


definition filter_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "filter_on R X F \<longleftrightarrow>
    F \<subseteq> X \<and> F \<noteq> {} \<and> (\<forall>a\<in>F. \<forall>b\<in>F. \<exists>c\<in>F. (c, a) \<in> R \<and> (c, b) \<in> R) \<and> (\<forall>a\<in>F. \<forall>b\<in>X. (a, b) \<in> R \<longrightarrow> b \<in> F)"

abbreviation ideal_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "ideal_on R X \<equiv> filter_on (dual R) X"


definition subset_order::"'a set rel"
  where "subset_order = {(A, B). A \<subseteq> B}"


definition up_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "up_closed R X A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>X. (a, b) \<in> R \<longrightarrow> b \<in> A)"

abbreviation down_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "down_closed R X \<equiv> up_closed (dual R) X"

definition up_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "up_cl R X A = {x \<in> X. \<exists>a\<in>A. (a, x) \<in> R}"

abbreviation down_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "down_cl R X \<equiv> up_cl (dual R) X"

abbreviation lcro::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "lcro R X a \<equiv> up_cl R X {a}"

abbreviation lorc::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "lorc R X a \<equiv> up_cl (dual R) X {a}"


definition isotone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "isotone R X S f \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. (x, y) \<in> R \<longrightarrow> (f x, f y) \<in> S)"

abbreviation antitone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "antitone R X S \<equiv> isotone R X (dual S)"

definition order_reflecting::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "order_reflecting R X S f \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. (f x, f y) \<in> S \<longrightarrow> (x, y) \<in> R)"

definition order_embedding::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "order_embedding R X S f \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. (x, y) \<in> R \<longleftrightarrow> (f x, f y) \<in> S)"

definition order_iso::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "order_iso R X S Y f \<longleftrightarrow> f ` X = Y \<and> order_embedding R X S f"

definition strictly_isotone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "strictly_isotone R X S f \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. (x, y) \<in> R \<longrightarrow> x \<noteq> y \<longrightarrow> (f x, f y) \<in> S \<and> f x \<noteq> f y)"

lemma ubd_iff[simp]:"b \<in> ubd R X A \<longleftrightarrow> b \<in> X \<and> (\<forall>a\<in>A. (a, b) \<in> R)"
  by (simp add:ubd_def)

lemma is_sup_iff:
  "is_sup R X A s \<longleftrightarrow> s \<in> X \<and> (\<forall>a\<in>A. (a, s) \<in> R) \<and> (\<forall>b\<in>X. (\<forall>a\<in>A. (a, b) \<in> R) \<longrightarrow> (s, b) \<in> R)"
  by (auto simp:is_sup_def)

lemma is_greatestI:"\<lbrakk>m \<in> A;\<And>a. a \<in> A \<Longrightarrow> (a, m) \<in> R\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add:is_greatest_def)

lemma is_supI1:
  "is_least R (ubd R X A) m \<Longrightarrow> is_sup R X A m"
  by (simp add: is_greatest_def is_sup_def)

lemma is_supI2:
  "\<lbrakk>A \<subseteq>X; m \<in> X;(\<And>a. a\<in>A\<Longrightarrow>(a,m)\<in>R);(\<And>b. b\<in>ubd R X A\<Longrightarrow>(m,b)\<in>R)\<rbrakk>\<Longrightarrow> is_least R (ubd R X A) m"
  by (simp add: is_greatest_def)

lemma is_supI3:
  "\<lbrakk>x\<in>X; (\<And>a. a\<in>A \<Longrightarrow> (a,x)\<in>R); (\<And>b. b\<in>X\<Longrightarrow>(\<And>a. a\<in>A \<Longrightarrow>(a,b)\<in>R)\<Longrightarrow> (x,b)\<in>R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma is_supI4:
  "\<lbrakk>m \<in> ubd R X A;(\<And>b. b\<in>ubd R X A\<Longrightarrow>(m,b)\<in>R)\<rbrakk>\<Longrightarrow> is_sup R X A m "
  by (simp add: is_sup_def)

lemma upper_eq_sup_eq:
  "ubd R  X A = ubd R  X B \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (simp add: is_sup_def)

lemma upper_eq_sup_eq2:
  "\<lbrakk>is_sup R X A s1;  ubd R X A=ubd R X B\<rbrakk> \<Longrightarrow> is_sup R X B s1"
  by (simp add: is_sup_def)


lemma is_greatestD:
  "is_greatest R A m \<Longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (a,m)\<in>R) \<and> (m \<in> A)"
  by (simp add:is_greatest_def ubd_def)

lemma is_maximalI:"\<lbrakk>m \<in> A; \<And>a. \<lbrakk>a \<in> A; (m, a)\<in>R\<rbrakk> \<Longrightarrow> a = m\<rbrakk> \<Longrightarrow> is_maximal R A m"
  by (simp add:is_maximal_def)

lemma dual_ops:
  "Sup (dual R) X = Inf R X" 
  "Inf (dual R) X = Sup R X"
  "sup (dual R) X = inf R X" 
  "inf (dual R) X = sup R X"
  by (simp_all add:Inf_def inf_def)



locale poset =
  fixes R::"'a rel" and X::"'a set"
  assumes refl[simp, intro]:"x \<in> X \<Longrightarrow> (x, x) \<in> R"
    and   trans[trans]    :"\<lbrakk>(x, y) \<in> R; (y, z) \<in> R; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (x, z) \<in> R"
    and   antisym         :"\<lbrakk>(x, y) \<in> R; (y, x) \<in> R; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x = y"
begin

abbreviation leq::"'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<le>''" 50) where "x \<le>' y \<equiv> (x, y) \<in> R"
abbreviation SupIn::"'a set \<Rightarrow> 'a" where "SupIn \<equiv> Sup R X"
abbreviation InfIn::"'a set \<Rightarrow> 'a" where "InfIn \<equiv> Inf R X"

lemma is_sup_unique:"\<lbrakk>is_sup R X A s; is_sup R X A t\<rbrakk> \<Longrightarrow> s = t"
  by (auto simp:is_sup_iff intro:antisym)

lemma SupIn_eqI:"is_sup R X A s \<Longrightarrow> SupIn A = s"
  unfolding Sup_def by (blast intro:is_sup_unique)

lemma is_sup_SupIn:"\<exists>s. is_sup R X A s \<Longrightarrow> is_sup R X A (SupIn A)"
  using SupIn_eqI by fastforce

lemma SupIn_props:
  assumes "\<exists>s. is_sup R X A s"
  shows SupIn_base[simp, intro]:"SupIn A \<in> X"
    and SupIn_upper:"a \<in> A \<Longrightarrow> a \<le>' SupIn A"
    and SupIn_least:"\<lbrakk>b \<in> X; \<And>a. a \<in> A \<Longrightarrow> a \<le>' b\<rbrakk> \<Longrightarrow> SupIn A \<le>' b"
  using is_sup_SupIn[OF assms] by (auto simp:is_sup_iff)

end


sublocale poset \<subseteq> dual:poset "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof-
  show "poset (dual R) X"
    by unfold_locales (auto intro:trans antisym)
qed (simp_all add:dual_ops)

context poset
begin

lemma is_inf_unique:"\<lbrakk>is_inf R X A s; is_inf R X A t\<rbrakk> \<Longrightarrow> s = t"
  and InfIn_eqI:"is_inf R X A s \<Longrightarrow> InfIn A = s"
  and is_inf_InfIn:"\<exists>s. is_inf R X A s \<Longrightarrow> is_inf R X A (InfIn A)"
  and InfIn_base:"\<exists>s. is_inf R X A s \<Longrightarrow> InfIn A \<in> X"
  and InfIn_lower:"\<lbrakk>\<exists>s. is_inf R X A s; a \<in> A\<rbrakk> \<Longrightarrow> InfIn A \<le>' a"
  and InfIn_greatest:"\<lbrakk>\<exists>s. is_inf R X A s; b \<in> X; \<And>a. a \<in> A \<Longrightarrow> b \<le>' a\<rbrakk> \<Longrightarrow> b \<le>' InfIn A"
  by (fact dual.is_sup_unique dual.SupIn_eqI dual.is_sup_SupIn dual.SupIn_base dual.SupIn_upper dual.SupIn_least)+

end



locale sup_semilattice = poset +
  assumes ex_sup:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X {a, b} s"
begin

abbreviation supin::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<or>''" 65)
  where "a \<or>' b \<equiv> sup R X a b"

lemma sup_is_sup:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {a, b} (a \<or>' b)"
  unfolding sup_def by (intro is_sup_SupIn ex_sup)

lemma sup_closed[simp, intro]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<in> X"
  and sup_ge1[simp, intro]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<le>' a \<or>' b"
  and sup_ge2[simp, intro]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> b \<le>' a \<or>' b"
  and sup_least:"\<lbrakk>a \<le>' c; b \<le>' c; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<le>' c"
  using sup_is_sup[of a b] by (auto simp:is_sup_iff)

lemma sup_le_iff[simp]:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<le>' c \<longleftrightarrow> a \<le>' c \<and> b \<le>' c"
  by (blast intro:sup_least trans[OF sup_ge1] trans[OF sup_ge2])

lemma le_supI1:"\<lbrakk>x \<le>' a; x \<in> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> x \<le>' a \<or>' b"
  by (rule trans[OF _ sup_ge1]) simp_all

lemma le_supI2:"\<lbrakk>x \<le>' b; x \<in> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> x \<le>' a \<or>' b"
  by (rule trans[OF _ sup_ge2]) simp_all

lemma sup_commute:"a \<or>' b = b \<or>' a"
  by (simp add:sup_def insert_commute)

lemma sup_assoc:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<or>' b) \<or>' c = a \<or>' (b \<or>' c)"
  by (rule antisym) (auto intro:le_supI1 le_supI2)

lemma sup_idem[simp]:"a \<in> X \<Longrightarrow> a \<or>' a = a"
  by (rule antisym) simp_all

lemma le_iff_sup:
  assumes "a \<in> X" "b \<in> X"
  shows "a \<le>' b \<longleftrightarrow> a \<or>' b = b"
proof
  show "a \<or>' b = b" if "a \<le>' b" using assms that by (intro antisym) simp_all
  show "a \<le>' b" if "a \<or>' b = b" using sup_ge1[OF assms] that by simp
qed

lemma sup_iso:"\<lbrakk>a \<le>' c; b \<le>' d; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<le>' c \<or>' d"
  by (intro sup_least) (auto intro:le_supI1 le_supI2)

end


locale inf_semilattice = poset +
  assumes ex_inf:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X {a, b} s"
begin

abbreviation infin::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<and>''" 70) where "a \<and>' b \<equiv> inf R X a b"

end

sublocale inf_semilattice \<subseteq> dual:sup_semilattice "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "sup_semilattice (dual R) X"
    by unfold_locales (simp_all add:ex_inf)
qed (simp_all add:dual_ops)

context inf_semilattice
begin

lemma inf_is_inf:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> is_inf R X {a, b} (a \<and>' b)"
  and inf_closed[]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' b \<in> X"
  and inf_le1[]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' b \<le>' a"
  and inf_le2[]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' b \<le>' b"
  and inf_greatest:"\<lbrakk>c \<le>' a; c \<le>' b; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> c \<le>' a \<and>' b"
  and le_inf_iff[]:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> c \<le>' a \<and>' b \<longleftrightarrow> c \<le>' a \<and> c \<le>' b"
  and le_infI1:"\<lbrakk>a \<le>' x; x \<in> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' b \<le>' x"
  and le_infI2:"\<lbrakk>b \<le>' x; x \<in> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' b \<le>' x"
  and inf_commute:"a \<and>' b = b \<and>' a"
  and inf_assoc:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<and>' b) \<and>' c = a \<and>' (b \<and>' c)"
  and inf_idem[]:"a \<in> X \<Longrightarrow> a \<and>' a = a"
  and le_iff_inf:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> b \<le>' a \<longleftrightarrow> a \<and>' b = b"
  and inf_iso:"\<lbrakk>c \<le>' a; d \<le>' b; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> c \<and>' d \<le>' a \<and>' b"
  apply (simp_all add:dual.sup_is_sup)
  apply (simp add:dual.le_supI1)
  apply (simp add:dual.le_supI2)
  apply (simp add:dual.sup_commute)
  apply (simp add:dual.sup_assoc)
  apply (simp add:dual.le_iff_sup)
  by (simp add:dual.le_supI1 dual.le_supI2)

end

sublocale sup_semilattice \<subseteq> dual:inf_semilattice "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "inf_semilattice (dual R) X"
    by unfold_locales (simp_all add:ex_sup)
qed (simp_all add:dual_ops)


locale lattice_on = sup_semilattice + inf_semilattice
begin

lemma sup_absorb:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<or>' (a \<and>' b) = a"
  by (rule antisym) simp_all

lemma modular_ineq:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<and>' b) \<or>' (a \<and>' c) \<le>' a \<and>' (b \<or>' c)"
  by (intro sup_least inf_greatest) (auto intro:le_supI1 le_supI2 le_infI1 le_infI2)

end

sublocale lattice_on \<subseteq> dual:lattice_on "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "lattice_on (dual R) X"
    by unfold_locales
qed (simp_all add:dual_ops)

context lattice_on
begin

lemma inf_absorb:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' (a \<or>' b) = a"
  and modular_ineq_dual:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<or>' (b \<and>' c) \<le>' (a \<or>' b) \<and>' (a \<or>' c)"
  by (fact dual.sup_absorb dual.modular_ineq)+

end

context poset
begin
abbreviation filters::"'a set set" where "filters \<equiv> {F. filter_on R X F}"
end

context inf_semilattice
begin

lemma filter_iff:
  "filter_on R X F \<longleftrightarrow>
    F \<subseteq> X \<and> F \<noteq> {} \<and> (\<forall>a\<in>F. \<forall>b\<in>F. a \<and>' b \<in> F) \<and> (\<forall>a\<in>F. \<forall>b\<in>X. a \<le>' b \<longrightarrow> b \<in> F)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then have F:"F \<subseteq> X" "F \<noteq> {}" and up:"\<And>a b. \<lbrakk>a \<in> F; b \<in> X; a \<le>' b\<rbrakk> \<Longrightarrow> b \<in> F"
    and dir:"\<And>a b. \<lbrakk>a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> \<exists>c\<in>F. c \<le>' a \<and> c \<le>' b"
    by (auto simp:filter_on_def)
  have "a \<and>' b \<in> F" if ab:"a \<in> F" "b \<in> F" for a b
  proof -
    obtain c where c:"c \<in> F" "c \<le>' a" "c \<le>' b" using dir ab by blast
    from F ab c have X:"a \<in> X" "b \<in> X" "c \<in> X" by auto
    with c have "c \<le>' a \<and>' b" by simp
    with c(1) X show ?thesis by (blast intro:up)
  qed
  with F up show ?R by blast
next
  assume R:?R
  then have "\<exists>c\<in>F. c \<le>' a \<and> c \<le>' b" if "a \<in> F" "b \<in> F" for a b
    using that by (intro bexI[of _ "a \<and>' b"]) auto
  show ?L
    by (simp add: R \<open>\<And>b a. a \<in> F \<Longrightarrow> b \<in> F \<Longrightarrow> \<exists>c\<in>F. c \<le>' a \<and> c \<le>' b\<close>filter_on_def)
qed

end



locale complete_lattice_on = poset +
  assumes ex_SupIn:"A \<subseteq> X \<Longrightarrow> \<exists>s. is_sup R X A s"
begin

lemma ex_InfIn:assumes "A \<subseteq> X" shows "\<exists>s. is_inf R X A s"
proof -
  have "\<exists>s. is_sup R X (lbd R X A) s" by (rule ex_SupIn) auto
  then obtain s where "is_sup R X (lbd R X A) s" ..
  with assms have "is_inf R X A s" by (auto simp:is_sup_iff)
  then show ?thesis
    by auto 
qed

end

sublocale complete_lattice_on \<subseteq> lattice_on
  by unfold_locales (simp_all add:ex_SupIn ex_InfIn)

sublocale complete_lattice_on \<subseteq> dual:complete_lattice_on "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "complete_lattice_on (dual R) X"
    by unfold_locales (simp_all add:ex_InfIn)
qed (simp_all add:dual_ops)



lemma subset_order_iff[simp]:"(A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  by (simp add:subset_order_def)


locale closure_op = poset +
  fixes cl::"'a \<Rightarrow> 'a"
  assumes cl_base[simp, intro]:"x \<in> X \<Longrightarrow> cl x \<in> X"
    and cl_extensive:"x \<in> X \<Longrightarrow> x \<le>' cl x"
    and cl_iso:"\<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> cl x \<le>' cl y"
    and cl_idem[simp]:"x \<in> X \<Longrightarrow> cl (cl x) = cl x"
begin

definition closed::"'a set"
  where "closed = {c \<in> X. cl c = c}"

lemma closed_iff:"c \<in> closed \<longleftrightarrow> c \<in> X \<and> cl c = c"
  by (simp add:closed_def)

lemma closed_base:"closed \<subseteq> X"
  by (auto simp:closed_def)

lemma cl_closed[simp, intro]:"x \<in> X \<Longrightarrow> cl x \<in> closed"
  by (simp add:closed_def)

lemma closed_range:"closed = cl ` X"
proof
  show "closed \<subseteq> cl ` X"
  proof
    fix c assume "c \<in> closed"
    then have c:"c \<in> X" "cl c = c" by (simp_all add:closed_iff)
    then have "c = cl c" by simp
    from this c(1) show "c \<in> cl ` X" by (rule image_eqI)
  qed
  show "cl ` X \<subseteq> closed" by (auto simp:closed_def)
qed

lemma cl_least:"\<lbrakk>x \<le>' c; x \<in> X; c \<in> closed\<rbrakk> \<Longrightarrow> cl x \<le>' c"
proof -
  assume "x \<le>' c" "x \<in> X" "c \<in> closed"
  then have "cl x \<le>' cl c" using closed_base by (intro cl_iso) auto
  with \<open>c \<in> closed\<close> show "cl x \<le>' c" by (simp add:closed_iff)
qed

lemma cl_is_sup_closed:"x \<in> X \<Longrightarrow> is_sup R closed {x} (cl x)"
  by (auto simp:is_sup_iff intro:cl_extensive cl_least)

end

lemma interior_contractive:"\<lbrakk>closure_op (dual R) X i; x \<in> X\<rbrakk> \<Longrightarrow> (i x, x) \<in> R"
  by (drule closure_op.cl_extensive) simp_all


context poset
begin

lemma Sup_sub_eqI:assumes "C \<subseteq> X" and s:"is_sup R C A s" shows "Sup R C A = s"
proof -
  have uniq:"t = s" if t:"is_sup R C A t" for t
  proof (rule antisym)
    show "t \<le>' s" and "s \<le>' t" using t s by (auto simp:is_sup_iff)
    show "t \<in> X" and "s \<in> X" using t s \<open>C \<subseteq> X\<close> by (auto simp:is_sup_iff)
  qed
  show ?thesis unfolding Sup_def by (rule the_equality) (rule s, rule uniq)
qed

lemma Inf_sub_eqI:"\<lbrakk>C \<subseteq> X; is_inf R C A s\<rbrakk> \<Longrightarrow> Inf R C A = s"
  unfolding Inf_def using dual.poset_axioms poset.Sup_sub_eqI[of "dual R" X C A s] by simp

lemma closure_opI:
  assumes A0:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> X" and A1:"\<And>x. x \<in> X \<Longrightarrow> x \<le>' f x" and
          A2:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X; x \<le>' f y\<rbrakk> \<Longrightarrow> f x \<le>' f y"
  shows "closure_op R X f"
proof(unfold_locales)
  show "\<And>x. x \<in> X \<Longrightarrow> f x \<in> X"
    by (rule A0)
  show "\<And>x. x \<in> X \<Longrightarrow> x \<le>' f x"
    by (rule A1)
  show "\<And>x y. \<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f x \<le>' f y"
  proof-
    fix x y assume B0:"x \<le>' y" and B1:"x \<in> X" and B2:"y \<in> X"
    have "x \<le>' f y"
      by (rule trans[OF B0 A1[OF B2] B1 B2 A0[OF B2]])
    then show "f x \<le>' f y"
      by (rule A2[OF B1 B2])
  qed
  show "\<And>x. x \<in> X \<Longrightarrow> f (f x) = f x"
  proof-
    fix x assume B0:"x \<in> X"
    have "f (f x) \<le>' f x"
      using A2[OF A0[OF B0] B0] A0[OF B0] by simp
    moreover have "f x \<le>' f (f x)"
      by (rule A1[OF A0[OF B0]])
    ultimately show "f (f x) = f x"
      using A0[OF B0] A0[OF A0[OF B0]] by (intro antisym) simp_all
  qed
qed
end

locale closure_range = poset +
  fixes C::"'a set"
  assumes C_base:"C \<subseteq> X"
    and ex_cl:"x \<in> X \<Longrightarrow> \<exists>c. is_sup R C {x} c"
begin

definition cl::"'a \<Rightarrow> 'a"
  where "cl x = Sup R C {x}"

lemma cl_is_sup:assumes "x \<in> X" shows "is_sup R C {x} (cl x)"
proof -
  obtain s where s:"is_sup R C {x} s" using ex_cl[OF assms] ..
  then show ?thesis unfolding cl_def by (simp add:Sup_sub_eqI[OF C_base s])
qed

lemma cl_closed[simp, intro]:"x \<in> X \<Longrightarrow> cl x \<in> C"
  and cl_extensive:"x \<in> X \<Longrightarrow> x \<le>' cl x"
  and cl_least:"\<lbrakk>x \<le>' c; x \<in> X; c \<in> C\<rbrakk> \<Longrightarrow> cl x \<le>' c"
  using cl_is_sup[of x] by (auto simp:is_sup_iff)

lemma cl_base[simp, intro]:"x \<in> X \<Longrightarrow> cl x \<in> X"
  using cl_closed C_base by blast

lemma cl_fixed[simp]:assumes c:"c \<in> C" shows "cl c = c"
proof -
  have cX:"c \<in> X" using c C_base by blast
  show ?thesis by (rule antisym) (auto intro:cl_least[OF refl] cl_extensive simp:c cX)
qed

lemma cl_iso:"\<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> cl x \<le>' cl y"
  by (rule cl_least) (auto intro:trans[OF _ cl_extensive])

lemma cl_idem[simp]:"x \<in> X \<Longrightarrow> cl (cl x) = cl x"
  by (intro cl_fixed cl_closed)

sublocale op:closure_op R X cl
  by unfold_locales (auto intro:cl_extensive cl_iso)

lemma closed_eq[simp]:"op.closed = C"
proof
  show "op.closed \<subseteq> C"
  proof
    fix c assume "c \<in> op.closed"
    then have "c \<in> X" "cl c = c" by (simp_all add:op.closed_iff)
    then show "c \<in> C" using cl_closed[of c] by simp
  qed
  show "C \<subseteq> op.closed" using C_base by (auto simp:op.closed_iff)
qed

end
context closure_op
begin

lemma range_closure_range:"closure_range R X closed"
  by unfold_locales (auto simp:closed_iff intro:cl_is_sup_closed)

lemma range_cl_eq:assumes "x \<in> X" shows "closure_range.cl R closed x = cl x"
proof -
  interpret cr:closure_range R X closed by (rule range_closure_range)
  show ?thesis
    unfolding cr.cl_def by (rule Sup_sub_eqI[OF closed_base cl_is_sup_closed[OF assms]])
qed

end


locale complete_closure_range = closure_range + complete_lattice_on
begin

lemma InfIn_closed:assumes A:"A \<subseteq> C" shows "InfIn A \<in> C"
proof -
  have AX:"A \<subseteq> X" using A C_base by blast
  note ex = ex_InfIn[OF AX]
  have g:"InfIn A \<in> X" by (rule InfIn_base[OF ex])
  have "cl (InfIn A) \<le>' InfIn A"
  proof (rule InfIn_greatest[OF ex])
    show "cl (InfIn A) \<in> X" using g by simp
    fix a assume a:"a \<in> A"
    have "InfIn A \<le>' a" by (rule InfIn_lower[OF ex a])
    then show "cl (InfIn A) \<le>' a" using g a A by (intro cl_least) auto
  qed
  then have "cl (InfIn A) = InfIn A" using g by (intro antisym) (auto intro:cl_extensive)
  then show ?thesis using cl_closed[OF g] by simp
qed

lemma is_sup_closed_cl:assumes A:"A \<subseteq> C" shows "is_sup R C A (cl (SupIn A))"
proof -
  have AX:"A \<subseteq> X" using A C_base by blast
  note ex = ex_SupIn[OF AX]
  have L1:"SupIn A \<in> X" by (rule SupIn_base[OF ex])
  have L2:"a \<le>' SupIn A" if "a \<in> A" for a by (rule SupIn_upper[OF ex that])
  have L3:"SupIn A \<le>' b" if "b \<in> X" "\<And>a. a \<in> A \<Longrightarrow> a \<le>' b" for b by (rule SupIn_least[OF ex that])
  have 1:"cl (SupIn A) \<in> C" using L1 by simp
  have 2:"a \<le>' cl (SupIn A)" if a:"a \<in> A" for a
    by (rule trans[OF L2[OF a] cl_extensive]) (simp_all add:L1 subsetD[OF AX a])
  have 3:"cl (SupIn A) \<le>' b" if b:"b \<in> C" and ub:"\<And>a. a \<in> A \<Longrightarrow> a \<le>' b" for b
  proof -
    have bX:"b \<in> X" using b C_base by blast
    have "SupIn A \<le>' b" by (rule L3[OF bX ub])
    then have "cl (SupIn A) \<le>' cl b" by (rule cl_iso) (simp_all add:L1 bX)
    then show ?thesis using b by simp
  qed
  show ?thesis unfolding is_sup_iff using 1 2 3 by blast
qed

lemma is_inf_closed:assumes A:"A \<subseteq> C" shows "is_inf R C A (InfIn A)"
proof -
  have AX:"A \<subseteq> X" using A C_base by blast
  note ex = ex_InfIn[OF AX]
  show ?thesis
    unfolding is_sup_iff
    using InfIn_closed[OF A] InfIn_lower[OF ex] InfIn_greatest[OF ex] C_base by auto
qed


lemma closed_complete:"complete_lattice_on R C"
proof (rule complete_lattice_on.intro)
  show "poset R C" by unfold_locales (auto intro:trans antisym dest:subsetD[OF C_base])
  show "complete_lattice_on_axioms R C"
    by (rule complete_lattice_on_axioms.intro) (blast intro:is_sup_closed_cl)
qed

lemma closed_Sup_eq:"A \<subseteq> C \<Longrightarrow> Sup R C A = cl (SupIn A)"
  by (rule Sup_sub_eqI[OF C_base is_sup_closed_cl])

lemma closed_Inf_eq:"A \<subseteq> C \<Longrightarrow> Inf R C A = InfIn A"
  by (rule Inf_sub_eqI[OF C_base is_inf_closed])

end

locale inf_closed = complete_lattice_on +
  fixes C::"'a set"
  assumes C_base:"C \<subseteq> X"
    and InfIn_closed:"A \<subseteq> C \<Longrightarrow> InfIn A \<in> C"
begin

lemma is_sup_above:assumes x:"x \<in> X" shows "is_sup R C {x} (InfIn {c \<in> C. x \<le>' c})"
proof -
  let ?U = "{c \<in> C. x \<le>' c}"
  have U:"?U \<subseteq> C" by blast
  have UX:"?U \<subseteq> X" using C_base by blast
  note ex = ex_InfIn[OF UX]
  have 1:"InfIn ?U \<in> C" by (rule InfIn_closed[OF U])
  have 2:"x \<le>' InfIn ?U" by (rule InfIn_greatest[OF ex x]) simp
  have 3:"InfIn ?U \<le>' c" if "c \<in> C" "x \<le>' c" for c by (rule InfIn_lower[OF ex]) (simp add:that)
  show ?thesis unfolding is_sup_iff using 1 2 3 by blast
qed

sublocale cr:complete_closure_range R X C
proof (rule complete_closure_range.intro)
  show "closure_range R X C"
  proof (rule closure_range.intro[OF poset_axioms], rule closure_range_axioms.intro)
    show "C \<subseteq> X" by (rule C_base)
    show "\<exists>c. is_sup R C {x} c" if "x \<in> X" for x using is_sup_above[OF that] ..
  qed
  show "complete_lattice_on R X" by (rule complete_lattice_on_axioms)
qed

lemma cl_eq_InfIn:"x \<in> X \<Longrightarrow> cr.cl x = InfIn {c \<in> C. x \<le>' c}"
  unfolding cr.cl_def by (rule Sup_sub_eqI[OF C_base is_sup_above])

end



lemma pow_poset:"poset subset_order (Pow X)"
  by unfold_locales auto

lemma is_inf_pow:"is_inf subset_order (Pow X) A (X \<inter> \<Inter>A)"
  by (auto simp:is_sup_iff)

lemma is_sup_pow:"A \<subseteq> Pow X \<Longrightarrow> is_sup subset_order (Pow X) A (\<Union>A)"
  by (auto simp:is_sup_iff)

lemma pow_complete:"complete_lattice_on subset_order (Pow X)"
  by (rule complete_lattice_on.intro[OF pow_poset])
     (blast intro:complete_lattice_on_axioms.intro is_sup_pow)

lemma Inf_pow:"Inf subset_order (Pow X) = (\<lambda>A. X \<inter> \<Inter>A)"
proof (rule ext)
  interpret pow:poset subset_order "Pow X" by (rule pow_poset)
  fix A show "Inf subset_order (Pow X) A = X \<inter> \<Inter>A" by (rule pow.InfIn_eqI[OF is_inf_pow])
qed

lemma Sup_pow:"A \<subseteq> Pow X \<Longrightarrow> Sup subset_order (Pow X) A = \<Union>A"
proof -
  interpret pow:poset subset_order "Pow X" by (rule pow_poset)
  assume "A \<subseteq> Pow X" then show ?thesis by (rule pow.SupIn_eqI[OF is_sup_pow])
qed

locale moore_family =
  fixes X::"'a set" and C::"'a set set"
  assumes base:"C \<subseteq> Pow X"
    and whole:"X \<in> C"
    and Inter_closed:"\<lbrakk>E \<subseteq> C; E \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>E \<in> C"
begin

definition cl::"'a set \<Rightarrow> 'a set"
  where "cl A = \<Inter>{c \<in> C. A \<subseteq> c}"

lemma cl_closed[simp, intro]:"A \<subseteq> X \<Longrightarrow> cl A \<in> C"
  unfolding cl_def using whole by (intro Inter_closed) auto

lemma cl_extensive:"A \<subseteq> cl A"
  and cl_least:"\<lbrakk>c \<in> C; A \<subseteq> c\<rbrakk> \<Longrightarrow> cl A \<subseteq> c"
  and cl_iso:"A \<subseteq> B \<Longrightarrow> cl A \<subseteq> cl B"
  by (auto simp:cl_def)

lemma cl_fixed[simp]:"c \<in> C \<Longrightarrow> cl c = c"
  using cl_extensive[of c] cl_least[of c c] by auto

lemma cl_idem:"A \<subseteq> X \<Longrightarrow> cl (cl A) = cl A"
  by simp

lemma is_sup_cl:assumes "E \<subseteq> C" shows "is_sup subset_order C E (cl (\<Union>E))"
proof -
  have B0:"\<Union>E \<subseteq> X" 
    using assms base by blast
  show "is_sup subset_order C E (cl (\<Union>E))"
  proof(rule is_supI4)
    show "cl (\<Union> E) \<in> ubd subset_order C E"
      using B0 cl_extensive by fastforce
    show "\<And>b. b \<in> ubd subset_order C E \<Longrightarrow> (cl (\<Union> E), b) \<in> subset_order"
      by (simp add: Sup_le_iff cl_least)
  qed
qed

end

sublocale moore_family \<subseteq> closed:complete_lattice_on subset_order C
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
proof -
  show "complete_lattice_on subset_order C"
    by unfold_locales (auto intro:is_sup_cl)
qed simp

context moore_family
begin

lemma SupIn_closed_eq:"E \<subseteq> C \<Longrightarrow> closed.SupIn E = cl (\<Union>E)"
  by (rule closed.SupIn_eqI) (rule is_sup_cl)

lemma InfIn_closed_eq:"\<lbrakk>E \<subseteq> C; E \<noteq> {}\<rbrakk> \<Longrightarrow> closed.InfIn E = \<Inter>E"
  by (rule closed.InfIn_eqI) (auto simp:is_sup_iff Inter_closed)

end



locale lattice_top = lattice_on +
  fixes tp::'a
  assumes tp_base:"tp \<in> X" and tp_greatest:"x \<in> X \<Longrightarrow> x \<le>' tp"
begin

lemma tp_in_filter:"filter_on R X F \<Longrightarrow> tp \<in> F"
  unfolding filter_on_def using tp_base tp_greatest by blast

sublocale filters:moore_family X filters
proof
  show "filters \<subseteq> Pow X" by (auto simp:filter_on_def)
  have "X \<noteq> {}" using tp_base by blast
  then show "X \<in> filters" by (auto simp:filter_iff)
  show "\<Inter>E \<in> filters" if E:"E \<subseteq> filters" "E \<noteq> {}" for E
  proof -
    have fil:"filter_on R X F" if "F \<in> E" for F using E(1) that by blast
    have "filter_on R X (\<Inter>E)"
      unfolding filter_iff
    proof (intro conjI ballI impI)
      show "\<Inter>E \<subseteq> X" using fil E(2) unfolding filter_on_def by blast
      show "\<Inter>E \<noteq> {}" using fil tp_in_filter by blast
      show "a \<and>' b \<in> \<Inter>E" if "a \<in> \<Inter>E" "b \<in> \<Inter>E" for a b
        using fil that unfolding filter_iff by blast
      show "b \<in> \<Inter>E" if "a \<in> \<Inter>E" "b \<in> X" "a \<le>' b" for a b
        using fil that unfolding filter_on_def by blast
    qed
    then show ?thesis by simp
  qed
qed


lemma "E \<subseteq> filters \<Longrightarrow> filters.closed.SupIn E = filters.cl (\<Union>E)"
  and "\<lbrakk>E \<subseteq> filters; E \<noteq> {}\<rbrakk> \<Longrightarrow> filters.closed.InfIn E = \<Inter>E"
  by (fact filters.SupIn_closed_eq filters.InfIn_closed_eq)+

end



locale poset_bot = poset +
  fixes bt::'a
  assumes bt_base:"bt \<in> X" and bt_least:"x \<in> X \<Longrightarrow> bt \<le>' x"
begin

definition pfilter::"'a set \<Rightarrow> bool"
  where "pfilter F \<longleftrightarrow> filter_on R X F \<and> bt \<notin> F"

theorem ultrafilter_lemma:
  assumes "pfilter F"
  obtains U where "pfilter U" "F \<subseteq> U" "\<And>G. \<lbrakk>pfilter G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U"
proof -
  let ?\<A> = "{G. pfilter G \<and> F \<subseteq> G}"
  have "\<exists>U\<in>?\<A>. \<forall>G\<in>?\<A>. U \<subseteq> G \<longrightarrow> G = U"
  proof (rule subset_Zorn_nonempty)
    show "?\<A> \<noteq> {}" using assms by blast
    fix \<C> assume "\<C> \<noteq> {}" and chain:"subset.chain ?\<A> \<C>"
    then obtain G0 where G0:"G0 \<in> \<C>" by blast
    from chain have lin:"\<And>G H. \<lbrakk>G \<in> \<C>; H \<in> \<C>\<rbrakk> \<Longrightarrow> G \<subseteq> H \<or> H \<subseteq> G"
      and fil:"\<And>G. G \<in> \<C> \<Longrightarrow> filter_on R X G"
      and rest:"\<And>G. G \<in> \<C> \<Longrightarrow> bt \<notin> G \<and> F \<subseteq> G"
      by (auto simp:subset_chain_def pfilter_def)
    have "filter_on R X (\<Union>\<C>)"
      unfolding filter_on_def
    proof (intro conjI ballI impI)
      show "\<Union>\<C> \<subseteq> X" using fil unfolding filter_on_def by blast
      show "\<Union>\<C> \<noteq> {}" using fil[OF G0] G0 unfolding filter_on_def by blast
    next
      fix a b assume "a \<in> \<Union>\<C>" "b \<in> \<Union>\<C>"
      with lin obtain G where "G \<in> \<C>" "a \<in> G" "b \<in> G" by blast
      with fil[of G] show "\<exists>c\<in>\<Union>\<C>. c \<le>' a \<and> c \<le>' b" unfolding filter_on_def by blast
    next
      fix a b assume "a \<in> \<Union>\<C>" "b \<in> X" "a \<le>' b"
      with fil show "b \<in> \<Union>\<C>" unfolding filter_on_def by blast
    qed
    with G0 rest show "\<Union>\<C> \<in> ?\<A>" by (auto simp:pfilter_def)
  qed
  then obtain U where U:"pfilter U" "F \<subseteq> U"
    and max:"\<And>G. \<lbrakk>pfilter G; F \<subseteq> G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U" by auto
  show thesis
  proof (rule that[OF U])
    show "G = U" if "pfilter G" "U \<subseteq> G" for G using max[of G] that U(2) by blast
  qed
qed

end


definition lgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "lgc_from_rel R Y X = {t \<in> Y. \<forall>s\<in>X. (s, t) \<in> R}"

lemma lgc_from_rel_galois:"\<lbrakk>A \<subseteq> X; B \<subseteq> Y\<rbrakk> \<Longrightarrow> B \<subseteq> lgc_from_rel R Y A \<longleftrightarrow> A \<subseteq> lgc_from_rel (dual R) X B"
  and lgc_from_rel_mono_decreasing:"A \<subseteq> A' \<Longrightarrow> lgc_from_rel R Y A' \<subseteq> lgc_from_rel R Y A"
  and lgc_from_rel_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> lgc_from_rel (dual R) X (lgc_from_rel R Y A)"
  and lgc_from_rel_triple:"A \<subseteq> X \<Longrightarrow> lgc_from_rel R Y (lgc_from_rel (dual R) X (lgc_from_rel R Y A)) = lgc_from_rel R Y A"
  by (auto simp:lgc_from_rel_def)

definition meshes::"'a set rel"
  where "meshes = {(A, B). A \<inter> B \<noteq> {}}"

definition grill::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "grill X \<A> = lgc_from_rel meshes (Pow X) \<A>"

lemma meshes_sym[simp]:"dual meshes = meshes"
  by (auto simp:meshes_def)

lemma grill_antiiso:"\<A> \<subseteq> \<B> \<Longrightarrow> grill X \<B> \<subseteq> grill X \<A>"
  and grill_grill_extensive:"\<A> \<subseteq> Pow X \<Longrightarrow> \<A> \<subseteq> grill X (grill X \<A>)"
  and grill_triple:"\<A> \<subseteq> Pow X \<Longrightarrow> grill X (grill X (grill X \<A>)) = grill X \<A>"
  unfolding grill_def
  using lgc_from_rel_mono_decreasing[of \<A> \<B> meshes "Pow X"] lgc_from_rel_extensive[of \<A> "Pow X" meshes "Pow X"]
    lgc_from_rel_triple[of \<A> "Pow X" meshes "Pow X"]
  by simp_all



sublocale moore_family \<subseteq> cs:inf_closed subset_order "Pow X" C
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "Inf subset_order (Pow X) = (\<lambda>A. X \<inter> \<Inter>A)"
proof -
  show "inf_closed subset_order (Pow X) C"
  proof (rule inf_closed.intro[OF pow_complete], rule inf_closed_axioms.intro)
    show "C \<subseteq> Pow X" by (rule base)
    fix A assume A:"A \<subseteq> C"
    show "Inf subset_order (Pow X) A \<in> C"
    proof (cases "A = {}")
      case True
      then show ?thesis using whole by (simp add:Inf_pow)
    next
      case False
      then obtain a where a:"a \<in> A" by blast
      have "\<Inter>A \<subseteq> X" using a A base by blast
      then have "Inf subset_order (Pow X) A = \<Inter>A" by (simp add:Inf_pow Int_absorb1)
      then show ?thesis using Inter_closed[OF A False] by simp
    qed
  qed
qed (simp_all add:Inf_pow)

context moore_family
begin


lemma cl_eq_general:assumes A:"A \<subseteq> X" shows "cs.cr.cl A = cl A"
proof -
  have "cs.cr.cl A = X \<inter> \<Inter>{c \<in> C. A \<subseteq> c}" using A by (simp add:cs.cl_eq_InfIn)
  also have "\<dots> = \<Inter>{c \<in> C. A \<subseteq> c}" using whole A by (intro Int_absorb1 Inter_lower) simp
  finally show ?thesis by (simp add:cl_def)
qed


lemma "\<lbrakk>c \<in> C; A \<subseteq> c\<rbrakk> \<Longrightarrow> cl A \<subseteq> c"
  and "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> cl A \<subseteq> cl B"
  and "E \<subseteq> C \<Longrightarrow> closed.SupIn E = cl (\<Union>E)"
proof -
  show "\<lbrakk>c \<in> C; A \<subseteq> c\<rbrakk> \<Longrightarrow> cl A \<subseteq> c"
  proof -
    assume c:"c \<in> C" and Ac:"A \<subseteq> c"
    have AX:"A \<subseteq> X" using c Ac base by blast
    have "cs.cr.cl A \<subseteq> c" by (rule cs.cr.cl_least) (simp_all add:Ac AX c)
    then show "cl A \<subseteq> c" by (simp add:cl_eq_general[OF AX])
  qed
  show "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> cl A \<subseteq> cl B"
  proof -
    assume AB:"A \<subseteq> B" and BX:"B \<subseteq> X"
    have AX:"A \<subseteq> X" using AB BX by blast
    have "cs.cr.cl A \<subseteq> cs.cr.cl B" by (rule cs.cr.cl_iso) (simp_all add:AB AX BX)
    then show "cl A \<subseteq> cl B" by (simp add:cl_eq_general[OF AX] cl_eq_general[OF BX])
  qed
  show "E \<subseteq> C \<Longrightarrow> closed.SupIn E = cl (\<Union>E)"
  proof -
    assume E:"E \<subseteq> C"
    have UX:"\<Union>E \<subseteq> X" using E base by blast
    have 1:"closed.SupIn E = cs.cr.cl (Sup subset_order (Pow X) E)" by (rule cs.cr.closed_Sup_eq[OF E])
    have 2:"Sup subset_order (Pow X) E = \<Union>E" using E base by (intro Sup_pow) blast
    show "closed.SupIn E = cl (\<Union>E)" by (simp add:1 2 cl_eq_general[OF UX])
  qed
qed

end


locale galois_conn = dom:poset R X + cod:poset S Y
  for R::"'a rel" and X::"'a set" and S::"'b rel" and Y::"'b set" +
  fixes f::"'a \<Rightarrow> 'b" and g::"'b \<Rightarrow> 'a"
  assumes f_maps[simp, intro]:"x \<in> X \<Longrightarrow> f x \<in> Y"
    and g_maps[simp, intro]:"y \<in> Y \<Longrightarrow> g y \<in> X"
    and cl_cond:"\<lbrakk>x \<in> X; y \<in> Y\<rbrakk> \<Longrightarrow> (x, g y) \<in> R \<longleftrightarrow> (y, f x) \<in> S"
begin

lemma ext_f:"x \<in> X \<Longrightarrow> (x, g (f x)) \<in> R"
  by (simp add:cl_cond)

lemma ext_g:"y \<in> Y \<Longrightarrow> (y, f (g y)) \<in> S"
  using cl_cond[of "g y" y] by simp

lemma anti_f:assumes xx:"(x, x') \<in> R" and x:"x \<in> X" and x':"x' \<in> X" shows "(f x', f x) \<in> S"
proof -
  have "(x, g (f x')) \<in> R" by (rule dom.trans[OF xx ext_f[OF x']]) (simp_all add:x x')
  then show ?thesis using cl_cond[OF x f_maps[OF x']] by simp
qed

lemma anti_g:assumes yy:"(y, y') \<in> S" and y:"y \<in> Y" and y':"y' \<in> Y" shows "(g y', g y) \<in> R"
proof -
  have "(y, f (g y')) \<in> S" by (rule cod.trans[OF yy ext_g[OF y']]) (simp_all add:y y')
  then show ?thesis using cl_cond[OF g_maps[OF y'] y] by simp
qed

lemma idem_f:assumes x:"x \<in> X" shows "f (g (f x)) = f x"
proof (rule cod.antisym)
  show "(f (g (f x)), f x) \<in> S" by (rule anti_f[OF ext_f[OF x] x]) (simp add:x)
  show "(f x, f (g (f x))) \<in> S" by (rule ext_g) (simp add:x)
qed (simp_all add:x)

sublocale closure:closure_op R X "g \<circ> f"
  by unfold_locales (auto simp:ext_f idem_f intro:anti_g anti_f)

end

lemma lgc_from_rel_galois_conn:"galois_conn subset_order (Pow S) subset_order (Pow T) (lgc_from_rel R T) (lgc_from_rel (R\<inverse>) S)"
  by unfold_locales (auto simp:lgc_from_rel_def)

lemma double_lgc_from_rel_closure_op:"closure_op subset_order (Pow S) (lgc_from_rel (R\<inverse>) S \<circ> lgc_from_rel R T)"
proof -
  interpret galois_conn subset_order "Pow S" subset_order "Pow T" "lgc_from_rel R T" "lgc_from_rel (R\<inverse>) S"
    by (rule lgc_from_rel_galois_conn)
  show ?thesis by (rule closure.closure_op_axioms)
qed

lemma double_grill_closure_op:"closure_op subset_order (Pow (Pow X)) (grill X \<circ> grill X)"
  using double_lgc_from_rel_closure_op[where R = meshes and S = "Pow X" and T = "Pow X"]
  by (simp add:grill_def[abs_def])




lemma is_greatest_iff:"is_greatest R A m \<longleftrightarrow> m \<in> A \<and> (\<forall>a\<in>A. (a, m) \<in> R)"
  and is_least_iff:"is_least R A m \<longleftrightarrow> m \<in> A \<and> (\<forall>a\<in>A. (m, a) \<in> R)"
  and is_maximal_iff:"is_maximal R A m \<longleftrightarrow> m \<in> A \<and> (\<forall>a\<in>A. (m, a) \<in> R \<longrightarrow> a = m)"
  and is_minimal_iff:"is_minimal R A m \<longleftrightarrow> m \<in> A \<and> (\<forall>a\<in>A. (a, m) \<in> R \<longrightarrow> a = m)"
  by (auto simp:is_greatest_def is_maximal_def)

lemma is_greatest_is_sup:"is_greatest R A m \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A m"
  by (auto simp:is_greatest_def is_sup_iff)

lemma is_sup_is_greatest:"\<lbrakk>is_sup R X A m; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (auto simp:is_greatest_def is_sup_iff)

lemma is_sup_empty_iff:"is_sup R X {} m \<longleftrightarrow> is_least R X m"
  by (auto simp:is_greatest_def is_sup_iff)

lemma is_sup_whole_iff:"is_sup R X X m \<longleftrightarrow> is_greatest R X m"
  by (auto simp:is_greatest_def is_sup_iff)

context poset
begin

lemma is_greatest_unique:"\<lbrakk>is_greatest R A m; is_greatest R A n; A \<subseteq> X\<rbrakk> \<Longrightarrow> m = n"
  by (auto simp:is_greatest_def intro:antisym)

lemma is_greatest_maximal:"\<lbrakk>is_greatest R A m; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_maximal R A m"
  by (auto simp:is_greatest_def is_maximal_def intro:antisym)


lemma finite_maximal:
  assumes A0:"finite A" and A1:"A \<noteq> {}" and A2:"A \<subseteq> X"
  shows "\<exists>m. is_maximal R A m"
  using assms
proof (induct A rule:finite_ne_induct)
  case (singleton x)
  then show ?case by (auto simp:is_maximal_def)
next
  case (insert x A)
  then obtain m where B0:"is_maximal R A m" by blast
  obtain B1:"m \<in> A" and B2:"m \<in> X" and B3:"x \<in> X" and B4:"A \<subseteq> X"
    using B0 insert(5)by (simp add:is_maximal_iff subset_iff)
  show ?case
  proof (cases "m \<le>' x")
    case T:True
    have "is_maximal R (insert x A) x"
      unfolding is_maximal_def
    proof (intro conjI ballI impI)
      show " x \<in> insert x A"
        by simp
      show "\<And>a. a \<in> insert x A \<Longrightarrow> x \<le>' a \<Longrightarrow> a = x"
      proof-
        fix a assume A3:"a \<in> insert x A" and A4:"x \<le>' a"
        show "a = x"
        proof (cases "a = x")
          case False
          have  B5:"a \<in> A"
            using A3 False by auto 
          have B6:"m \<le>' a"
            using A4 B2 B3 B4 B5 T dual.trans by blast 
          have "a = m"
            by (meson B0 B5 B6 is_maximal_iff)
          then show ?thesis
            using A4 B2 B3 T dual.antisym by blast
        qed
      qed
    qed
    then show ?thesis 
      by blast
  next
    case False
    then have "is_maximal R (insert x A) m"
      using B0 by (auto simp:is_maximal_def)
    then show ?thesis by blast
  qed
qed

lemma finite_unique_maximal:
  assumes A0:"finite A" and 
          A1:"A \<subseteq> X" and
          A2:"is_maximal R A m" and 
          A3:"\<And>n. is_maximal R A n \<Longrightarrow> n = m"
  shows "is_greatest R A m"
proof(rule is_greatestI)
  show "m \<in> A" 
    using A2 by (simp add:is_maximal_iff) 
  show "\<And>a. a \<in> A \<Longrightarrow> a \<le>' m"
  proof-
    fix a assume A4:"a \<in> A"
    let ?U = "{b \<in> A. a \<le>' b}"
    obtain B0:"finite ?U" and B1:"?U \<noteq> {}" and B2:"?U \<subseteq> X"
      using A0 A1 A4 by auto 
    then obtain n where B3:"is_maximal R ?U n" 
      using finite_maximal by blast
    have B4:"n \<in> A" 
      using B3 by (simp add:is_maximal_iff)
    have B5:"a \<le>' n"
      using B3 by (simp add:is_maximal_iff)  
    have B6:"is_maximal R A n"
    proof(rule is_maximalI)
      show "n \<in> A"
        by (simp add:B4)
      show "\<And>a. a \<in> A \<Longrightarrow> n \<le>' a \<Longrightarrow> a = n"
      proof-
        fix x assume B7:"x \<in> A" and B8:"n \<le>' x"
        then have "a \<le>' x"
          using A1 A4 B4 B5 dual.trans by blast
        then show "x = n"
          using B3 B7 B8 by (simp add:is_maximal_iff)
      qed
    qed 
    show "a \<le>' m"
      using A3 B5 B6 by blast
  qed
qed

end

context poset
begin

lemma is_least_unique:"\<lbrakk>is_least R A m; is_least R A n; A \<subseteq> X\<rbrakk> \<Longrightarrow> m = n"
  and is_least_minimal:"\<lbrakk>is_least R A m; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_minimal R A m"
  and finite_minimal:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> \<exists>m. is_minimal R A m"
  and finite_unique_minimal:
    "\<lbrakk>finite A; A \<subseteq> X; is_minimal R A m; \<And>n. is_minimal R A n \<Longrightarrow> n = m\<rbrakk> \<Longrightarrow> is_least R A m"
  by (fact dual.is_greatest_unique dual.is_greatest_maximal dual.finite_maximal dual.finite_unique_maximal)+

end



context poset
begin

lemma is_sup_singleton[simp]:"x \<in> X \<Longrightarrow> is_sup R X {x} x"
  by (auto simp:is_sup_iff)

lemma SupIn_singleton[simp]:"x \<in> X \<Longrightarrow> SupIn {x} = x"
  by (simp add:SupIn_eqI[OF is_sup_singleton])

lemma is_sup_iso:assumes s:"is_sup R X A s" and t:"is_sup R X B t" and AB:"A \<subseteq> B" shows "s \<le>' t"
proof -
  have "t \<in> X" "\<And>a. a \<in> A \<Longrightarrow> a \<le>' t" using t AB by (auto simp:is_sup_iff)
  with s show ?thesis by (auto simp:is_sup_iff)
qed

lemma is_sup_insert:
  assumes A:"A \<subseteq> X" and s:"is_sup R X A s" and t:"is_sup R X {x, s} t"
  shows "is_sup R X (insert x A) t"
  unfolding is_sup_iff
proof (intro conjI ballI impI)
  show tX:"t \<in> X" using t by (simp add:is_sup_iff)
  have sX:"s \<in> X" and st:"s \<le>' t" and xt:"x \<le>' t" using s t by (auto simp:is_sup_iff)
  show "a \<le>' t" if "a \<in> insert x A" for a
  proof (cases "a = x")
    case False
    with that have aA:"a \<in> A" by simp
    have "a \<le>' s" using s aA by (simp add:is_sup_iff)
    then show ?thesis by (rule trans[OF _ st]) (auto simp:aA A[THEN subsetD] sX tX)
  qed (simp add:xt)
  fix b assume b:"b \<in> X" and ub:"\<forall>a\<in>insert x A. a \<le>' b"
  have "s \<le>' b" using s b ub by (auto simp:is_sup_iff)
  with ub t b show "t \<le>' b" by (auto simp:is_sup_iff)
qed

lemma is_sup_union:
  assumes A:"A \<subseteq> X" and B:"B \<subseteq> X" and s:"is_sup R X A s" and t:"is_sup R X B t" and u:"is_sup R X {s, t} u"
  shows "is_sup R X (A \<union> B) u"
  unfolding is_sup_iff
proof (intro conjI ballI impI)
  have sX:"s \<in> X" and tX:"t \<in> X" and su:"s \<le>' u" and tu:"t \<le>' u" using s t u by (auto simp:is_sup_iff)
  show uX:"u \<in> X" using u by (simp add:is_sup_iff)
  show "a \<le>' u" if "a \<in> A \<union> B" for a
  proof (cases "a \<in> A")
    case True
    then have "a \<le>' s" using s by (simp add:is_sup_iff)
    then show ?thesis by (rule trans[OF _ su]) (auto simp:True A[THEN subsetD] sX uX)
  next
    case False
    with that have aB:"a \<in> B" by simp
    then have "a \<le>' t" using t by (simp add:is_sup_iff)
    then show ?thesis by (rule trans[OF _ tu]) (auto simp:aB B[THEN subsetD] tX uX)
  qed
  fix b assume b:"b \<in> X" and ub:"\<forall>a\<in>A \<union> B. a \<le>' b"
  have "s \<le>' b" "t \<le>' b" using s t b ub by (auto simp:is_sup_iff)
  with u b show "u \<le>' b" by (auto simp:is_sup_iff)
qed


lemma is_sup_families:
  assumes sub:"\<And>A. A \<in> \<A> \<Longrightarrow> A \<subseteq> X" and sups:"\<And>A. A \<in> \<A> \<Longrightarrow> \<exists>s. is_sup R X A s"
  shows "is_sup R X (SupIn ` \<A>) s \<longleftrightarrow> is_sup R X (\<Union>\<A>) s"
proof -
  have S:"is_sup R X A (SupIn A)" if "A \<in> \<A>" for A by (rule is_sup_SupIn[OF sups[OF that]])
  have SX:"SupIn A \<in> X" if "A \<in> \<A>" for A using S[OF that] by (simp add:is_sup_iff)
  show ?thesis
  proof
    assume L:"is_sup R X (SupIn ` \<A>) s"
    then have sX:"s \<in> X" by (simp add:is_sup_iff)
    show "is_sup R X (\<Union>\<A>) s"
      unfolding is_sup_iff
    proof (intro conjI ballI impI sX)
      fix a assume "a \<in> \<Union>\<A>"
      then obtain A where A:"A \<in> \<A>" "a \<in> A" by blast
      have aX:"a \<in> X" using A sub by blast
      have "a \<le>' SupIn A" using S[OF A(1)] A(2) by (simp add:is_sup_iff)
      moreover have "SupIn A \<le>' s" using L A(1) by (auto simp:is_sup_iff)
      ultimately show "a \<le>' s" by (rule trans) (auto simp:aX SX[OF A(1)] sX)
    next
      fix b assume b:"b \<in> X" and ub:"\<forall>a\<in>\<Union>\<A>. a \<le>' b"
      have "SupIn A \<le>' b" if "A \<in> \<A>" for A using S[OF that] that b ub by (auto simp:is_sup_iff)
      with L b show "s \<le>' b" by (auto simp:is_sup_iff)
    qed
  next
    assume L:"is_sup R X (\<Union>\<A>) s"
    then have sX:"s \<in> X" by (simp add:is_sup_iff)
    show "is_sup R X (SupIn ` \<A>) s"
      unfolding is_sup_iff
    proof (intro conjI ballI impI sX)
      fix t assume "t \<in> SupIn ` \<A>"
      then obtain A where A:"A \<in> \<A>" "t = SupIn A" by blast
      have "a \<le>' s" if "a \<in> A" for a using L A(1) that by (auto simp:is_sup_iff)
      with S[OF A(1)] show "t \<le>' s" unfolding A(2) using sX by (auto simp:is_sup_iff)
    next
      fix b assume b:"b \<in> X" and ub:"\<forall>t\<in>SupIn ` \<A>. t \<le>' b"
      have "a \<le>' b" if A:"A \<in> \<A>" and a:"a \<in> A" for a A
      proof -
        have aX:"a \<in> X" using A a sub by blast
        have "a \<le>' SupIn A" using S[OF A] a by (simp add:is_sup_iff)
        moreover have "SupIn A \<le>' b" using ub A by auto
        ultimately show ?thesis by (rule trans) (auto simp:aX SX[OF A] b)
      qed
      with L b show "s \<le>' b" by (auto simp:is_sup_iff)
    qed
  qed
qed

end

context poset
begin

lemma is_inf_singleton[]:"x \<in> X \<Longrightarrow> is_inf R X {x} x"
  and is_inf_iso:"\<lbrakk>is_inf R X A s; is_inf R X B t; A \<subseteq> B\<rbrakk> \<Longrightarrow> t \<le>' s"
  and is_inf_insert:"\<lbrakk>A \<subseteq> X; is_inf R X A s; is_inf R X {x, s} t\<rbrakk> \<Longrightarrow> is_inf R X (insert x A) t"
  and is_inf_union:"\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_inf R X A s; is_inf R X B t; is_inf R X {s, t} u\<rbrakk> \<Longrightarrow> is_inf R X (A \<union> B) u"
  and is_inf_families:
    "\<lbrakk>\<And>A. A \<in> \<A> \<Longrightarrow> A \<subseteq> X; \<And>A. A \<in> \<A> \<Longrightarrow> \<exists>s. is_inf R X A s\<rbrakk>
      \<Longrightarrow> is_inf R X (InfIn ` \<A>) s \<longleftrightarrow> is_inf R X (\<Union>\<A>) s"
  apply simp
  apply (simp add:dual.is_sup_iso)
  using dual.is_sup_insert apply blast
  apply (simp add:dual.is_sup_union)
  by (simp add:dual.is_sup_families)

lemma InfIn_singleton[]:"x \<in> X \<Longrightarrow> InfIn {x} = x"
  by simp

end

context sup_semilattice
begin

lemma finite_sup_ex:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s"
proof (induct A rule:finite_ne_induct)
  case (singleton x)
  then show ?case by (auto intro:is_sup_singleton)
next
  case (insert x A)
  then obtain s where s:"is_sup R X A s" by blast
  then have "s \<in> X" by (simp add:is_sup_iff)
  with insert(5) obtain t where t:"is_sup R X {x, s} t" using ex_sup by blast
  have "is_sup R X (insert x A) t" using insert(5) by (intro is_sup_insert[OF _ s t]) auto
  then show ?case ..
qed

lemma finite_SupIn:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup R X A (SupIn A)"
  by (rule is_sup_SupIn[OF finite_sup_ex])

lemma finite_SupIn_base[simp]:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> SupIn A \<in> X"
  and finite_SupIn_upper:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<le>' SupIn A"
  and finite_SupIn_least:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; b \<in> X; \<And>a. a \<in> A \<Longrightarrow> a \<le>' b\<rbrakk> \<Longrightarrow> SupIn A \<le>' b"
  using finite_SupIn[of A] by (auto simp:is_sup_iff)

lemma SupIn_insert:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; x \<in> X\<rbrakk> \<Longrightarrow> SupIn (insert x A) = x \<or>' SupIn A"
  by (rule SupIn_eqI[OF is_sup_insert[OF _ finite_SupIn sup_is_sup]]) auto

lemma SupIn_doubleton:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> SupIn {a, b} = a \<or>' b"
  by (simp add:sup_def)

lemma SupIn_union:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; finite B; B \<noteq> {}; B \<subseteq> X\<rbrakk> \<Longrightarrow> SupIn (A \<union> B) = SupIn A \<or>' SupIn B"
  by (rule SupIn_eqI[OF is_sup_union[OF _ _ finite_SupIn finite_SupIn sup_is_sup]]) auto

lemma finite_SupIn_iso:"\<lbrakk>finite B; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> SupIn A \<le>' SupIn B"
  by (rule is_sup_iso[OF finite_SupIn finite_SupIn]) (auto intro:finite_subset)


lemma finite_sup_closed:
  assumes D:"D \<subseteq> X" and cl:"\<And>a b. \<lbrakk>a \<in> D; b \<in> D\<rbrakk> \<Longrightarrow> a \<or>' b \<in> D"
  shows "\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> D\<rbrakk> \<Longrightarrow> SupIn A \<in> D"
proof (induct A rule:finite_ne_induct)
  case (singleton x)
  then show ?case using D by auto
next
  case (insert x A)
  then have "SupIn (insert x A) = x \<or>' SupIn A" using D by (intro SupIn_insert) auto
  with insert cl show ?case by simp
qed


lemma join_hom_isotone:
  assumes "sup_semilattice S Y" and maps:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y"
    and hom:"\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> f (a \<or>' b) = sup S Y (f a) (f b)"
    and ab:"a \<le>' b" "a \<in> X" "b \<in> X"
  shows "(f a, f b) \<in> S"
proof -
  interpret cod:sup_semilattice S Y by fact
  have "f (a \<or>' b) = f b" using ab by (simp add:le_iff_sup)
  then have "sup S Y (f a) (f b) = f b" by (simp add:hom ab)
  then show ?thesis using maps ab by (simp add:cod.le_iff_sup)
qed

end

context inf_semilattice
begin

lemma finite_inf_ex:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X A s"
  and finite_InfIn:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_inf R X A (InfIn A)"
  and finite_InfIn_base[]:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> InfIn A \<in> X"
  and finite_InfIn_lower:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> InfIn A \<le>' a"
  and finite_InfIn_greatest:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; b \<in> X; \<And>a. a \<in> A \<Longrightarrow> b \<le>' a\<rbrakk> \<Longrightarrow> b \<le>' InfIn A"
  and InfIn_insert:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; x \<in> X\<rbrakk> \<Longrightarrow> InfIn (insert x A) = x \<and>' InfIn A"
  and InfIn_doubleton:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> InfIn {a, b} = a \<and>' b"
  and InfIn_union:"\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X; finite B; B \<noteq> {}; B \<subseteq> X\<rbrakk> \<Longrightarrow> InfIn (A \<union> B) = InfIn A \<and>' InfIn B"
  and finite_InfIn_anti:"\<lbrakk>finite B; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> InfIn B \<le>' InfIn A"
  and finite_inf_closed:"\<lbrakk>D \<subseteq> X; \<And>a b. \<lbrakk>a \<in> D; b \<in> D\<rbrakk> \<Longrightarrow> a \<and>' b \<in> D; finite A; A \<noteq> {}; A \<subseteq> D\<rbrakk> \<Longrightarrow> InfIn A \<in> D"
  by (fact dual.finite_sup_ex dual.finite_SupIn dual.finite_SupIn_base dual.finite_SupIn_upper dual.finite_SupIn_least
      dual.SupIn_insert dual.SupIn_doubleton dual.SupIn_union dual.finite_SupIn_iso dual.finite_sup_closed)+

end



definition is_dir::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  where "is_dir R D \<longleftrightarrow> (\<forall>a\<in>D. \<forall>b\<in>D. \<exists>c\<in>D. (a, c) \<in> R \<and> (b, c) \<in> R)"

lemma is_dirI:"(\<And>a b. \<lbrakk>a \<in> D; b \<in> D\<rbrakk> \<Longrightarrow> \<exists>c\<in>D. (a, c) \<in> R \<and> (b, c) \<in> R) \<Longrightarrow> is_dir R D"
  and is_dirD:"\<lbrakk>is_dir R D; a \<in> D; b \<in> D\<rbrakk> \<Longrightarrow> \<exists>c\<in>D. (a, c) \<in> R \<and> (b, c) \<in> R"
  by (auto simp:is_dir_def)

lemma is_dir_empty[simp]:"is_dir R {}"
  by (simp add:is_dir_def)

lemma filter_on_iff_dir:"filter_on R X F \<longleftrightarrow> F \<subseteq> X \<and> F \<noteq> {} \<and> is_dir (dual R) F \<and> (\<forall>a\<in>F. \<forall>b\<in>X. (a, b) \<in> R \<longrightarrow> b \<in> F)"
  by (auto simp:filter_on_def is_dir_def)

context poset
begin

lemma dir_finite_bound:
  assumes dir:"is_dir R D" and D:"D \<subseteq> X"
  shows "\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> D\<rbrakk> \<Longrightarrow> \<exists>c\<in>D. \<forall>a\<in>A. a \<le>' c"
proof (induct A rule:finite_ne_induct)
  case (singleton x)
  then show ?case using D by (auto intro!:bexI[of _ x])
next
  case (insert x A)
  then obtain c where c:"c \<in> D" "\<And>a. a \<in> A \<Longrightarrow> a \<le>' c" by blast
  obtain d where d:"d \<in> D" "x \<le>' d" "c \<le>' d" using is_dirD[OF dir _ c(1), of x] insert(5) by blast
  have "a \<le>' d" if a:"a \<in> A" for a
  proof -
    have "a \<in> X" "c \<in> X" "d \<in> X" using a c(1) d(1) insert(5) D by auto
    then show ?thesis by (rule trans[OF c(2)[OF a] d(3)])
  qed
  with d show ?case by auto
qed



lemma  dir_finite_bound_dual:
  "\<lbrakk>is_dir (dual R) D; D \<subseteq> X; finite A; A \<noteq> {}; A \<subseteq> D\<rbrakk> \<Longrightarrow> \<exists>c\<in>D. \<forall>a\<in>A. c \<le>' a"
  using dual.poset_axioms poset.dir_finite_bound by fastforce
end

context sup_semilattice
begin
lemma  sup_closed_dir:
  assumes D:"D \<subseteq> X" and cl:"\<And>a b. \<lbrakk>a \<in> D; b \<in> D\<rbrakk> \<Longrightarrow> a \<or>' b \<in> D"
  shows "is_dir R D"
  unfolding is_dir_def
proof (intro ballI)
  fix a b assume ab:"a \<in> D" "b \<in> D"
  then have "a \<in> X" "b \<in> X" using D by auto
  with cl[OF ab] show "\<exists>c\<in>D. a \<le>' c \<and> b \<le>' c" by (intro bexI[of _ "a \<or>' b"]) auto
qed

lemma base_dir:"is_dir R X"
  by (rule sup_closed_dir) auto
end

context inf_semilattice
begin
lemma base_dwdir:"is_dir (dual R) X"
  by (rule dual.base_dir)

lemma  filter_dwdir:"filter_on R X F \<Longrightarrow> is_dir (dual R) F"
  by (simp add:filter_on_iff_dir)
end


lemma up_closedI:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; (a, b) \<in> R\<rbrakk> \<Longrightarrow> b \<in> A) \<Longrightarrow> up_closed R X A"
  and up_closedD:"\<lbrakk>up_closed R X A; a \<in> A; b \<in> X; (a, b) \<in> R\<rbrakk> \<Longrightarrow> b \<in> A"
  by (auto simp:up_closed_def)

lemma up_cl_iff[simp]:"x \<in> up_cl R X A \<longleftrightarrow> x \<in> X \<and> (\<exists>a\<in>A. (a, x) \<in> R)"
  by (simp add:up_cl_def)

lemma lcro_iff:"x \<in> lcro R X a \<longleftrightarrow> x \<in> X \<and> (a, x) \<in> R"
  by simp

lemma lcro_eq_ubd:"lcro R X a = ubd R X {a}"
  by auto

lemma up_cl_base:"up_cl R X A \<subseteq> X"
  by auto

lemma up_closed_Union:"(\<And>A. A \<in> \<A> \<Longrightarrow> up_closed R X A) \<Longrightarrow> up_closed R X (\<Union>\<A>)"
  and up_closed_Inter:"(\<And>A. A \<in> \<A> \<Longrightarrow> up_closed R X A) \<Longrightarrow> up_closed R X (\<Inter>\<A>)"
  and up_closed_Un:"\<lbrakk>up_closed R X A; up_closed R X B\<rbrakk> \<Longrightarrow> up_closed R X (A \<union> B)"
  and up_closed_Int:"\<lbrakk>up_closed R X A; up_closed R X B\<rbrakk> \<Longrightarrow> up_closed R X (A \<inter> B)"
  and up_closed_whole:"up_closed R X X"
  and up_closed_empty:"up_closed R X {}"
  by (auto simp:up_closed_def)

lemma up_closed_complement:"A \<subseteq> X \<Longrightarrow> up_closed R X A \<longleftrightarrow> down_closed R X (X - A)"
  by (auto simp:up_closed_def subset_iff)

lemma filter_up_closed:"filter_on R X F \<Longrightarrow> up_closed R X F"
  by (auto simp:filter_on_def up_closed_def)

lemma filter_on_iff_up_closed:
  "filter_on R X F \<longleftrightarrow> F \<subseteq> X \<and> F \<noteq> {} \<and> is_dir (dual R) F \<and> up_closed R X F"
  by (auto simp:filter_on_def is_dir_def up_closed_def)

context poset
begin

lemma up_cl_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> up_cl R X A"
  and up_cl_iso:"A \<subseteq> B \<Longrightarrow> up_cl R X A \<subseteq> up_cl R X B"
  by (auto simp:subset_iff)

lemma up_cl_up_closed:assumes A:"A \<subseteq> X" shows "up_closed R X (up_cl R X A)"
  unfolding up_closed_def
proof (intro ballI impI)
  fix x y assume x:"x \<in> up_cl R X A" and y:"y \<in> X" and xy:"x \<le>' y"
  from x obtain a where a:"a \<in> A" "a \<le>' x" and xX:"x \<in> X" by auto
  have "a \<in> X" using a A by blast
  with a xX y xy have "a \<le>' y" by (blast intro:trans)
  with a y show "y \<in> up_cl R X A" by auto
qed

lemma up_cl_idem:assumes A:"A \<subseteq> X" shows "up_cl R X (up_cl R X A) = up_cl R X A"
proof
  show "up_cl R X (up_cl R X A) \<subseteq> up_cl R X A"
  proof
    fix y assume "y \<in> up_cl R X (up_cl R X A)"
    then obtain x where "x \<in> up_cl R X A" "y \<in> X" "x \<le>' y" by auto
    then show "y \<in> up_cl R X A" by (rule up_closedD[OF up_cl_up_closed[OF A]])
  qed
  show "up_cl R X A \<subseteq> up_cl R X (up_cl R X A)" by (rule up_cl_extensive) (rule up_cl_base)
qed

lemma up_closed_iff_up_cl:assumes A:"A \<subseteq> X" shows "up_closed R X A \<longleftrightarrow> up_cl R X A = A"
proof
  assume "up_closed R X A"
  then show "up_cl R X A = A"
    by (intro subset_antisym up_cl_extensive[OF A]) (auto simp:up_closed_def)
next
  assume "up_cl R X A = A"
  then show "up_closed R X A" using up_cl_up_closed[OF A] by simp
qed

lemma up_cl_least:"\<lbrakk>up_closed R X B; A \<subseteq> B\<rbrakk> \<Longrightarrow> up_cl R X A \<subseteq> B"
  by (auto simp:up_closed_def subset_iff)


lemma up_cl_closure_op:"closure_op subset_order (Pow X) (up_cl R X)"
  by unfold_locales (auto simp:up_cl_idem up_cl_iso up_cl_extensive up_cl_base)

lemma up_cl_dwdir:"\<lbrakk>is_dir (dual R) A; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_dir (dual R) (up_cl R X A)"
  unfolding is_dir_def
proof (intro ballI)
  fix x y assume dir:"\<forall>a\<in>A. \<forall>b\<in>A. \<exists>c\<in>A. (a, c) \<in> dual R \<and> (b, c) \<in> dual R" and A:"A \<subseteq> X"
    and x:"x \<in> up_cl R X A" and y:"y \<in> up_cl R X A"
  then obtain a b where ab:"a \<in> A" "a \<le>' x" "b \<in> A" "b \<le>' y" by auto
  with dir obtain c where c:"c \<in> A" "c \<le>' a" "c \<le>' b" by auto
  have cX:"c \<in> X" and aX:"a \<in> X" "b \<in> X" and xX:"x \<in> X" "y \<in> X" using c ab x y A by auto
  have cU:"c \<in> up_cl R X A" using c cX by auto
  have "c \<le>' x" "c \<le>' y" using c ab cX aX xX by (blast intro:trans)+
  then have cxy:"(x, c) \<in> dual R \<and> (y, c) \<in> dual R" by simp
  show "\<exists>c\<in>up_cl R X A. (x, c) \<in> dual R \<and> (y, c) \<in> dual R" by (rule bexI[where x = c]) (rule cxy, rule cU)
qed

lemma lcro_base[simp]:"a \<in> X \<Longrightarrow> a \<in> lcro R X a"
  by simp

lemma lcro_filter:assumes a:"a \<in> X" shows "filter_on R X (lcro R X a)"
  unfolding filter_on_iff_up_closed
proof (intro conjI)
  show "lcro R X a \<subseteq> X" by (rule up_cl_base)
  show "lcro R X a \<noteq> {}" using lcro_base[OF a] by blast
  show "is_dir (dual R) (lcro R X a)" by (rule up_cl_dwdir) (auto simp:is_dir_def a)
  show "up_closed R X (lcro R X a)" by (rule up_cl_up_closed) (simp add:a)
qed

lemma lcro_anti_iff:assumes "a \<in> X" "b \<in> X" shows "a \<le>' b \<longleftrightarrow> lcro R X b \<subseteq> lcro R X a"
proof
  show "lcro R X b \<subseteq> lcro R X a" if "a \<le>' b" using assms by (auto intro:trans[OF that])
  show "a \<le>' b" if "lcro R X b \<subseteq> lcro R X a" using subsetD[OF that lcro_base[OF assms(2)]] by simp
qed

lemma lcro_inj:"\<lbrakk>a \<in> X; b \<in> X; lcro R X a = lcro R X b\<rbrakk> \<Longrightarrow> a = b"
  by (intro antisym) (auto simp:lcro_anti_iff)

lemma up_cl_dir:
  assumes A0:"is_dir (dual R) A" and A1:"A \<subseteq> X"
  shows "is_dir (dual R) (up_cl R X A)"
  by (simp add: A0 A1 up_cl_dwdir)
end



lemma isotoneI:"(\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (f x, f y) \<in> S) \<Longrightarrow> isotone R X S f"
  and isotoneD:"\<lbrakk>isotone R X S f; x \<in> X; y \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (f x, f y) \<in> S"
  by (auto simp:isotone_def)

lemma order_embedding_iff:"order_embedding R X S f \<longleftrightarrow> isotone R X S f \<and> order_reflecting R X S f"
  by (auto simp:order_embedding_def isotone_def order_reflecting_def)

lemma order_isoD:
  assumes "order_iso R X S Y f"
  shows order_iso_image:"f ` X = Y"
    and order_iso_maps:"x \<in> X \<Longrightarrow> f x \<in> Y"
    and order_iso_embed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> (f x, f y) \<in> S"
    and order_iso_isotone:"isotone R X S f"
    and order_iso_surj:"v \<in> Y \<Longrightarrow> \<exists>x\<in>X. v = f x"
  using assms by (auto simp:order_iso_def order_embedding_def isotone_def)

lemma order_isoI:"\<lbrakk>f ` X = Y; \<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> (f x, f y) \<in> S\<rbrakk> \<Longrightarrow> order_iso R X S Y f"
  by (simp add:order_iso_def order_embedding_def)

lemma isotone_comp:"\<lbrakk>isotone R X S f; isotone S Y T g; f ` X \<subseteq> Y\<rbrakk> \<Longrightarrow> isotone R X T (g \<circ> f)"
  by (auto simp:isotone_def image_subset_iff)

lemma order_iso_id:"order_iso R X R X id"
  by (simp add:order_iso_def order_embedding_def)

lemma order_iso_comp:"\<lbrakk>order_iso R X S Y f; order_iso S Y T Z g\<rbrakk> \<Longrightarrow> order_iso R X T Z (g \<circ> f)"
  unfolding order_iso_def order_embedding_def by (auto simp:image_comp)

lemma order_iso_cong:
  assumes iso:"order_iso R X S Y f" and eq:"\<And>x. x \<in> X \<Longrightarrow> f x = g x"
  shows "order_iso R X S Y g"
proof (rule order_isoI)
  have "f ` X = g ` X" by (rule image_cong) (simp_all add:eq)
  then show "g ` X = Y" using order_iso_image[OF iso] by simp
  fix x y assume "x \<in> X" "y \<in> X"
  then show "(x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> S" by (simp add:eq[symmetric] order_iso_embed[OF iso])
qed


lemma order_iso_is_sup:
  assumes iso:"order_iso R X S Y f" and A:"A \<subseteq> X" and s:"is_sup R X A s"
  shows "is_sup S Y (f ` A) (f s)"
  unfolding is_sup_iff
proof (intro conjI ballI impI)
  have sX:"s \<in> X" using s by (simp add:is_sup_iff)
  then show "f s \<in> Y" by (rule order_iso_maps[OF iso])
  show "(t, f s) \<in> S" if "t \<in> f ` A" for t
  proof -
    from that obtain a where a:"a \<in> A" "t = f a" by blast
    have aX:"a \<in> X" using a A by blast
    have "(a, s) \<in> R" using s a by (simp add:is_sup_iff)
    then show ?thesis unfolding a(2) using order_iso_embed[OF iso aX sX] by simp
  qed
  fix b assume "b \<in> Y" and ub:"\<forall>t\<in>f ` A. (t, b) \<in> S"
  then obtain y where y:"y \<in> X" "b = f y" using order_iso_surj[OF iso] by blast
  have "(a, y) \<in> R" if a:"a \<in> A" for a
  proof -
    have aX:"a \<in> X" using a A by blast
    have "(f a, f y) \<in> S" using ub a by (simp add:y(2))
    then show ?thesis using order_iso_embed[OF iso aX y(1)] by simp
  qed
  with s y have "(s, y) \<in> R" by (auto simp:is_sup_iff)
  then show "(f s, b) \<in> S" unfolding y(2) using order_iso_embed[OF iso sX y(1)] by simp
qed

lemma order_iso_is_inf:
  "\<lbrakk>order_iso R X S Y f; A \<subseteq> X; is_inf R X A s\<rbrakk> \<Longrightarrow> is_inf S Y (f ` A) (f s)"
  by (rule order_iso_is_sup) (auto simp:order_iso_def order_embedding_def)

lemma isotone_is_sup:
  assumes iso:"isotone R X S f" and maps:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y" and A:"A \<subseteq> X"
    and s:"is_sup R X A s" and t:"is_sup S Y (f ` A) t"
  shows "(t, f s) \<in> S"
proof -
  have "f s \<in> Y" using s maps by (simp add:is_sup_iff)
  moreover have "(f a, f s) \<in> S" if "a \<in> A" for a
    using s A that by (auto simp:is_sup_iff intro:isotoneD[OF iso])
  ultimately show ?thesis using t by (auto simp:is_sup_iff)
qed

context poset
begin

lemma order_embedding_inj:
  assumes emb:"order_embedding R X S f" and refl:"\<And>x. x \<in> X \<Longrightarrow> (f x, f x) \<in> S"
  shows "inj_on f X"
proof
  fix x y assume xy:"x \<in> X" "y \<in> X" "f x = f y"
  then have "(f x, f y) \<in> S" "(f y, f x) \<in> S" using refl by auto
  then have "x \<le>' y" "y \<le>' x" using emb xy by (auto simp:order_embedding_def)
  then show "x = y" using xy by (intro antisym)
qed

lemma order_iso_inj:
  assumes "order_iso R X S Y f" "poset S Y"
  shows "inj_on f X"
proof -
  interpret cod:poset S Y by fact
  show ?thesis using assms(1) by (intro order_embedding_inj) (auto simp:order_iso_def)
qed

lemma order_iso_bij:"\<lbrakk>order_iso R X S Y f; poset S Y\<rbrakk> \<Longrightarrow> bij_betw f X Y"
  by (simp add:bij_betw_def order_iso_inj order_iso_image)

lemma order_iso_inv:
  assumes iso:"order_iso R X S Y f" and inj:"inj_on f X"
  shows "order_iso S Y R X (inv_into X f)"
proof (rule order_isoI)
  have Y:"Y = f ` X" by (simp add:order_iso_image[OF iso])
  show "inv_into X f ` Y = X" unfolding Y by (rule inv_into_image_cancel[OF inj subset_refl])
  fix u v assume uv:"u \<in> Y" "v \<in> Y"
  then have iu:"inv_into X f u \<in> X" "inv_into X f v \<in> X"
    and fu:"f (inv_into X f u) = u" "f (inv_into X f v) = v"
    unfolding Y by (simp_all add:f_inv_into_f inv_into_into)
  show "(u, v) \<in> S \<longleftrightarrow> (inv_into X f u, inv_into X f v) \<in> R"
    using order_iso_embed[OF iso iu] unfolding fu by simp
qed

lemma order_iso_poset:"order_iso R X S Y f \<Longrightarrow> poset S Y \<Longrightarrow> order_iso S Y R X (inv_into X f)"
  by (intro order_iso_inv order_iso_inj)

lemma order_iso_strict:
  assumes iso:"order_iso R X S Y f" and inj:"inj_on f X" and xy:"x \<in> X" "y \<in> X"
  shows "x \<le>' y \<and> x \<noteq> y \<longleftrightarrow> (f x, f y) \<in> S \<and> f x \<noteq> f y"
proof -
  have 1:"x \<le>' y \<longleftrightarrow> (f x, f y) \<in> S" by (rule order_iso_embed[OF iso xy])
  have 2:"x \<noteq> y \<longleftrightarrow> f x \<noteq> f y" using inj_onD[OF inj _ xy] by auto
  show ?thesis by (simp only:1 2)
qed

lemma order_iso_strictly_isotone:
  assumes iso:"order_iso R X S Y f" and inj:"inj_on f X"
  shows "strictly_isotone R X S f"
  unfolding strictly_isotone_def
proof (intro ballI impI)
  fix x y assume "x \<in> X" "y \<in> X" "x \<le>' y" "x \<noteq> y"
  then show "(f x, f y) \<in> S \<and> f x \<noteq> f y" using order_iso_strict[OF iso inj, of x y] by simp
qed

end



definition strict_part::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel"
  where "strict_part R X = {(x, y) \<in> X \<times> X. (x, y) \<in> R \<and> x \<noteq> y}"

definition reflcl_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel"
  where "reflcl_on S X = {(x, y) \<in> X \<times> X. (x, y) \<in> S \<or> x = y}"

lemma strict_part_iff[simp]:"(x, y) \<in> strict_part R X \<longleftrightarrow> x \<in> X \<and> y \<in> X \<and> (x, y) \<in> R \<and> x \<noteq> y"
  and reflcl_on_iff[simp]:"(x, y) \<in> reflcl_on S X \<longleftrightarrow> x \<in> X \<and> y \<in> X \<and> ((x, y) \<in> S \<or> x = y)"
  by (auto simp:strict_part_def reflcl_on_def)



locale csup_semilattice = poset +
  assumes ex_csup:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s"

locale cinf_semilattice = poset +
  assumes ex_cinf:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X A s"

sublocale csup_semilattice \<subseteq> sup_semilattice
  by unfold_locales (simp add:ex_csup)

sublocale cinf_semilattice \<subseteq> inf_semilattice
  by unfold_locales (simp add:ex_cinf)

sublocale csup_semilattice \<subseteq> dual:cinf_semilattice "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "cinf_semilattice (dual R) X"
    by unfold_locales (simp add:ex_csup)
qed (simp_all add:dual_ops)

sublocale cinf_semilattice \<subseteq> dual:csup_semilattice "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "csup_semilattice (dual R) X"
    by unfold_locales (simp add:ex_cinf)
qed (simp_all add:dual_ops)

sublocale complete_lattice_on \<subseteq> csup_semilattice
  by unfold_locales (simp add:ex_SupIn)

sublocale complete_lattice_on \<subseteq> cinf_semilattice
  by unfold_locales (simp add:ex_InfIn)

context csup_semilattice
begin

lemma csup_SupIn:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (SupIn A)"
  by (rule is_sup_SupIn[OF ex_csup])

lemma csup_SupIn_base:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> SupIn A \<in> X"
  and csup_SupIn_upper:"\<lbrakk>A \<subseteq> X; A \<noteq> {}; a \<in> A\<rbrakk> \<Longrightarrow> a \<le>' SupIn A"
  and csup_SupIn_least:"\<lbrakk>A \<subseteq> X; A \<noteq> {}; b \<in> X; \<And>a. a \<in> A \<Longrightarrow> a \<le>' b\<rbrakk> \<Longrightarrow> SupIn A \<le>' b"
  using csup_SupIn[of A] by (auto simp:is_sup_iff)

lemma csup_SupIn_iso:"\<lbrakk>A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> SupIn A \<le>' SupIn B"
  by (rule is_sup_iso[OF csup_SupIn csup_SupIn]) auto

lemma csup_greatest:
  assumes A0:"X \<noteq> {}"
  shows "is_greatest R X (SupIn X)"
  using csup_SupIn[OF _ A0] by (auto simp:is_sup_iff is_greatest_iff)

lemma complete_if_least:
  assumes A0:"is_least R X bt"
  shows "complete_lattice_on R X"
proof(unfold_locales)
  fix A assume A1:"A \<subseteq> X"
  show "\<exists>s. is_sup R X A s"
  proof(cases "A = {}")
    case True
    then have "is_sup R X A bt"
      using A0 by (auto simp:is_sup_iff is_least_iff)
    then show ?thesis
      by blast
  next
    case False
    then show ?thesis
      using ex_csup[OF A1] by simp
  qed
qed

end

lemma (in complete_lattice_on) SupIn_sub_le:
  assumes A0:"complete_lattice_on R Y" and A1:"Y \<subseteq> X" and A2:"A \<subseteq> Y"
  shows "SupIn A \<le>' Sup R Y A"
proof-
  have B0:"is_sup R Y A (Sup R Y A)"
    by (rule poset.is_sup_SupIn[OF complete_lattice_on.axioms(1)[OF A0] complete_lattice_on.ex_SupIn[OF A0 A2]])
  then have B1:"Sup R Y A \<in> X" and B2:"\<And>a. a \<in> A \<Longrightarrow> (a, Sup R Y A) \<in> R"
    using A1 by (auto simp:is_sup_iff)
  show ?thesis
    using B1 B2 A1 A2 by (intro SupIn_least ex_SupIn) auto
qed

lemma (in complete_lattice_on) InfIn_sub_ge:
  assumes A0:"complete_lattice_on R Y" and A1:"Y \<subseteq> X" and A2:"A \<subseteq> Y"
  shows "Inf R Y A \<le>' InfIn A"
proof-
  have B0:"complete_lattice_on (dual R) Y"
  proof-
    interpret sub:complete_lattice_on R Y
      by (rule A0)
    show ?thesis
      by (rule sub.dual.complete_lattice_on_axioms)
  qed
  have "(Sup (dual R) Y A, InfIn A) \<in> R"
    using dual.SupIn_sub_le[OF B0 A1 A2] by simp
  then show ?thesis
    by (simp add:dual_ops)
qed
definition equivs::"'a set \<Rightarrow> 'a rel set"
  where "equivs X = {E. equiv X E}"

lemma equivs_memI:"equiv X E \<Longrightarrow> E \<in> equivs X"
  and equivs_memD:"E \<in> equivs X \<Longrightarrow> equiv X E"
  by (simp_all add:equivs_def)

lemma equivs_base:"equivs X \<subseteq> Pow (X \<times> X)"
  by (auto simp:equivs_def equiv_def refl_on_def)

lemma equivs_whole:"X \<times> X \<in> equivs X"
  by (auto simp:equivs_def equiv_def refl_on_def sym_def trans_def)

lemma equivs_diag:"Id_on X \<in> equivs X"
  by (auto simp:equivs_def equiv_def refl_on_def sym_def trans_def)

lemma equivs_Inter:
  assumes A0:"\<E> \<subseteq> equivs X" and A1:"\<E> \<noteq> {}"
  shows "\<Inter>\<E> \<in> equivs X"
proof-
  have B0:"\<And>E. E \<in> \<E> \<Longrightarrow> E \<subseteq> X \<times> X"
    using A0 equivs_base by blast
  have B1:"\<And>E x. \<lbrakk>E \<in> \<E>; x \<in> X\<rbrakk> \<Longrightarrow> (x, x) \<in> E"
    using A0 by (auto simp:equivs_def equiv_def refl_on_def)
  have B2:"\<And>E x y. \<lbrakk>E \<in> \<E>; (x, y) \<in> E\<rbrakk> \<Longrightarrow> (y, x) \<in> E"
    using A0 by (auto simp:equivs_def equiv_def sym_def)
  have B3:"\<And>E x y z. \<lbrakk>E \<in> \<E>; (x, y) \<in> E; (y, z) \<in> E\<rbrakk> \<Longrightarrow> (x, z) \<in> E"
    using A0 unfolding equivs_def equiv_def trans_def by blast
  have C0:"\<Inter>\<E> \<subseteq> X \<times> X"
    using A1 B0 by blast
  have C1:"\<forall>x\<in>X. (x, x) \<in> \<Inter>\<E>"
    using B1 by blast
  have C2:"\<forall>x y. (x, y) \<in> \<Inter>\<E> \<longrightarrow> (y, x) \<in> \<Inter>\<E>"
    using B2 by blast
  have C3:"\<forall>x y z. (x, y) \<in> \<Inter>\<E> \<longrightarrow> (y, z) \<in> \<Inter>\<E> \<longrightarrow> (x, z) \<in> \<Inter>\<E>"
  proof(intro allI impI)
    fix x y z assume "(x, y) \<in> \<Inter>\<E>" and "(y, z) \<in> \<Inter>\<E>"
    then have "\<And>E. E \<in> \<E> \<Longrightarrow> (x, z) \<in> E"
      using B3 by blast
    then show "(x, z) \<in> \<Inter>\<E>"
      by blast
  qed
  show ?thesis
    unfolding equivs_def equiv_def refl_on_def sym_def trans_def mem_Collect_eq
    using C0 C1 C2 C3 by blast
qed

theorem equivs_moore:"moore_family (X \<times> X) (equivs X)"
  by unfold_locales (simp_all add:equivs_base equivs_whole equivs_Inter)

lemma equivs_clattice:"complete_lattice_on subset_order (equivs X)"
proof-
  interpret m:moore_family "X \<times> X" "equivs X"
    by (rule equivs_moore)
  show ?thesis
    by (rule m.closed.complete_lattice_on_axioms)
qed

lemma equivs_least:"is_least subset_order (equivs X) (Id_on X)"
  and equivs_greatest:"is_greatest subset_order (equivs X) (X \<times> X)"
  using equivs_diag equivs_whole equivs_base by (auto simp:is_least_iff is_greatest_iff equivs_def equiv_def refl_on_def)



lemma galois_connI:
  assumes px:"poset R X" and py:"poset S Y" and fm:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y" and gm:"\<And>y. y \<in> Y \<Longrightarrow> g y \<in> X" and
          af:"antitone R X S f" and ag:"antitone S Y R g" and
          ef:"\<And>x. x \<in> X \<Longrightarrow> (x, g (f x)) \<in> R" and eg:"\<And>y. y \<in> Y \<Longrightarrow> (y, f (g y)) \<in> S"
  shows "galois_conn R X S Y f g"
proof(intro galois_conn.intro galois_conn_axioms.intro px py fm gm)
  fix x y assume xmem:"x \<in> X" and ymem:"y \<in> Y"
  show "(x, g y) \<in> R \<longleftrightarrow> (y, f x) \<in> S"
  proof
    assume "(x, g y) \<in> R"
    then have "(f (g y), f x) \<in> S"
      using af xmem gm[OF ymem] by (simp add:isotone_def)
    then show "(y, f x) \<in> S"
      using poset.trans[OF py eg[OF ymem] _ ymem fm[OF gm[OF ymem]] fm[OF xmem]] by simp
  next
    assume "(y, f x) \<in> S"
    then have "(g (f x), g y) \<in> R"
      using ag ymem fm[OF xmem] by (simp add:isotone_def)
    then show "(x, g y) \<in> R"
      using poset.trans[OF px ef[OF xmem] _ xmem gm[OF fm[OF xmem]] gm[OF ymem]] by simp
  qed
qed
locale strict_poset =
  fixes S::"'a rel" and X::"'a set"
  assumes irrefl:"x \<in> X \<Longrightarrow> (x, x) \<notin> S"
    and trans[trans]:"\<lbrakk>(x, y) \<in> S; (y, z) \<in> S; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (x, z) \<in> S"
begin

lemma asym:"\<lbrakk>(x, y) \<in> S; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (y, x) \<notin> S"
  using trans[of x y x] irrefl[of x] by blast

lemma reflcl_poset:"poset (reflcl_on S X) X"
  by unfold_locales (auto dest:asym intro:trans)

lemma strict_part_reflcl:assumes S:"S \<subseteq> X \<times> X" shows "strict_part (reflcl_on S X) X = S"
proof -
  have "(x, y) \<in> S \<Longrightarrow> x \<noteq> y" for x y using irrefl[of x] S by (auto simp:subset_iff)
  then show ?thesis using S by (auto simp:subset_iff)
qed

end

context poset
begin

abbreviation lt::"'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "<''" 50) where "x <' y \<equiv> x \<le>' y \<and> x \<noteq> y"

lemma lt_le_trans:assumes "x <' y" "y \<le>' z" "x \<in> X" "y \<in> X" "z \<in> X" shows "x <' z"
proof
  show "x \<le>' z" using assms by (blast intro:trans)
  show "x \<noteq> z" using assms by (blast intro:antisym)
qed

lemma le_lt_trans:assumes "x \<le>' y" "y <' z" "x \<in> X" "y \<in> X" "z \<in> X" shows "x <' z"
proof
  show "x \<le>' z" using assms by (blast intro:trans)
  show "x \<noteq> z" using assms by (blast intro:antisym)
qed

lemma lt_trans:assumes "x <' y" "y <' z" "x \<in> X" "y \<in> X" "z \<in> X" shows "x <' z"
proof
  show "x \<le>' z" using assms by (blast intro:trans)
  show "x \<noteq> z" using assms by (blast intro:antisym)
qed

lemma lt_asym:"\<lbrakk>x <' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> \<not> y <' x"
  by (blast intro:antisym)

lemma lt_irrefl:"\<not> x <' x"
  by simp

lemma strict_part_strict_poset:"strict_poset (strict_part R X) X"
proof unfold_locales
  fix x y z assume "(x, y) \<in> strict_part R X" "(y, z) \<in> strict_part R X" "x \<in> X" "y \<in> X" "z \<in> X"
  then show "(x, z) \<in> strict_part R X" using lt_trans[of x y z] by simp
qed simp

lemma reflcl_strict_part:"R \<subseteq> X \<times> X \<Longrightarrow> reflcl_on (strict_part R X) X = R"
  by auto

lemma strict_part_poset:"poset (reflcl_on (strict_part R X) X) X"
  by (rule strict_poset.reflcl_poset[OF strict_part_strict_poset])

end



locale distributive_lattice = lattice_on +
  assumes distrib:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<and>' (b \<or>' c) = (a \<and>' b) \<or>' (a \<and>' c)"
begin

lemma distrib_dual:assumes "a \<in> X" "b \<in> X" "c \<in> X"
  shows "a \<or>' (b \<and>' c) = (a \<or>' b) \<and>' (a \<or>' c)"
proof -
  note X = assms
  have 2:"(a \<or>' b) \<and>' a = a" by (subst inf_commute) (rule inf_absorb[OF X(1,2)])
  have 3:"(a \<or>' b) \<and>' c = (c \<and>' a) \<or>' (c \<and>' b)" by (subst inf_commute) (rule distrib[OF X(3,1,2)])
  have 5:"a \<or>' (a \<and>' c) = a" by (rule sup_absorb[OF X(1,3)])
  have "(a \<or>' b) \<and>' (a \<or>' c) = ((a \<or>' b) \<and>' a) \<or>' ((a \<or>' b) \<and>' c)" using X by (intro distrib) auto
  also have "\<dots> = a \<or>' ((c \<and>' a) \<or>' (c \<and>' b))" by (simp only:2 3)
  also have "\<dots> = (a \<or>' (a \<and>' c)) \<or>' (b \<and>' c)"
    using X by (simp add:sup_assoc[symmetric] inf_commute[of c a] inf_commute[of c b])
  also have "\<dots> = a \<or>' (b \<and>' c)" by (simp only:5)
  finally show ?thesis by (rule sym)
qed

end

sublocale distributive_lattice \<subseteq> dual:distributive_lattice "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "distributive_lattice (dual R) X"
    by unfold_locales (simp add:dual_ops distrib_dual)
qed (simp_all add:dual_ops)

lemma distributive_latticeI_dual:
  assumes "lattice_on R X" and "\<And>a b c. \<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sup R X a (inf R X b c) = inf R X (sup R X a b) (sup R X a c)"
  shows "distributive_lattice R X"
proof -
  interpret lattice_on R X by fact
  interpret d:distributive_lattice "dual R" X
    by (rule distributive_lattice.intro[OF dual.lattice_on_axioms])
       (rule distributive_lattice_axioms.intro, simp add:dual_ops assms(2))
  show ?thesis using d.dual.distributive_lattice_axioms by simp
qed

context distributive_lattice
begin


lemma inf_SupIn_finite:
  assumes b:"b \<in> X"
  shows "\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> b \<and>' SupIn A = SupIn ((\<lambda>a. b \<and>' a) ` A)"
proof (induct A rule:finite_ne_induct)
  case (singleton x)
  then show ?case using b by simp
next
  case (insert x A)
  have AX:"A \<subseteq> X" and xX:"x \<in> X" using insert(5) by auto
  have fin:"finite ((\<lambda>a. b \<and>' a) ` A)" "(\<lambda>a. b \<and>' a) ` A \<noteq> {}" "(\<lambda>a. b \<and>' a) ` A \<subseteq> X"
    using insert(1,2) AX b by auto
  have "b \<and>' SupIn (insert x A) = b \<and>' (x \<or>' SupIn A)" using insert(1,2) AX xX by (simp add:SupIn_insert)
  also have "\<dots> = (b \<and>' x) \<or>' (b \<and>' SupIn A)" using b xX insert(1,2) AX by (intro distrib) auto
  also have "\<dots> = (b \<and>' x) \<or>' SupIn ((\<lambda>a. b \<and>' a) ` A)" by (simp add:insert(4)[OF AX])
  also have "\<dots> = SupIn (insert (b \<and>' x) ((\<lambda>a. b \<and>' a) ` A))" using fin b xX by (simp add:SupIn_insert)
  finally show ?case by simp
qed

end

lemma (in distributive_lattice) sup_InfIn_finite:
  "\<lbrakk>b \<in> X; finite A; A \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> b \<or>' InfIn A = InfIn ((\<lambda>a. b \<or>' a) ` A)"
  by (rule dual.inf_SupIn_finite)

lemma pow_lattice:"lattice_on subset_order (Pow X)"
proof -
  interpret complete_lattice_on subset_order "Pow X" by (rule pow_complete)
  show ?thesis by (rule lattice_on_axioms)
qed

lemma sup_pow:"\<lbrakk>A \<subseteq> X; B \<subseteq> X\<rbrakk> \<Longrightarrow> sup subset_order (Pow X) A B = A \<union> B"
  by (simp add:sup_def Sup_pow)

lemma inf_pow:assumes "A \<subseteq> X" "B \<subseteq> X" shows "inf subset_order (Pow X) A B = A \<inter> B"
proof -
  have "A \<inter> B \<subseteq> X" using assms by blast
  then show ?thesis using assms by (simp add:inf_def sup_def dual_ops(1) Inf_pow Int_absorb1)
qed

lemma pow_distributive:"distributive_lattice subset_order (Pow X)"
proof (rule distributive_lattice.intro[OF pow_lattice], rule distributive_lattice_axioms.intro)
  fix a b c assume abc:"a \<in> Pow X" "b \<in> Pow X" "c \<in> Pow X"
  then have "b \<union> c \<subseteq> X" "a \<inter> b \<subseteq> X" "a \<inter> c \<subseteq> X" by auto
  then show "inf subset_order (Pow X) a (sup subset_order (Pow X) b c) =
    sup subset_order (Pow X) (inf subset_order (Pow X) a b) (inf subset_order (Pow X) a c)"
    using abc by (simp add:sup_pow inf_pow Int_Un_distrib)
qed



context complete_lattice_on
begin

lemma SupIn_whole_greatest:"is_greatest R X (SupIn X)"
  and SupIn_empty_least:"is_least R X (SupIn {})"
  using is_sup_SupIn[OF ex_SupIn, of X] is_sup_SupIn[OF ex_SupIn, of "{}"]
  by (simp_all add:is_sup_whole_iff is_sup_empty_iff)

theorem knaster_tarski:
  assumes maps:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> X" and iso:"\<And>x y. \<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f x \<le>' f y"
  shows "f (SupIn {x \<in> X. x \<le>' f x}) = SupIn {x \<in> X. x \<le>' f x}"
    and "\<And>x. \<lbrakk>x \<in> X; f x = x\<rbrakk> \<Longrightarrow> x \<le>' SupIn {x \<in> X. x \<le>' f x}"
proof -
  let ?P = "{x \<in> X. x \<le>' f x}"
  let ?s = "SupIn ?P"
  have P:"?P \<subseteq> X" by blast
  note ex = ex_SupIn[OF P]
  have sX:"?s \<in> X" by (rule SupIn_base[OF ex])
  have fsX:"f ?s \<in> X" by (rule maps[OF sX])
  have up:"x \<le>' ?s" if "x \<in> ?P" for x by (rule SupIn_upper[OF ex that])
  have "?s \<le>' f ?s"
  proof (rule SupIn_least[OF ex fsX])
    fix x assume x:"x \<in> ?P"
    then have "x \<le>' f x" and xX:"x \<in> X" by auto
    moreover have "f x \<le>' f ?s" using up[OF x] xX sX by (rule iso)
    ultimately show "x \<le>' f ?s" using xX fsX maps by (blast intro:trans)
  qed
  then have "f ?s \<le>' f (f ?s)" using sX fsX by (rule iso)
  then have "f ?s \<in> ?P" using fsX by simp
  then have "f ?s \<le>' ?s" by (rule up)
  with \<open>?s \<le>' f ?s\<close> show "f ?s = ?s" using sX fsX by (intro antisym)
  show "x \<le>' ?s" if "x \<in> X" "f x = x" for x using that by (intro up) simp
qed

end

context complete_lattice_on
begin

theorem knaster_tarski_least:
  assumes maps:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> X" and iso:"\<And>x y. \<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f x \<le>' f y"
  shows "f (InfIn {x \<in> X. f x \<le>' x}) = InfIn {x \<in> X. f x \<le>' x}"
    and "\<And>x. \<lbrakk>x \<in> X; f x = x\<rbrakk> \<Longrightarrow> InfIn {x \<in> X. f x \<le>' x} \<le>' x"
proof -
  note kt = dual.knaster_tarski[of f]
  show "f (InfIn {x \<in> X. f x \<le>' x}) = InfIn {x \<in> X. f x \<le>' x}"
    by (rule kt(1)) (auto intro:maps iso)
  show "\<And>x. \<lbrakk>x \<in> X; f x = x\<rbrakk> \<Longrightarrow> InfIn {x \<in> X. f x \<le>' x} \<le>' x"
    by (rule kt(2)) (auto intro:maps iso)
qed

end

lemma cantor:"f ` X = Pow X \<Longrightarrow> False"
  using Cantors_theorem by blast

definition covers::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "covers R X x y \<longleftrightarrow> x \<in> X \<and> y \<in> X \<and> (x, y) \<in> R \<and> x \<noteq> y \<and> (\<forall>z\<in>X. (x, z) \<in> R \<and> (z, y) \<in> R \<longrightarrow> z = x \<or> z = y)"

lemma (in poset) covers_iff:
  "\<lbrakk>x \<in> X; y \<in> X; x <' y\<rbrakk> \<Longrightarrow> covers R X x y \<longleftrightarrow> (\<forall>z\<in>X. x <' z \<and> z \<le>' y \<longrightarrow> z = y)"
  by (auto simp:covers_def)



lemma (in poset) closure_range_mono:
  assumes C1:"closure_range R X C1" and C2:"closure_range R X C2" and sub:"C2 \<subseteq> C1" and x:"x \<in> X"
  shows "closure_range.cl R C1 x \<le>' closure_range.cl R C2 x"
proof -
  interpret c1:closure_range R X C1 by fact
  interpret c2:closure_range R X C2 by fact
  have "c2.cl x \<in> C1" using c2.cl_closed[OF x] sub by blast
  then show ?thesis using c2.cl_extensive[OF x] x by (intro c1.cl_least)
qed


context inf_semilattice
begin

lemma filter_inf_closed:"\<lbrakk>filter_on R X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> a \<and>' b \<in> F"
  by (simp add:filter_iff)

lemma filter_base:"filter_on R X F \<Longrightarrow> F \<subseteq> X"
  and filter_ne:"filter_on R X F \<Longrightarrow> F \<noteq> {}"
  and filter_upD:"\<lbrakk>filter_on R X F; a \<in> F; b \<in> X; a \<le>' b\<rbrakk> \<Longrightarrow> b \<in> F"
  by (auto simp:filter_on_def)

lemma filter_finite_inf_closed:"\<lbrakk>filter_on R X F; finite A; A \<noteq> {}; A \<subseteq> F\<rbrakk> \<Longrightarrow> InfIn A \<in> F"
  by (rule finite_inf_closed[OF filter_base]) (auto intro:filter_inf_closed)

lemma filter_whole:"X \<noteq> {} \<Longrightarrow> filter_on R X X"
  by (auto simp:filter_iff)

lemma filter_Inter:
  assumes ne:"\<E> \<noteq> {}" and fil:"\<And>F. F \<in> \<E> \<Longrightarrow> filter_on R X F" and nonempty:"\<Inter>\<E> \<noteq> {}"
  shows "filter_on R X (\<Inter>\<E>)"
  unfolding filter_iff
proof (intro conjI ballI impI nonempty)
  show "\<Inter>\<E> \<subseteq> X" using ne fil filter_base by blast
  show "a \<and>' b \<in> \<Inter>\<E>" if "a \<in> \<Inter>\<E>" "b \<in> \<Inter>\<E>" for a b
    using that fil filter_inf_closed by blast
  show "b \<in> \<Inter>\<E>" if "a \<in> \<Inter>\<E>" "b \<in> X" "a \<le>' b" for a b
    using that fil filter_upD by blast
qed


lemma filter_dir_Union:
  assumes D:"D \<subseteq> filters" and ne:"D \<noteq> {}" and dir:"is_dir subset_order D"
  shows "filter_on R X (\<Union>D)"
  unfolding filter_iff
proof (intro conjI ballI impI)
  have fil:"filter_on R X F" if "F \<in> D" for F using D that by blast
  show "\<Union>D \<subseteq> X" using fil filter_base by blast
  show "\<Union>D \<noteq> {}" using ne fil filter_ne by blast
  show "a \<and>' b \<in> \<Union>D" if "a \<in> \<Union>D" "b \<in> \<Union>D" for a b
  proof -
    from that obtain F G where F:"F \<in> D" "a \<in> F" and G:"G \<in> D" "b \<in> G" by blast
    obtain H where H:"H \<in> D" "F \<subseteq> H" "G \<subseteq> H" using is_dirD[OF dir F(1) G(1)] by auto
    then have "a \<and>' b \<in> H" using F G filter_inf_closed[OF fil[OF H(1)]] by blast
    then show ?thesis using H(1) by blast
  qed
  show "b \<in> \<Union>D" if "a \<in> \<Union>D" "b \<in> X" "a \<le>' b" for a b
    using that fil filter_upD by blast
qed


definition fcl::"'a set \<Rightarrow> 'a set"
  where "fcl A = {x \<in> X. \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> InfIn F \<le>' x}"

lemma fclI:"\<lbrakk>x \<in> X; F \<subseteq> A; finite F; F \<noteq> {}; InfIn F \<le>' x\<rbrakk> \<Longrightarrow> x \<in> fcl A"
  and fclE:"\<lbrakk>x \<in> fcl A; \<And>F. \<lbrakk>x \<in> X; F \<subseteq> A; finite F; F \<noteq> {}; InfIn F \<le>' x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:fcl_def)

lemma fcl_base:"fcl A \<subseteq> X"
  by (auto simp:fcl_def)

lemma fcl_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> fcl A"
proof
  fix a assume "A \<subseteq> X" "a \<in> A"
  then show "a \<in> fcl A" by (intro fclI[of a "{a}"]) auto
qed

lemma fcl_iso:"A \<subseteq> B \<Longrightarrow> fcl A \<subseteq> fcl B"
  using fcl_def by fastforce

lemma fcl_filter:
  assumes A:"A \<subseteq> X" and ne:"A \<noteq> {}"
  shows "filter_on R X (fcl A)"
  unfolding filter_iff
proof (intro conjI ballI impI)
  show "fcl A \<subseteq> X" by (rule fcl_base)
  show "fcl A \<noteq> {}" using fcl_extensive[OF A] ne by blast
next
  fix x y assume "x \<in> fcl A" "y \<in> fcl A"
  then obtain F G where F:"x \<in> X" "F \<subseteq> A" "finite F" "F \<noteq> {}" "InfIn F \<le>' x"
    and G:"y \<in> X" "G \<subseteq> A" "finite G" "G \<noteq> {}" "InfIn G \<le>' y" by (auto simp:fcl_def)
  have FX:"F \<subseteq> X" "G \<subseteq> X" using F G A by blast+
  have "InfIn (F \<union> G) = InfIn F \<and>' InfIn G" using F G FX by (intro InfIn_union)
  also have "\<dots> \<le>' x \<and>' y" using F G FX by (intro inf_iso) auto
  finally show "x \<and>' y \<in> fcl A" using F G by (intro fclI[of _ "F \<union> G"]) auto
next
  fix x y assume "x \<in> fcl A" "y \<in> X" "x \<le>' y"
  then obtain F where F:"x \<in> X" "F \<subseteq> A" "finite F" "F \<noteq> {}" "InfIn F \<le>' x" by (auto simp:fcl_def)
  have iX:"InfIn F \<in> X" using F A by (intro finite_InfIn_base) auto
  have "InfIn F \<le>' y" by (rule trans[OF F(5) \<open>x \<le>' y\<close> iX F(1) \<open>y \<in> X\<close>])
  with F \<open>y \<in> X\<close> show "y \<in> fcl A" by (intro fclI[of _ F]) auto
qed

lemma fcl_least:
  assumes G:"filter_on R X G" and AG:"A \<subseteq> G"
  shows "fcl A \<subseteq> G"
proof
  fix x assume "x \<in> fcl A"
  then obtain F where F:"x \<in> X" "F \<subseteq> A" "finite F" "F \<noteq> {}" "InfIn F \<le>' x" by (auto simp:fcl_def)
  have "InfIn F \<in> G" using F AG by (intro filter_finite_inf_closed[OF G]) auto
  then show "x \<in> G" by (rule filter_upD[OF G _ F(1) F(5)])
qed

lemma fcl_fixed:"filter_on R X F \<Longrightarrow> fcl F = F"
  using fcl_least[of F F] fcl_extensive[of F] filter_base by blast

lemma fcl_idem:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> fcl (fcl A) = fcl A"
  by (rule fcl_fixed[OF fcl_filter])

lemma fcl_is_inf:
  assumes A:"A \<subseteq> X" "A \<noteq> {}"
  shows "is_inf subset_order filters {F \<in> filters. A \<subseteq> F} (fcl A)"
  unfolding is_sup_iff
proof (intro conjI ballI impI)
  show "fcl A \<in> filters" using fcl_filter[OF A] by simp
  show "(G, fcl A) \<in> dual subset_order" if "G \<in> {F \<in> filters. A \<subseteq> F}" for G
    using that by (simp add:fcl_least)
  fix B assume "B \<in> filters" and lb:"\<forall>G\<in>{F \<in> filters. A \<subseteq> F}. (G, B) \<in> dual subset_order"
  have "fcl A \<in> {F \<in> filters. A \<subseteq> F}" using fcl_filter[OF A] fcl_extensive[OF A(1)] by simp
  then show "(fcl A, B) \<in> dual subset_order" using lb by simp
qed

lemma lcro_InfIn_is_sup:
  assumes F:"finite F" "F \<noteq> {}" "F \<subseteq> X"
  shows "is_sup subset_order filters (lcro R X ` F) (lcro R X (InfIn F))"
  unfolding is_sup_iff
proof (intro conjI ballI impI)
  have iX:"InfIn F \<in> X" using F by simp
  show "lcro R X (InfIn F) \<in> filters" using lcro_filter[OF iX] by simp
  show "(U, lcro R X (InfIn F)) \<in> subset_order" if "U \<in> lcro R X ` F" for U
  proof -
    from that obtain f where f:"f \<in> F" "U = lcro R X f" by blast
    have fX:"f \<in> X" using f F by blast
    have "InfIn F \<le>' f" using F f by (intro finite_InfIn_lower)
    then show ?thesis unfolding f(2) using lcro_anti_iff[OF iX fX] by simp
  qed
  fix G assume G:"G \<in> filters" and ub:"\<forall>U\<in>lcro R X ` F. (U, G) \<in> subset_order"
  have G':"filter_on R X G" using G by simp
  have fG:"f \<in> G" if f:"f \<in> F" for f
  proof -
    have "lcro R X f \<subseteq> G" using ub f by auto
    then show ?thesis using lcro_base[of f] f F by blast
  qed
  have iG:"InfIn F \<in> G" using G' F fG by (intro filter_finite_inf_closed) auto
  show "(lcro R X (InfIn F), G) \<in> subset_order"
    unfolding subset_order_iff
  proof
    fix y assume "y \<in> lcro R X (InfIn F)"
    then have "y \<in> X" "InfIn F \<le>' y" by auto
    then show "y \<in> G" by (rule filter_upD[OF G' iG])
  qed
qed

lemma lcro_inf:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> is_sup subset_order filters {lcro R X a, lcro R X b} (lcro R X (a \<and>' b))"
  using lcro_InfIn_is_sup[of "{a, b}"] by (simp add:InfIn_doubleton)

lemma ulbd_up_closed:"up_closed R X (ubd R X (lbd R X A))"
  unfolding up_closed_def
proof (intro ballI impI)
  fix x y assume x:"x \<in> ubd R X (lbd R X A)" and y:"y \<in> X" and xy:"x \<le>' y"
  have "l \<le>' y" if l:"l \<in> lbd R X A" for l
    using x l by (intro trans[OF _ xy _ _ y]) auto
  with y show "y \<in> ubd R X (lbd R X A)" by auto
qed

lemma ulbd_filter:
  assumes A:"A \<subseteq> X" and ne:"ubd R X (lbd R X A) \<noteq> {}"
  shows "filter_on R X (ubd R X (lbd R X A))"
  unfolding filter_iff
proof (intro conjI ballI impI ne)
  show "ubd R X (lbd R X A) \<subseteq> X" by auto
  show "x \<and>' y \<in> ubd R X (lbd R X A)" if "x \<in> ubd R X (lbd R X A)" "y \<in> ubd R X (lbd R X A)" for x y
    using that by (auto intro:inf_greatest)
  show "y \<in> ubd R X (lbd R X A)" if "x \<in> ubd R X (lbd R X A)" "y \<in> X" "x \<le>' y" for x y
    using up_closedD[OF ulbd_up_closed that] .
qed

end

lemma ubd_eq_lgc:"ubd R X A = lgc_from_rel R X A"
  by (auto simp:lgc_from_rel_def)

lemma (in poset) ulbd_closure_op:"closure_op subset_order (Pow X) (\<lambda>A. ubd R X (lbd R X A))"
  and lubd_closure_op:"closure_op subset_order (Pow X) (\<lambda>A. lbd R X (ubd R X A))"
  using double_lgc_from_rel_closure_op[where R = "dual R" and S = X and T = X]
    double_lgc_from_rel_closure_op[where R = R and S = X and T = X]
  by (simp_all add:ubd_eq_lgc comp_def)



context lattice_on
begin

lemma filter_Int:
  assumes F:"filter_on R X F" and G:"filter_on R X G"
  shows "filter_on R X (F \<inter> G)"
  unfolding filter_iff
proof (intro conjI ballI impI)
  show "F \<inter> G \<subseteq> X" using filter_base[OF F] by blast
  obtain a b where a:"a \<in> F" and b:"b \<in> G" using filter_ne[OF F] filter_ne[OF G] by blast
  then have X:"a \<in> X" "b \<in> X" using filter_base[OF F] filter_base[OF G] by blast+
  have "a \<or>' b \<in> F" using filter_upD[OF F a sup_closed[OF X] sup_ge1[OF X]] .
  moreover have "a \<or>' b \<in> G" using filter_upD[OF G b sup_closed[OF X] sup_ge2[OF X]] .
  ultimately show "F \<inter> G \<noteq> {}" by blast
  show "a \<and>' b \<in> F \<inter> G" if "a \<in> F \<inter> G" "b \<in> F \<inter> G" for a b
    using that by (auto intro:filter_inf_closed[OF F] filter_inf_closed[OF G])
  show "b \<in> F \<inter> G" if "a \<in> F \<inter> G" "b \<in> X" "a \<le>' b" for a b
    using that filter_upD[OF F _ that(2,3)] filter_upD[OF G _ that(2,3)] by blast
qed


definition fsup::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "fsup F G = {x \<in> X. \<exists>a\<in>F. \<exists>b\<in>G. a \<and>' b \<le>' x}"

lemma fsupI:"\<lbrakk>x \<in> X; a \<in> F; b \<in> G; a \<and>' b \<le>' x\<rbrakk> \<Longrightarrow> x \<in> fsup F G"
  and fsupE:"\<lbrakk>x \<in> fsup F G; \<And>a b. \<lbrakk>x \<in> X; a \<in> F; b \<in> G; a \<and>' b \<le>' x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:fsup_def)

lemma fsup_base:"fsup F G \<subseteq> X"
  by (auto simp:fsup_def)

lemma fsup_ge1:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> F \<subseteq> fsup F G"
  and fsup_ge2:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> G \<subseteq> fsup F G"
proof -
  assume F:"filter_on R X F" and G:"filter_on R X G"
  obtain b where b:"b \<in> G" using filter_ne[OF G] by blast
  obtain a where a:"a \<in> F" using filter_ne[OF F] by blast
  have aX:"a \<in> X" and bX:"b \<in> X" using a b filter_base[OF F] filter_base[OF G] by blast+
  show "F \<subseteq> fsup F G"
  proof
    fix x assume x:"x \<in> F"
    then have xX:"x \<in> X" using filter_base[OF F] by blast
    show "x \<in> fsup F G" using x b xX bX by (intro fsupI[where a = x and b = b]) auto
  qed
  show "G \<subseteq> fsup F G"
  proof
    fix x assume x:"x \<in> G"
    then have xX:"x \<in> X" using filter_base[OF G] by blast
    show "x \<in> fsup F G" using x a xX aX by (intro fsupI[where a = a and b = x]) auto
  qed
qed

lemma fsup_filter:
  assumes F:"filter_on R X F" and G:"filter_on R X G"
  shows "filter_on R X (fsup F G)"
  unfolding filter_iff
proof (intro conjI ballI impI)
  show "fsup F G \<subseteq> X" by (rule fsup_base)
  show "fsup F G \<noteq> {}" using fsup_ge1[OF F G] filter_ne[OF F] by blast
next
  fix x y assume "x \<in> fsup F G" "y \<in> fsup F G"
  then obtain a b c d where x:"x \<in> X" "a \<in> F" "b \<in> G" "a \<and>' b \<le>' x"
    and y:"y \<in> X" "c \<in> F" "d \<in> G" "c \<and>' d \<le>' y" by (auto simp:fsup_def)
  have X:"a \<in> X" "b \<in> X" "c \<in> X" "d \<in> X" using x y filter_base[OF F] filter_base[OF G] by blast+
  have ac:"a \<and>' c \<in> F" and bd:"b \<and>' d \<in> G" using x y by (auto intro:filter_inf_closed[OF F] filter_inf_closed[OF G])
  have 1:"(a \<and>' c) \<and>' (b \<and>' d) \<le>' (a \<and>' b) \<and>' (c \<and>' d)"
    using X by (intro inf_greatest) (auto intro:le_infI1 le_infI2)
  have 2:"(a \<and>' b) \<and>' (c \<and>' d) \<le>' x \<and>' y" using x y X by (intro inf_iso) auto
  have "(a \<and>' c) \<and>' (b \<and>' d) \<le>' x \<and>' y" by (rule trans[OF 1 2]) (use x y X in auto)
  then show "x \<and>' y \<in> fsup F G" using x y X ac bd by (intro fsupI[where a = "a \<and>' c" and b = "b \<and>' d"]) auto
next
  fix x y assume "x \<in> fsup F G" "y \<in> X" "x \<le>' y"
  then obtain a b where x:"x \<in> X" "a \<in> F" "b \<in> G" "a \<and>' b \<le>' x" by (auto simp:fsup_def)
  have "a \<in> X" "b \<in> X" using x filter_base[OF F] filter_base[OF G] by blast+
  then have "a \<and>' b \<le>' y" by (intro trans[OF x(4) \<open>x \<le>' y\<close>]) (auto simp:x \<open>y \<in> X\<close>)
  with x \<open>y \<in> X\<close> show "y \<in> fsup F G" by (intro fsupI[where a = a and b = b]) auto
qed

lemma fsup_least:
  assumes H:"filter_on R X H" and FH:"F \<subseteq> H" and GH:"G \<subseteq> H"
  shows "fsup F G \<subseteq> H"
proof
  fix x assume "x \<in> fsup F G"
  then obtain a b where x:"x \<in> X" "a \<in> F" "b \<in> G" "a \<and>' b \<le>' x" by (auto simp:fsup_def)
  have "a \<and>' b \<in> H" using x FH GH by (intro filter_inf_closed[OF H]) auto
  then show "x \<in> H" by (rule filter_upD[OF H _ x(1) x(4)])
qed

lemma fsup_is_sup:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> is_sup subset_order filters {F, G} (fsup F G)"
  by (auto simp:is_sup_iff fsup_filter fsup_ge1 fsup_ge2 fsup_least)

lemma fsup_commute:"fsup F G = fsup G F"
  by (auto simp:fsup_def) (metis inf_commute)+

lemma Int_is_inf:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> is_inf subset_order filters {F, G} (F \<inter> G)"
  by (auto simp:is_sup_iff filter_Int)


lemma filters_poset:"poset subset_order filters"
  by unfold_locales auto

lemma filters_lattice:"lattice_on subset_order filters"
  by (rule lattice_on.intro) (unfold_locales, auto intro:fsup_is_sup Int_is_inf)

lemma filters_sup_eq:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> sup subset_order filters F G = fsup F G"
  and filters_inf_eq:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> inf subset_order filters F G = F \<inter> G"
proof -
  interpret fl:lattice_on subset_order filters by (rule filters_lattice)
  show "\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> sup subset_order filters F G = fsup F G"
    unfolding sup_def by (intro fl.SupIn_eqI fsup_is_sup)
  show "\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> inf subset_order filters F G = F \<inter> G"
    unfolding inf_def sup_def dual_ops(1) by (intro fl.InfIn_eqI Int_is_inf)
qed


lemma fsup_lcro:
  assumes F:"filter_on R X F" and a:"a \<in> X"
  shows "fsup F (lcro R X a) = {x \<in> X. \<exists>y\<in>F. y \<and>' a \<le>' x}"
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> fsup F (lcro R X a)"
  then obtain y b where x:"x \<in> X" "y \<in> F" "b \<in> lcro R X a" "y \<and>' b \<le>' x" by (auto simp:fsup_def)
  have yX:"y \<in> X" and bX:"b \<in> X" and ab:"a \<le>' b" using x filter_base[OF F] by auto
  have "y \<and>' a \<le>' y \<and>' b" using yX bX a ab by (intro inf_iso) auto
  then have "y \<and>' a \<le>' x" by (rule trans[OF _ x(4)]) (use x yX bX a in auto)
  then show "x \<in> {x \<in> X. \<exists>y\<in>F. y \<and>' a \<le>' x}" using x by blast
next
  fix x assume "x \<in> {x \<in> X. \<exists>y\<in>F. y \<and>' a \<le>' x}"
  then obtain y where "x \<in> X" "y \<in> F" "y \<and>' a \<le>' x" by blast
  then show "x \<in> fsup F (lcro R X a)" using a by (intro fsupI[where a = y and b = a]) auto
qed

end

context lattice_top
begin

lemma filters_cl_eq:assumes A:"A \<subseteq> X" "A \<noteq> {}" shows "filters.cl A = fcl A"
proof (intro subset_antisym)
  have "fcl A \<in> {c \<in> filters. A \<subseteq> c}" using fcl_filter[OF A] fcl_extensive[OF A(1)] by simp
  then show "filters.cl A \<subseteq> fcl A" unfolding filters.cl_def by (rule Inter_lower)
  show "fcl A \<subseteq> filters.cl A" unfolding filters.cl_def
  proof (rule Inter_greatest)
    fix c assume "c \<in> {c \<in> filters. A \<subseteq> c}"
    then show "fcl A \<subseteq> c" by (intro fcl_least) auto
  qed
qed

lemma filters_cl_empty:"filters.cl {} = {tp}"
proof -
  have "filters.cl {} = \<Inter>filters" by (simp add:filters.cl_def)
  also have "\<dots> = {tp}"
  proof (intro subset_antisym)
    have "lcro R X tp = {tp}" using tp_greatest tp_base by (auto intro:antisym)
    with lcro_filter[OF tp_base] have "{tp} \<in> filters" by simp
    then show "\<Inter>filters \<subseteq> {tp}" by blast
    show "{tp} \<subseteq> \<Inter>filters" using tp_in_filter by blast
  qed
  finally show ?thesis .
qed

lemma filters_SupIn_eq:"\<lbrakk>\<F> \<subseteq> filters; \<F> \<noteq> {}\<rbrakk> \<Longrightarrow> filters.closed.SupIn \<F> = fcl (\<Union>\<F>)"
proof -
  assume F:"\<F> \<subseteq> filters" "\<F> \<noteq> {}"
  then have U:"\<Union>\<F> \<subseteq> X" "\<Union>\<F> \<noteq> {}" using filter_base filter_ne by blast+
  have "filters.closed.SupIn \<F> = filters.cl (\<Union>\<F>)" by (rule filters.SupIn_closed_eq[OF F(1)])
  also have "\<dots> = fcl (\<Union>\<F>)" by (rule filters_cl_eq[OF U])
  finally show ?thesis .
qed

lemma filters_SupIn_pair:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> filters.closed.SupIn {F, G} = fsup F G"
  by (intro filters.closed.SupIn_eqI fsup_is_sup)

lemma filters_InfIn_pair:"\<lbrakk>filter_on R X F; filter_on R X G\<rbrakk> \<Longrightarrow> filters.closed.InfIn {F, G} = F \<inter> G"
  using filters.InfIn_closed_eq[of "{F, G}"] by simp


lemma filters_SupIn_finite:
  assumes F:"\<F> \<subseteq> filters" "\<F> \<noteq> {}" "finite \<F>"
  shows "filters.closed.SupIn \<F> = {x \<in> X. \<exists>g. (\<forall>F\<in>\<F>. g F \<in> F) \<and> InfIn (g ` \<F>) \<le>' x}"
    (is "_ = ?S")
proof -
  have fil:"filter_on R X F" if "F \<in> \<F>" for F using F(1) that by blast
  have UX:"\<Union>\<F> \<subseteq> X" using fil filter_base by blast
  have "fcl (\<Union>\<F>) = ?S"
  proof (intro subset_antisym subsetI)
    fix x assume "x \<in> fcl (\<Union>\<F>)"
    then obtain E where E:"x \<in> X" "E \<subseteq> \<Union>\<F>" "finite E" "E \<noteq> {}" "InfIn E \<le>' x" by (auto simp:fcl_def)
    define g where "g F = (if E \<inter> F = {} then (SOME y. y \<in> F) else InfIn (E \<inter> F))" for F
    have gF:"g F \<in> F" if "F \<in> \<F>" for F
    proof (cases "E \<inter> F = {}")
      case True
      then show ?thesis unfolding g_def using filter_ne[OF fil[OF that]] by (simp add:some_in_eq)
    next
      case False
      have "finite (E \<inter> F)" "E \<inter> F \<subseteq> F" using E(3) by auto
      then have "InfIn (E \<inter> F) \<in> F" using False by (intro filter_finite_inf_closed[OF fil[OF that]])
      then show ?thesis unfolding g_def using False by simp
    qed
    have gX:"g F \<in> X" if "F \<in> \<F>" for F using gF[OF that] fil[OF that] filter_base by blast
    have "InfIn (g ` \<F>) \<le>' InfIn E"
    proof (intro finite_InfIn_greatest)
      show "InfIn (g ` \<F>) \<in> X" using F gX by (intro finite_InfIn_base) auto
      fix e assume e:"e \<in> E"
      then obtain F where Fe:"F \<in> \<F>" "e \<in> F" using E(2) by blast
      have EF:"E \<inter> F \<noteq> {}" "finite (E \<inter> F)" "E \<inter> F \<subseteq> X" using e Fe E(3) UX E(2) by auto
      have 1:"InfIn (g ` \<F>) \<le>' g F" using F gX Fe by (intro finite_InfIn_lower) auto
      have 2:"g F = InfIn (E \<inter> F)" unfolding g_def using EF by simp
      have 3:"InfIn (E \<inter> F) \<le>' e" using EF e Fe by (intro finite_InfIn_lower) auto
      have eX:"e \<in> X" using e E(2) UX by blast
      have gfX:"InfIn (g ` \<F>) \<in> X" using F gX by (intro finite_InfIn_base) auto
      show "InfIn (g ` \<F>) \<le>' e" by (rule trans[OF 1[unfolded 2] 3]) (use gfX eX EF in auto)
    qed (use E UX in auto)
    moreover have "InfIn (g ` \<F>) \<in> X" "InfIn E \<in> X" using F gX E UX by (intro finite_InfIn_base; auto)+
    ultimately have "InfIn (g ` \<F>) \<le>' x" using E(5) E(1) by (intro trans[OF _ E(5)])
    then show "x \<in> ?S" using E(1) gF by blast
  next
    fix x assume "x \<in> ?S"
    then obtain g where g:"x \<in> X" "\<And>F. F \<in> \<F> \<Longrightarrow> g F \<in> F" "InfIn (g ` \<F>) \<le>' x" by blast
    show "x \<in> fcl (\<Union>\<F>)" using g F by (intro fclI[of _ "g ` \<F>"]) auto
  qed
  then show ?thesis using F by (simp add:filters_SupIn_eq)
qed

lemma lcro_InfIn_SupIn:"\<lbrakk>finite F; F \<noteq> {}; F \<subseteq> X\<rbrakk> \<Longrightarrow> filters.closed.SupIn (lcro R X ` F) = lcro R X (InfIn F)"
  by (rule filters.closed.SupIn_eqI) (rule lcro_InfIn_is_sup)

lemma filter_SupIn_lcro:
  assumes F:"filter_on R X F"
  shows "filters.closed.SupIn (lcro R X ` F) = F"
proof-
  have B0:"lcro R X ` F \<subseteq> filters"
    using lcro_filter filter_base[OF F] by auto
  have B1:"lcro R X ` F \<noteq> {}"
    using filter_ne[OF F] by simp
  have B2:"\<Union>(lcro R X ` F) = F"
  proof
    show "\<Union>(lcro R X ` F) \<subseteq> F"
      using F unfolding filter_on_def by (auto simp:lcro_iff)
    show "F \<subseteq> \<Union>(lcro R X ` F)"
    proof
      fix x assume "x \<in> F"
      then have "x \<in> X"
        using filter_base[OF F] by blast
      then have "x \<in> lcro R X x"
        by (simp add:lcro_iff)
      then show "x \<in> \<Union>(lcro R X ` F)"
        using \<open>x \<in> F\<close> by blast
    qed
  qed
  have "filters.closed.SupIn (lcro R X ` F) = fcl F"
    using filters_SupIn_eq[OF B0 B1] B2 by simp
  also have "... = F"
    using fcl_least[OF F] fcl_extensive[OF filter_base[OF F]] by blast
  finally show ?thesis .
qed

lemma filters_Inter_SupIn:
  assumes F:"\<F> \<subseteq> filters" "\<F> \<noteq> {}" "finite \<F>"
  shows "\<Inter>\<F> = {SupIn (g ` \<F>)|g. \<forall>F\<in>\<F>. g F \<in> F}" (is "?L = ?R")
proof
  have fil:"\<And>F. F \<in> \<F> \<Longrightarrow> filter_on R X F"
    using F(1) by blast
  show "?L \<subseteq> ?R"
  proof
    fix x assume L0:"x \<in> ?L"
    obtain F0 where F0:"F0 \<in> \<F>"
      using F(2) by blast
    then have xX:"x \<in> X"
      using L0 filter_base[OF fil[OF F0]] by blast
    have "(\<lambda>F. x) ` \<F> = {x}"
      using F(2) by auto
    then have "x = SupIn ((\<lambda>F. x) ` \<F>)"
      using SupIn_singleton[OF xX] by simp
    moreover have "\<forall>F\<in>\<F>. (\<lambda>F. x) F \<in> F"
      using L0 by blast
    ultimately show "x \<in> ?R"
      by blast
  qed
  show "?R \<subseteq> ?L"
  proof
    fix x assume "x \<in> ?R"
    then obtain g where g:"\<forall>F\<in>\<F>. g F \<in> F" and x:"x = SupIn (g ` \<F>)"
      by blast
    have gX:"g ` \<F> \<subseteq> X"
      using g fil filter_base by blast
    have "\<And>F. F \<in> \<F> \<Longrightarrow> x \<in> F"
    proof-
      fix F assume Fm:"F \<in> \<F>"
      have "g F \<le>' SupIn (g ` \<F>)"
        using F(2,3) gX Fm by (intro finite_SupIn_upper) auto
      moreover have "SupIn (g ` \<F>) \<in> X"
        using F(2,3) gX by simp
      ultimately show "x \<in> F"
        using fil[OF Fm] g Fm x unfolding filter_on_def by blast
    qed
    then show "x \<in> ?L"
      using F(2) by blast
  qed
qed

end


context distributive_lattice
begin

lemma filters_distributive:"distributive_lattice subset_order filters"
proof (rule distributive_lattice.intro[OF filters_lattice], rule distributive_lattice_axioms.intro)
  fix F G H assume "F \<in> filters" "G \<in> filters" "H \<in> filters"
  then have F:"filter_on R X F" and G:"filter_on R X G" and H:"filter_on R X H" by simp_all
  have GH:"filter_on R X (fsup G H)" and FG:"filter_on R X (F \<inter> G)" and FH:"filter_on R X (F \<inter> H)"
    by (intro fsup_filter filter_Int F G H)+
  have "F \<inter> fsup G H \<subseteq> fsup (F \<inter> G) (F \<inter> H)"
  proof
    fix x assume "x \<in> F \<inter> fsup G H"
    then have xF:"x \<in> F" and "x \<in> fsup G H" by auto
    then obtain g h where x:"x \<in> X" "g \<in> G" "h \<in> H" "g \<and>' h \<le>' x" by (auto simp:fsup_def)
    have gX:"g \<in> X" and hX:"h \<in> X" using x filter_base[OF G] filter_base[OF H] by blast+
    have xg:"x \<or>' g \<in> F \<inter> G" and xh:"x \<or>' h \<in> F \<inter> H"
      using filter_upD[OF F xF sup_closed[OF x(1) gX] sup_ge1[OF x(1) gX]]
        filter_upD[OF G x(2) sup_closed[OF x(1) gX] sup_ge2[OF x(1) gX]]
        filter_upD[OF F xF sup_closed[OF x(1) hX] sup_ge1[OF x(1) hX]]
        filter_upD[OF H x(3) sup_closed[OF x(1) hX] sup_ge2[OF x(1) hX]] by blast+
    have e1:"(g \<and>' h) \<or>' x = x" by (rule le_iff_sup[THEN iffD1]) (auto simp:x gX hX)
    have "x = x \<or>' (g \<and>' h)" by (simp only:sup_commute[of x "g \<and>' h"] e1)
    also have "\<dots> = (x \<or>' g) \<and>' (x \<or>' h)" by (rule distrib_dual[OF x(1) gX hX])
    finally have eq:"x = (x \<or>' g) \<and>' (x \<or>' h)" .
    have "(x \<or>' g) \<and>' (x \<or>' h) \<le>' x" by (subst eq[symmetric]) (rule refl[OF x(1)])
    then show "x \<in> fsup (F \<inter> G) (F \<inter> H)" using x xg xh by (intro fsupI[where a = "x \<or>' g" and b = "x \<or>' h"]) auto
  qed
  moreover have "fsup (F \<inter> G) (F \<inter> H) \<subseteq> F \<inter> fsup G H"
  proof -
    have "F \<inter> G \<subseteq> F \<inter> fsup G H" "F \<inter> H \<subseteq> F \<inter> fsup G H" using fsup_ge1[OF G H] fsup_ge2[OF G H] by blast+
    then show ?thesis by (intro fsup_least filter_Int F GH)
  qed
  ultimately have "F \<inter> fsup G H = fsup (F \<inter> G) (F \<inter> H)" by blast
  then show "inf subset_order filters F (sup subset_order filters G H) =
    sup subset_order filters (inf subset_order filters F G) (inf subset_order filters F H)"
    by (simp add:filters_sup_eq filters_inf_eq F G H GH FG FH)
qed

end



context poset
begin

lemma zorn_maximal:
  assumes S:"S \<subseteq> X" and ne:"S \<noteq> {}"
    and chains:"\<And>C. \<lbrakk>C \<subseteq> S; C \<noteq> {}; \<And>a b. \<lbrakk>a \<in> C; b \<in> C\<rbrakk> \<Longrightarrow> a \<le>' b \<or> b \<le>' a\<rbrakk> \<Longrightarrow> \<exists>u\<in>S. \<forall>c\<in>C. c \<le>' u"
  shows "\<exists>m. is_maximal R S m"
proof -
  let ?r = "R \<inter> (S \<times> S)"
  have F:"Field ?r = S" using S by (auto simp:Field_def)
  have sub:"?r \<subseteq> S \<times> S" by auto
  have rf:"\<forall>x\<in>S. (x, x) \<in> ?r" using S by auto
  have tr:"trans_on UNIV ?r"
    unfolding trans_on_def
  proof (intro ballI impI)
    fix x y z assume "(x, y) \<in> ?r" "(y, z) \<in> ?r"
    then show "(x, z) \<in> ?r" using S trans[of x y z] by auto
  qed
  have as:"antisym_on UNIV ?r"
    unfolding antisym_on_def
  proof (intro ballI impI)
    fix x y assume "(x, y) \<in> ?r" "(y, x) \<in> ?r"
    then show "x = y" using S antisym[of x y] by auto
  qed
  have po:"Partial_order ?r"
    unfolding partial_order_on_def preorder_on_def refl_on_def F using sub rf tr as by blast
  have "\<exists>u\<in>Field ?r. \<forall>a\<in>C. (a, u) \<in> ?r" if C:"C \<in> Chains ?r" for C
  proof (cases "C = {}")
    case True
    then show ?thesis using ne F by auto
  next
    case False
    have CS:"C \<subseteq> S" using C by (auto simp:Chains_def)
    have ch:"a \<le>' b \<or> b \<le>' a" if "a \<in> C" "b \<in> C" for a b using C that by (auto simp:Chains_def)
    obtain u where "u \<in> S" "\<forall>c\<in>C. c \<le>' u" using chains[OF CS False ch] by blast
    then show ?thesis using CS F by auto
  qed
  then obtain m where "m \<in> Field ?r" "\<forall>a\<in>Field ?r. (m, a) \<in> ?r \<longrightarrow> a = m"
    using Zorns_po_lemma[OF po] by blast
  then show ?thesis unfolding F by (auto simp:is_maximal_def)
qed

lemma chain_dir:"(\<And>a b. \<lbrakk>a \<in> C; b \<in> C\<rbrakk> \<Longrightarrow> a \<le>' b \<or> b \<le>' a) \<Longrightarrow> C \<subseteq> X \<Longrightarrow> is_dir R C"
  unfolding is_dir_def
proof (intro ballI)
  fix a b assume ch:"\<And>a b. \<lbrakk>a \<in> C; b \<in> C\<rbrakk> \<Longrightarrow> a \<le>' b \<or> b \<le>' a" and C:"C \<subseteq> X" and ab:"a \<in> C" "b \<in> C"
  show "\<exists>c\<in>C. a \<le>' c \<and> b \<le>' c"
  proof (cases "a \<le>' b")
    case True
    then show ?thesis using ab C by (intro bexI[where x = b]) auto
  next
    case False
    then have "b \<le>' a" using ch[OF ab] by simp
    then show ?thesis using ab C by (intro bexI[where x = a]) auto
  qed
qed

end



context sup_semilattice
begin


definition fne_sup_cl::"'a set \<Rightarrow> 'a set"
  where "fne_sup_cl A = {x \<in> X. \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> is_sup R X F x}"

lemma fne_sup_cl_iff:
  assumes A:"A \<subseteq> X"
  shows "x \<in> fne_sup_cl A \<longleftrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> x = SupIn F)"
proof
  assume "x \<in> fne_sup_cl A"
  then obtain F where F:"x \<in> X" "F \<subseteq> A" "finite F" "F \<noteq> {}" "is_sup R X F x" by (auto simp:fne_sup_cl_def)
  then have "x = SupIn F" using SupIn_eqI[OF F(5)] by simp
  with F show "\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> x = SupIn F" by blast
next
  assume "\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> x = SupIn F"
  then obtain F where F:"F \<subseteq> A" "finite F" "F \<noteq> {}" "x = SupIn F" by blast
  have FX:"F \<subseteq> X" using F A by blast
  have "is_sup R X F x" unfolding F(4) by (rule finite_SupIn[OF F(2,3) FX])
  moreover have "x \<in> X" unfolding F(4) using F FX by simp
  ultimately show "x \<in> fne_sup_cl A" unfolding fne_sup_cl_def using F by blast
qed

lemma fne_sup_cl_base:"fne_sup_cl A \<subseteq> X"
  by (auto simp:fne_sup_cl_def)

lemma fne_sup_cl_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> fne_sup_cl A"
proof
  fix a assume "A \<subseteq> X" "a \<in> A"
  then show "a \<in> fne_sup_cl A" unfolding fne_sup_cl_def by (intro CollectI conjI exI[of _ "{a}"]) auto
qed

lemma fne_sup_cl_iso:"A \<subseteq> B \<Longrightarrow> fne_sup_cl A \<subseteq> fne_sup_cl B"
proof-
  assume A0:"A \<subseteq> B"
  show "fne_sup_cl A \<subseteq> fne_sup_cl B"
  proof
    fix x assume A1:"x \<in> fne_sup_cl A"
    show " x \<in> fne_sup_cl B"
      using A0 A1 fne_sup_cl_def by fastforce
  qed
qed

lemma fne_sup_cl_SupIn:assumes "A \<subseteq> X" "F \<subseteq> A" "finite F" "F \<noteq> {}" shows "SupIn F \<in> fne_sup_cl A"
  using assms by (subst fne_sup_cl_iff[OF assms(1)]) blast

lemma fne_sup_cl_idem:
  assumes A:"A \<subseteq> X"
  shows "fne_sup_cl (fne_sup_cl A) = fne_sup_cl A"
proof (intro subset_antisym)
  show "fne_sup_cl A \<subseteq> fne_sup_cl (fne_sup_cl A)" by (rule fne_sup_cl_extensive[OF fne_sup_cl_base])
  show "fne_sup_cl (fne_sup_cl A) \<subseteq> fne_sup_cl A"
  proof
  fix x assume x:"x \<in> fne_sup_cl (fne_sup_cl A)"
  obtain G where G:"G \<subseteq> fne_sup_cl A" "finite G" "G \<noteq> {}" "x = SupIn G"
    using fne_sup_cl_iff[OF fne_sup_cl_base, THEN iffD1, OF x] by blast
  have ex:"\<forall>g\<in>G. \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> SupIn F = g"
  proof
    fix g assume "g \<in> G"
    then have "g \<in> fne_sup_cl A" using G(1) by blast
    then obtain F where "F \<subseteq> A" "finite F" "F \<noteq> {}" "g = SupIn F" using fne_sup_cl_iff[OF A, THEN iffD1] by blast
    then show "\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> SupIn F = g" by (intro exI[of _ F]) simp
  qed
  have "\<exists>Fg. \<forall>g\<in>G. Fg g \<subseteq> A \<and> finite (Fg g) \<and> Fg g \<noteq> {} \<and> SupIn (Fg g) = g" by (rule bchoice[OF ex])
  then obtain Fg where Fg:"\<And>g. g \<in> G \<Longrightarrow> Fg g \<subseteq> A" "\<And>g. g \<in> G \<Longrightarrow> finite (Fg g)"
    "\<And>g. g \<in> G \<Longrightarrow> Fg g \<noteq> {}" "\<And>g. g \<in> G \<Longrightarrow> SupIn (Fg g) = g" by blast
  have FgX:"\<And>g. g \<in> G \<Longrightarrow> Fg g \<subseteq> X" using Fg(1) A by blast
  let ?H = "\<Union>(Fg ` G)"
  have H:"?H \<subseteq> A" "finite ?H" "?H \<noteq> {}" using Fg G(2,3) by (auto simp:finite_UN[OF G(2)])
  have GX:"G \<subseteq> X" using G(1) fne_sup_cl_base by blast
  have sG:"is_sup R X G x" unfolding G(4) using finite_SupIn[OF G(2,3) GX] .
  have img:"SupIn ` (Fg ` G) = G"
  proof
    show "SupIn ` (Fg ` G) \<subseteq> G" using Fg(4) by auto
    show "G \<subseteq> SupIn ` (Fg ` G)"
    proof
      fix g assume g:"g \<in> G"
      then have "g = SupIn (Fg g)" using Fg(4) by simp
      then show "g \<in> SupIn ` (Fg ` G)" using g by (intro image_eqI[of _ _ "Fg g"]) auto
    qed
  qed
  have fam:"is_sup R X (SupIn ` (Fg ` G)) x \<longleftrightarrow> is_sup R X ?H x"
  proof (rule is_sup_families)
    fix B assume B:"B \<in> Fg ` G"
    then obtain g where g:"g \<in> G" "B = Fg g" by blast
    show "B \<subseteq> X" using FgX[OF g(1)] g(2) by simp
    show "\<exists>s. is_sup R X B s" unfolding g(2) using Fg(2,3)[OF g(1)] FgX[OF g(1)] by (intro finite_sup_ex)
  qed
  have sH:"is_sup R X ?H x" using fam sG by (simp add:img)
  have xX:"x \<in> X" using sG by (simp add:is_sup_iff)
  show "x \<in> fne_sup_cl A" by (unfold fne_sup_cl_def) (intro CollectI conjI exI[of _ "?H"] xX H sH)
  qed
qed


lemma fne_sup_cl_closure_op:"closure_op subset_order (Pow X) fne_sup_cl"
  by unfold_locales (auto simp:fne_sup_cl_base fne_sup_cl_extensive fne_sup_cl_iso fne_sup_cl_idem)

lemma fne_sup_cl_dir:assumes A:"A \<subseteq> X" shows "is_dir R (fne_sup_cl A)"
proof (rule is_dirI)
  fix a b assume ab:"a \<in> fne_sup_cl A" "b \<in> fne_sup_cl A"
  obtain F where F:"F \<subseteq> A" "finite F" "F \<noteq> {}" "a = SupIn F" using fne_sup_cl_iff[OF A, THEN iffD1, OF ab(1)] by blast
  obtain G where G:"G \<subseteq> A" "finite G" "G \<noteq> {}" "b = SupIn G" using fne_sup_cl_iff[OF A, THEN iffD1, OF ab(2)] by blast
  have FX:"F \<subseteq> X" "G \<subseteq> X" using F G A by blast+
  have "SupIn (F \<union> G) \<in> fne_sup_cl A" using F G A by (intro fne_sup_cl_SupIn) auto
  moreover have "a \<le>' SupIn (F \<union> G)" "b \<le>' SupIn (F \<union> G)"
    unfolding F(4) G(4) using F G FX by (intro finite_SupIn_iso; auto)+
  ultimately show "\<exists>c\<in>fne_sup_cl A. a \<le>' c \<and> b \<le>' c" by blast
qed

lemma fne_sup_cl_is_sup:assumes A:"A \<subseteq> X" shows "is_sup R X A s \<longleftrightarrow> is_sup R X (fne_sup_cl A) s"
proof
  assume s:"is_sup R X A s"
  then have sX:"s \<in> X" by (simp add:is_sup_iff)
  show "is_sup R X (fne_sup_cl A) s"
    unfolding is_sup_iff
  proof (intro conjI ballI impI sX)
    fix x assume x:"x \<in> fne_sup_cl A"
    obtain F where F:"F \<subseteq> A" "finite F" "F \<noteq> {}" "x = SupIn F" using fne_sup_cl_iff[OF A, THEN iffD1, OF x] by blast
    then show "x \<le>' s" using s A sX by (auto simp:is_sup_iff intro!:finite_SupIn_least)
  next
    fix b assume "b \<in> X" "\<forall>x\<in>fne_sup_cl A. x \<le>' b"
    then have "\<forall>a\<in>A. a \<le>' b" using fne_sup_cl_extensive[OF A] by blast
    then show "s \<le>' b" using s \<open>b \<in> X\<close> by (auto simp:is_sup_iff)
  qed
next
  assume s:"is_sup R X (fne_sup_cl A) s"
  then have sX:"s \<in> X" by (simp add:is_sup_iff)
  show "is_sup R X A s"
    unfolding is_sup_iff
  proof (intro conjI ballI impI sX)
    show "a \<le>' s" if "a \<in> A" for a using s that fne_sup_cl_extensive[OF A] by (auto simp:is_sup_iff)
    fix b assume b:"b \<in> X" and ub:"\<forall>a\<in>A. a \<le>' b"
    have "x \<le>' b" if x:"x \<in> fne_sup_cl A" for x
    proof -
      obtain F where F:"F \<subseteq> A" "finite F" "F \<noteq> {}" "x = SupIn F" using fne_sup_cl_iff[OF A, THEN iffD1, OF x] by blast
      have FX:"F \<subseteq> X" using F A by blast
      show ?thesis unfolding F(4) using F FX b ub by (intro finite_SupIn_least) auto
    qed
    then show "s \<le>' b" using s b by (auto simp:is_sup_iff)
  qed
qed

end

context complete_lattice_on
begin

definition compact::"'a \<Rightarrow> bool"
  where "compact c \<longleftrightarrow> c \<in> X \<and>
    (\<forall>A. A \<subseteq> X \<longrightarrow> A \<noteq> {} \<longrightarrow> c \<le>' SupIn A \<longrightarrow> (\<exists>B. B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> c \<le>' SupIn B))"

abbreviation compacts::"'a set" where "compacts \<equiv> {c. compact c}"

lemma compact_base:"compact c \<Longrightarrow> c \<in> X"
  and compactD:"\<lbrakk>compact c; A \<subseteq> X; A \<noteq> {}; c \<le>' SupIn A\<rbrakk> \<Longrightarrow> \<exists>B. B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> c \<le>' SupIn B"
  and compactI:"\<lbrakk>c \<in> X; \<And>A. \<lbrakk>A \<subseteq> X; A \<noteq> {}; c \<le>' SupIn A\<rbrakk> \<Longrightarrow> \<exists>B. B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> c \<le>' SupIn B\<rbrakk> \<Longrightarrow> compact c"
  by (auto simp:compact_def)

lemma compact_dir:
  assumes c:"compact c" and D:"is_dir R D" "D \<subseteq> X" "D \<noteq> {}" and le:"c \<le>' SupIn D"
  shows "\<exists>d\<in>D. c \<le>' d"
proof -
  obtain B where B:"B \<subseteq> D" "finite B" "B \<noteq> {}" "c \<le>' SupIn B" using compactD[OF c D(2,3) le] by blast
  obtain d where d:"d \<in> D" "\<And>b. b \<in> B \<Longrightarrow> b \<le>' d" using dir_finite_bound[OF D(1,2) B(2,3,1)] by blast
  have dX:"d \<in> X" using d D by blast
  have BX:"B \<subseteq> X" using B D by blast
  have sd:"SupIn B \<le>' d" using B BX dX d by (intro finite_SupIn_least) auto
  have "c \<le>' d" by (rule trans[OF B(4) sd compact_base[OF c] finite_SupIn_base[OF B(2,3) BX] dX])
  then show ?thesis using d by blast
qed

lemma compactI_dir:
  assumes cX:"c \<in> X" and dir:"\<And>D. \<lbrakk>is_dir R D; D \<subseteq> X; D \<noteq> {}; c \<le>' SupIn D\<rbrakk> \<Longrightarrow> \<exists>d\<in>D. c \<le>' d"
  shows "compact c"
proof (rule compactI[OF cX])
  fix A assume A:"A \<subseteq> X" "A \<noteq> {}" and le:"c \<le>' SupIn A"
  have D:"is_dir R (fne_sup_cl A)" "fne_sup_cl A \<subseteq> X" "fne_sup_cl A \<noteq> {}"
    using fne_sup_cl_dir[OF A(1)] fne_sup_cl_base fne_sup_cl_extensive[OF A(1)] A(2) by blast+
  have "is_sup R X (fne_sup_cl A) (SupIn A)"
    using fne_sup_cl_is_sup[OF A(1), THEN iffD1, OF is_sup_SupIn[OF ex_SupIn[OF A(1)]]] .
  then have "SupIn (fne_sup_cl A) = SupIn A" by (rule SupIn_eqI)
  with le have "c \<le>' SupIn (fne_sup_cl A)" by simp
  then obtain d where d:"d \<in> fne_sup_cl A" "c \<le>' d" using dir[OF D] by blast
  obtain B where "B \<subseteq> A" "finite B" "B \<noteq> {}" "d = SupIn B" using fne_sup_cl_iff[OF A(1), THEN iffD1, OF d(1)] by blast
  then have "B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> c \<le>' SupIn B" using d(2) by simp
  then show "\<exists>B. B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> c \<le>' SupIn B" ..
qed

lemma compact_iff_dir:
  "compact c \<longleftrightarrow> c \<in> X \<and> (\<forall>D. is_dir R D \<longrightarrow> D \<subseteq> X \<longrightarrow> D \<noteq> {} \<longrightarrow> c \<le>' SupIn D \<longrightarrow> (\<exists>d\<in>D. c \<le>' d))"
  using compact_dir compactI_dir compact_base by blast

lemma bot_compact:"compact (SupIn {})"
proof (rule compactI)
  show "SupIn {} \<in> X" by (rule SupIn_base[OF ex_SupIn]) simp
  fix A assume "A \<subseteq> X" "A \<noteq> {}"
  then obtain a where a:"a \<in> A" "a \<in> X" by blast
  then have "SupIn {} \<le>' SupIn {a}" using SupIn_empty_least by (auto simp:is_greatest_def)
  then show "\<exists>B. B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> SupIn {} \<le>' SupIn B" using a by (intro exI[of _ "{a}"]) auto
qed

lemma compact_sup:
  assumes a:"compact a" and b:"compact b"
  shows "compact (a \<or>' b)"
proof (rule compactI)
  have aX:"a \<in> X" and bX:"b \<in> X" using a b by (auto intro:compact_base)
  then show "a \<or>' b \<in> X" by simp
  fix A assume A:"A \<subseteq> X" "A \<noteq> {}" and le:"a \<or>' b \<le>' SupIn A"
  have sA:"SupIn A \<in> X" by (rule SupIn_base[OF ex_SupIn[OF A(1)]])
  have "a \<le>' SupIn A" "b \<le>' SupIn A" using le aX bX sA by simp_all
  then obtain B1 B2 where B1:"B1 \<subseteq> A" "finite B1" "B1 \<noteq> {}" "a \<le>' SupIn B1"
    and B2:"B2 \<subseteq> A" "finite B2" "B2 \<noteq> {}" "b \<le>' SupIn B2" using compactD[OF a A] compactD[OF b A] by blast
  have B1X:"B1 \<subseteq> X" and B2X:"B2 \<subseteq> X" using B1 B2 A by blast+
  have U:"finite (B1 \<union> B2)" "B1 \<union> B2 \<noteq> {}" "B1 \<union> B2 \<subseteq> X" using B1 B2 B1X B2X by auto
  have 1:"SupIn B1 \<le>' SupIn (B1 \<union> B2)" using B1 U by (intro finite_SupIn_iso) auto
  have 2:"SupIn B2 \<le>' SupIn (B1 \<union> B2)" using B2 U by (intro finite_SupIn_iso) auto
  have "a \<le>' SupIn (B1 \<union> B2)" by (rule trans[OF B1(4) 1 aX finite_SupIn_base[OF B1(2,3) B1X] finite_SupIn_base[OF U]])
  moreover have "b \<le>' SupIn (B1 \<union> B2)" by (rule trans[OF B2(4) 2 bX finite_SupIn_base[OF B2(2,3) B2X] finite_SupIn_base[OF U]])
  ultimately have "a \<or>' b \<le>' SupIn (B1 \<union> B2)" using U aX bX by (intro sup_least) auto
  then show "\<exists>B. B \<subseteq> A \<and> finite B \<and> B \<noteq> {} \<and> a \<or>' b \<le>' SupIn B" using B1 B2 by (intro exI[of _ "B1 \<union> B2"]) auto
qed


definition join_dense::"'a set \<Rightarrow> bool"
  where "join_dense D \<longleftrightarrow> D \<subseteq> X \<and> (\<forall>x\<in>X. \<exists>E. E \<subseteq> D \<and> is_sup R X E x)"

lemma join_denseD:
  assumes D:"join_dense D" and x:"x \<in> X"
  shows "is_sup R X {d \<in> D. d \<le>' x} x"
proof -
  obtain E where E:"E \<subseteq> D" "is_sup R X E x" using D x by (auto simp:join_dense_def)
  have DX:"D \<subseteq> X" using D by (simp add:join_dense_def)
  have "E \<subseteq> {d \<in> D. d \<le>' x}" using E by (auto simp:is_sup_iff)
  then show ?thesis using E(2) x by (auto simp:is_sup_iff subset_iff)
qed

lemma join_dense_SupIn:"\<lbrakk>join_dense D; x \<in> X\<rbrakk> \<Longrightarrow> x = SupIn {d \<in> D. d \<le>' x}"
  by (rule sym, rule SupIn_eqI, rule join_denseD)

lemma join_denseI:
  assumes "D \<subseteq> X" and "\<And>x. x \<in> X \<Longrightarrow> is_sup R X {d \<in> D. d \<le>' x} x"
  shows "join_dense D"
  unfolding join_dense_def
proof (intro conjI ballI)
  show "D \<subseteq> X" by fact
  fix x assume "x \<in> X"
  then show "\<exists>E. E \<subseteq> D \<and> is_sup R X E x" using assms(2)[of x] by (intro exI[of _ "{d \<in> D. d \<le>' x}"]) auto
qed

lemma join_dense_iff:"join_dense D \<longleftrightarrow> D \<subseteq> X \<and> (\<forall>x\<in>X. is_sup R X {d \<in> D. d \<le>' x} x)"
  using join_denseD join_denseI join_dense_def by force


lemma join_dense_sep:
  assumes D:"join_dense D" and x:"x \<in> X" and y:"y \<in> X" and nle:"\<not> y \<le>' x"
  shows "\<exists>d\<in>D. d \<le>' y \<and> \<not> d \<le>' x"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<forall>d\<in>{d \<in> D. d \<le>' y}. d \<le>' x" by blast
  then have "y \<le>' x" using join_denseD[OF D y] x by (auto simp:is_sup_iff)
  with nle show False ..
qed

abbreviation compactly_generated::bool where "compactly_generated \<equiv> join_dense compacts"

lemma compactly_generated_iff:"compactly_generated \<longleftrightarrow> (\<forall>x\<in>X. is_sup R X {k \<in> compacts. k \<le>' x} x)"
  using compact_base by (auto simp:join_dense_iff)

end

context poset
begin

definition meet_reducible::"'a \<Rightarrow> bool"
  where "meet_reducible m \<longleftrightarrow> (\<exists>A. A \<subseteq> X \<and> A \<noteq> {} \<and> m \<notin> A \<and> is_inf R X A m)"

definition meet_irr::"'a \<Rightarrow> bool"
  where "meet_irr m \<longleftrightarrow> m \<in> X \<and> \<not> meet_reducible m"

lemma meet_reducibleI:"\<lbrakk>A \<subseteq> X; A \<noteq> {}; m \<notin> A; is_inf R X A m\<rbrakk> \<Longrightarrow> meet_reducible m"
  and meet_irrD:"\<lbrakk>meet_irr m; A \<subseteq> X; A \<noteq> {}; is_inf R X A m\<rbrakk> \<Longrightarrow> m \<in> A"
  and meet_irr_base:"meet_irr m \<Longrightarrow> m \<in> X"
  by (auto simp:meet_reducible_def meet_irr_def)

lemma meet_representation:
  assumes m:"m \<in> X" and red:"meet_reducible m"
  shows "is_inf R X {x \<in> X. m <' x} m"
proof -
  obtain A where A:"A \<subseteq> X" "A \<noteq> {}" "m \<notin> A" "is_inf R X A m" using red by (auto simp:meet_reducible_def)
  have "A \<subseteq> {x \<in> X. m <' x}" using A by (auto simp:is_sup_iff subset_iff)
  with A(4) m show ?thesis by (auto simp:is_sup_iff subset_iff)
qed

lemma meet_irr_iff:
  assumes m:"m \<in> X"
  shows "meet_irr m \<longleftrightarrow> {x \<in> X. m <' x} = {} \<or> \<not> is_inf R X {x \<in> X. m <' x} m"
proof
  show "{x \<in> X. m <' x} = {} \<or> \<not> is_inf R X {x \<in> X. m <' x} m" if "meet_irr m"
    using meet_irrD[OF that, of "{x \<in> X. m <' x}"] by auto
  show "meet_irr m" if "{x \<in> X. m <' x} = {} \<or> \<not> is_inf R X {x \<in> X. m <' x} m"
    unfolding meet_irr_def
  proof (intro conjI m notI)
    assume red:"meet_reducible m"
    then obtain A where A:"A \<subseteq> X" "A \<noteq> {}" "m \<notin> A" "is_inf R X A m" by (auto simp:meet_reducible_def)
    have "A \<subseteq> {x \<in> X. m <' x}" using A by (auto simp:is_sup_iff subset_iff)
    then have "{x \<in> X. m <' x} \<noteq> {}" using A(2) by blast
    moreover have "is_inf R X {x \<in> X. m <' x} m" by (rule meet_representation[OF m red])
    ultimately show False using that by blast
  qed
qed

end



locale algebraic_lattice = complete_lattice_on +
  assumes compactly_generated:"join_dense compacts"
begin

lemma compact_gen:"x \<in> X \<Longrightarrow> is_sup R X {k \<in> compacts. k \<le>' x} x"
  and compact_gen_eq:"x \<in> X \<Longrightarrow> x = SupIn {k \<in> compacts. k \<le>' x}"
  and compact_sep:"\<lbrakk>x \<in> X; y \<in> X; \<not> y \<le>' x\<rbrakk> \<Longrightarrow> \<exists>k. compact k \<and> k \<le>' y \<and> \<not> k \<le>' x"
  using join_denseD[OF compactly_generated] join_dense_SupIn[OF compactly_generated]
    join_dense_sep[OF compactly_generated] by auto

lemma dir_SupIn_compact_avoid:
  assumes k:"compact k" and a:"a \<in> X"
    and D:"D \<subseteq> {q \<in> X. a \<le>' q \<and> \<not> k \<le>' q}" "D \<noteq> {}" "is_dir R D"
  shows "SupIn D \<in> {q \<in> X. a \<le>' q \<and> \<not> k \<le>' q}"
proof -
  have DX:"D \<subseteq> X" using D(1) by blast
  note ex = ex_SupIn[OF DX]
  have sX:"SupIn D \<in> X" by (rule SupIn_base[OF ex])
  obtain d where d:"d \<in> D" using D(2) by blast
  have dS:"a \<le>' d" "d \<in> X" using D(1) d by blast+
  have "a \<le>' SupIn D" by (rule trans[OF dS(1) SupIn_upper[OF ex d] a dS(2) sX])
  moreover have "\<not> k \<le>' SupIn D"
  proof
    assume "k \<le>' SupIn D"
    then obtain d where "d \<in> D" "k \<le>' d" using compact_dir[OF k D(3) DX D(2)] by blast
    then show False using D(1) by blast
  qed
  ultimately show ?thesis using sX by simp
qed

theorem meet_irr_sep:
  assumes a:"a \<in> X" and b:"b \<in> X" and nle:"\<not> b \<le>' a"
  shows "\<exists>m. meet_irr m \<and> a \<le>' m \<and> \<not> b \<le>' m"
proof -
  obtain k where k:"compact k" "k \<le>' b" "\<not> k \<le>' a" using compact_sep[OF a b nle] by blast
  have kX:"k \<in> X" using k by (simp add:compact_base)
  let ?S = "{q \<in> X. a \<le>' q \<and> \<not> k \<le>' q}"
  have S:"?S \<subseteq> X" and ne:"?S \<noteq> {}" using a k by auto
  have "\<exists>m. is_maximal R ?S m"
  proof (rule zorn_maximal[OF S ne])
    fix C assume C:"C \<subseteq> ?S" "C \<noteq> {}" and ch:"\<And>x y. \<lbrakk>x \<in> C; y \<in> C\<rbrakk> \<Longrightarrow> x \<le>' y \<or> y \<le>' x"
    have CX:"C \<subseteq> X" using C(1) by blast
    have "SupIn C \<in> ?S" using dir_SupIn_compact_avoid[OF k(1) a C chain_dir[OF ch CX]] .
    then show "\<exists>u\<in>?S. \<forall>c\<in>C. c \<le>' u" using SupIn_upper[OF ex_SupIn[OF CX]] by blast
  qed
  then obtain m where m:"is_maximal R ?S m" ..
  have mS:"m \<in> X" "a \<le>' m" "\<not> k \<le>' m" using m by (auto simp:is_maximal_def)
  have "meet_irr m"
    unfolding meet_irr_def meet_reducible_def
  proof (intro conjI notI mS(1), elim exE conjE)
    fix A assume A:"A \<subseteq> X" "A \<noteq> {}" "m \<notin> A" "is_inf R X A m"
    have "k \<le>' q" if q:"q \<in> A" for q
    proof -
      have qX:"q \<in> X" using q A(1) by blast
      have mq:"m \<le>' q" using q A(4) by (auto simp:is_sup_iff)
      have "a \<le>' q" by (rule trans[OF mS(2) mq a mS(1) qX])
      moreover have "q \<noteq> m" using q A(3) by blast
      ultimately have "q \<notin> ?S" using m mq qX by (auto simp:is_maximal_def)
      then show ?thesis using qX \<open>a \<le>' q\<close> by simp
    qed
    then have "k \<le>' m" using A(4) kX by (auto simp:is_sup_iff)
    with mS(3) show False ..
  qed
  moreover have "\<not> b \<le>' m"
  proof
    assume "b \<le>' m"
    then have "k \<le>' m" by (rule trans[OF k(2) _ kX b mS(1)])
    with mS(3) show False ..
  qed
  ultimately show ?thesis using mS by blast
qed

theorem meet_irr_rep:
  assumes a:"a \<in> X"
  shows "is_inf R X {m \<in> X. meet_irr m \<and> a \<le>' m} a"
  unfolding is_sup_iff
proof (intro conjI ballI impI a)
  show "(m, a) \<in> dual R" if "m \<in> {m \<in> X. meet_irr m \<and> a \<le>' m}" for m using that by simp
  fix b assume b:"b \<in> X" and lb:"\<forall>m\<in>{m \<in> X. meet_irr m \<and> a \<le>' m}. (m, b) \<in> dual R"
  show "(a, b) \<in> dual R"
  proof (rule ccontr)
    assume "\<not> (a, b) \<in> dual R"
    then have "\<not> b \<le>' a" by simp
    then obtain m where "meet_irr m" "a \<le>' m" "\<not> b \<le>' m" using meet_irr_sep[OF a b] by blast
    with lb show False using meet_irr_base by auto
  qed
qed

theorem meet_irr_rep_eq:"a \<in> X \<Longrightarrow> a = InfIn {m \<in> X. meet_irr m \<and> a \<le>' m}"
  by (rule sym, rule InfIn_eqI, rule meet_irr_rep)

end


locale algebraic_closure_system = moore_family +
  assumes dir_Union:"\<lbrakk>D \<subseteq> C; D \<noteq> {}; is_dir subset_order D\<rbrakk> \<Longrightarrow> \<Union>D \<in> C"
begin

lemma SupIn_dir:"\<lbrakk>D \<subseteq> C; D \<noteq> {}; is_dir subset_order D\<rbrakk> \<Longrightarrow> closed.SupIn D = \<Union>D"
  by (simp add:SupIn_closed_eq dir_Union)

lemma cl_finite_compact:
  assumes F:"F \<subseteq> X" "finite F"
  shows "closed.compact (cl F)"
proof (rule closed.compactI_dir)
  show "cl F \<in> C" using F by simp
  fix D assume D:"is_dir subset_order D" "D \<subseteq> C" "D \<noteq> {}" and le:"cl F \<subseteq> closed.SupIn D"
  have "F \<subseteq> \<Union>D" using subset_trans[OF cl_extensive[of F] le] SupIn_dir[OF D(2,3,1)] by simp
  then obtain \<B> where B:"finite \<B>" "\<B> \<subseteq> D" "F \<subseteq> \<Union>\<B>" using finite_subset_Union[OF F(2)] by blast
  show "\<exists>d\<in>D. cl F \<subseteq> d"
  proof (cases "\<B> = {}")
    case True
    obtain d where d:"d \<in> D" using D(3) by blast
    have "cl F \<subseteq> d" using B True d D(2) by (intro cl_least) auto
    then show ?thesis using d by auto
  next
    case False
    obtain d where d:"d \<in> D" "\<And>b. b \<in> \<B> \<Longrightarrow> b \<subseteq> d"
      using closed.dir_finite_bound[OF D(1,2) B(1) False B(2)] by blast
    have "F \<subseteq> d" using B(3) d(2) by auto
    then have "cl F \<subseteq> d" using d(1) D(2) by (intro cl_least) auto
    then show ?thesis using d(1) by auto
  qed
qed

lemma closed_is_sup_finite_cls:
  assumes E:"E \<in> C"
  shows "is_sup subset_order C (cl ` {F. F \<subseteq> E \<and> finite F}) E"
  unfolding is_sup_iff
proof (intro conjI ballI impI E)
  have EX:"E \<subseteq> X" using E base by blast
  show "(G, E) \<in> subset_order" if "G \<in> cl ` {F. F \<subseteq> E \<and> finite F}" for G
  proof -
    from that obtain F where "G = cl F" "F \<subseteq> E" by blast
    then show ?thesis using cl_least[OF E] by simp
  qed
  fix G assume G:"G \<in> C" and ub:"\<forall>G'\<in>cl ` {F. F \<subseteq> E \<and> finite F}. (G', G) \<in> subset_order"
  have "x \<in> G" if x:"x \<in> E" for x
  proof -
    have "cl {x} \<subseteq> G" using ub x by auto
    then show ?thesis using cl_extensive[of "{x}"] by blast
  qed
  then show "(E, G) \<in> subset_order" by auto
qed

lemma closed_algebraic:"algebraic_lattice subset_order C"
proof (rule algebraic_lattice.intro[OF closed.complete_lattice_on_axioms], rule algebraic_lattice_axioms.intro)
  show "closed.join_dense closed.compacts"
    unfolding closed.join_dense_def
  proof (intro conjI ballI)
    show "closed.compacts \<subseteq> C" using closed.compact_base by blast
    fix E assume E:"E \<in> C"
    have "cl ` {F. F \<subseteq> E \<and> finite F} \<subseteq> closed.compacts"
      using cl_finite_compact E base by force
    with closed_is_sup_finite_cls[OF E] show "\<exists>D. D \<subseteq> closed.compacts \<and> is_sup subset_order C D E" by blast
  qed
qed

end

sublocale algebraic_closure_system \<subseteq> closed:algebraic_lattice subset_order C
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  by (rule closed_algebraic) simp



definition pfilter_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "pfilter_on R X F \<longleftrightarrow> filter_on R X F \<and> F \<noteq> X"

context poset_bot
begin

lemma bt_in_filter_iff:"filter_on R X F \<Longrightarrow> bt \<in> F \<longleftrightarrow> F = X"
  using bt_least bt_base by (auto simp:filter_on_def)

lemma pfilter_iff:"pfilter F \<longleftrightarrow> pfilter_on R X F"
  by (auto simp:pfilter_def pfilter_on_def bt_in_filter_iff)

end

context sup_semilattice
begin

lemma lcro_sup:assumes "a \<in> X" "b \<in> X" shows "lcro R X (a \<or>' b) = lcro R X a \<inter> lcro R X b"
proof (intro set_eqI iffI)
  fix x assume "x \<in> lcro R X (a \<or>' b)"
  then have x:"x \<in> X" "a \<or>' b \<le>' x" by auto
  then have "a \<le>' x" "b \<le>' x" using sup_le_iff[OF assms x(1)] by simp_all
  then show "x \<in> lcro R X a \<inter> lcro R X b" using x(1) by simp
next
  fix x assume "x \<in> lcro R X a \<inter> lcro R X b"
  then have x:"x \<in> X" "a \<le>' x" "b \<le>' x" by auto
  then have "a \<or>' b \<le>' x" using sup_le_iff[OF assms x(1)] by simp
  then show "x \<in> lcro R X (a \<or>' b)" using x(1) by simp
qed

end

context lattice_on
begin

definition sup_prime::"'a set \<Rightarrow> bool"
  where "sup_prime A \<longleftrightarrow> (\<forall>a\<in>X. \<forall>b\<in>X. a \<or>' b \<in> A \<longrightarrow> a \<in> A \<or> b \<in> A)"

definition elem_sup_prime::"'a \<Rightarrow> bool"
  where "elem_sup_prime x \<longleftrightarrow> x \<in> X \<and> (\<forall>a\<in>X. \<forall>b\<in>X. x \<le>' a \<or>' b \<longrightarrow> x \<le>' a \<or> x \<le>' b)"

definition fin_sup_irr::"'a \<Rightarrow> bool"
  where "fin_sup_irr x \<longleftrightarrow> x \<in> X \<and> (\<forall>a\<in>X. \<forall>b\<in>X. x = a \<or>' b \<longrightarrow> x = a \<or> x = b)"

lemma sup_primeI:"(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; a \<or>' b \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A) \<Longrightarrow> sup_prime A"
  and sup_primeD:"\<lbrakk>sup_prime A; a \<in> X; b \<in> X; a \<or>' b \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (auto simp:sup_prime_def)

lemma sup_prime_whole:"sup_prime X"
  by (simp add:sup_prime_def)


lemma elem_sup_prime_fin_irr:assumes "elem_sup_prime x" shows "fin_sup_irr x"
  unfolding fin_sup_irr_def
proof (intro conjI ballI impI)
  show xX:"x \<in> X" using assms by (simp add:elem_sup_prime_def)
  fix a b assume ab:"a \<in> X" "b \<in> X" and e:"x = a \<or>' b"
  have "x \<le>' a \<or>' b" using e ab by simp
  then have "x \<le>' a \<or> x \<le>' b" using assms ab by (auto simp:elem_sup_prime_def)
  moreover have "a \<le>' x" "b \<le>' x" using e ab by simp_all
  ultimately show "x = a \<or> x = b" using xX ab by (auto intro:antisym)
qed


lemma sup_prime_lcro_iff:"x \<in> X \<Longrightarrow> sup_prime (lcro R X x) \<longleftrightarrow> elem_sup_prime x"
  by (auto simp:sup_prime_def elem_sup_prime_def)


lemma prime_filter_compl_ideal:
  assumes F:"filter_on R X F" and ne:"F \<noteq> X" and prime:"sup_prime F"
  shows "ideal_on R X (X - F)"
  unfolding filter_on_iff_up_closed
proof (intro conjI)
  show "X - F \<subseteq> X" by blast
  show "X - F \<noteq> {}" using ne filter_base[OF F] by blast
  show "is_dir (dual (dual R)) (X - F)"
    unfolding is_dir_def
  proof (intro ballI)
    fix a b assume ab:"a \<in> X - F" "b \<in> X - F"
    then have "a \<or>' b \<notin> F" using sup_primeD[OF prime, of a b] by blast
    then show "\<exists>c\<in>X - F. (a, c) \<in> dual (dual R) \<and> (b, c) \<in> dual (dual R)" using ab by (intro bexI[where x = "a \<or>' b"]) auto
  qed
  show "down_closed R X (X - F)"
    unfolding up_closed_def
  proof (intro ballI impI)
    fix a b assume a:"a \<in> X - F" and b:"b \<in> X" and ba:"(a, b) \<in> dual R"
    then show "b \<in> X - F" using filter_upD[OF F, of b a] by auto
  qed
qed

lemma prime_filter_iff_meet_prime:
  assumes F:"filter_on R X F"
  shows "sup_prime F \<longleftrightarrow> (\<forall>G\<in>filters. \<forall>H\<in>filters. G \<inter> H \<subseteq> F \<longrightarrow> G \<subseteq> F \<or> H \<subseteq> F)"
proof
  assume prime:"sup_prime F"
  show "\<forall>G\<in>filters. \<forall>H\<in>filters. G \<inter> H \<subseteq> F \<longrightarrow> G \<subseteq> F \<or> H \<subseteq> F"
  proof (intro ballI impI, rule ccontr)
    fix G H assume G:"G \<in> filters" and H:"H \<in> filters" and GH:"G \<inter> H \<subseteq> F"
      and n:"\<not> (G \<subseteq> F \<or> H \<subseteq> F)"
    then obtain g h where g:"g \<in> G" "g \<notin> F" and h:"h \<in> H" "h \<notin> F" by blast
    have gX:"g \<in> X" and hX:"h \<in> X" using g h G H filter_base by blast+
    have "g \<or>' h \<in> G" using filter_upD[OF _ g(1) sup_closed[OF gX hX] sup_ge1[OF gX hX]] G by simp
    moreover have "g \<or>' h \<in> H" using filter_upD[OF _ h(1) sup_closed[OF gX hX] sup_ge2[OF gX hX]] H by simp
    ultimately have "g \<or>' h \<in> F" using GH by blast
    then show False using sup_primeD[OF prime gX hX] g h by blast
  qed
next
  assume mp:"\<forall>G\<in>filters. \<forall>H\<in>filters. G \<inter> H \<subseteq> F \<longrightarrow> G \<subseteq> F \<or> H \<subseteq> F"
  show "sup_prime F"
  proof (rule sup_primeI)
    fix a b assume ab:"a \<in> X" "b \<in> X" and s:"a \<or>' b \<in> F"
    have "lcro R X a \<inter> lcro R X b \<subseteq> F"
    proof
      fix y assume "y \<in> lcro R X a \<inter> lcro R X b"
      then have "y \<in> X" "a \<le>' y" "b \<le>' y" by auto
      then have "a \<or>' b \<le>' y" using ab by simp
      then show "y \<in> F" using filter_upD[OF F s \<open>y \<in> X\<close>] by simp
    qed
    then have "lcro R X a \<subseteq> F \<or> lcro R X b \<subseteq> F" using mp lcro_filter[OF ab(1)] lcro_filter[OF ab(2)] by blast
    then show "a \<in> F \<or> b \<in> F" using lcro_base[OF ab(1)] lcro_base[OF ab(2)] by blast
  qed
qed

lemma prime_filter_fin_irr:
  assumes F:"filter_on R X F" and prime:"sup_prime F" and G:"filter_on R X G" and H:"filter_on R X H"
    and eq:"F = G \<inter> H"
  shows "F = G \<or> F = H"
proof -
  have "G \<subseteq> F \<or> H \<subseteq> F" using prime_filter_iff_meet_prime[OF F] prime G H eq by blast
  then show ?thesis using eq by blast
qed

end

context distributive_lattice
begin

lemma fin_irr_elem_sup_prime:
  assumes "fin_sup_irr x"
  shows "elem_sup_prime x"
  unfolding elem_sup_prime_def
proof (intro conjI ballI impI)
  show xX:"x \<in> X" using assms by (simp add:fin_sup_irr_def)
  fix a b assume ab:"a \<in> X" "b \<in> X" and le:"x \<le>' a \<or>' b"
  have e1:"(a \<or>' b) \<and>' x = x" using le_iff_inf[OF sup_closed[OF ab] xX] le by simp
  have "x = x \<and>' (a \<or>' b)" by (simp only:inf_commute[of x "a \<or>' b"] e1)
  also have "\<dots> = (x \<and>' a) \<or>' (x \<and>' b)" by (rule distrib[OF xX ab])
  finally have "x = (x \<and>' a) \<or>' (x \<and>' b)" .
  then have "x = x \<and>' a \<or> x = x \<and>' b"
    using assms[unfolded fin_sup_irr_def] inf_closed[OF xX ab(1)] inf_closed[OF xX ab(2)] by blast
  then show "x \<le>' a \<or> x \<le>' b" using le_iff_inf[OF ab(1) xX] le_iff_inf[OF ab(2) xX] inf_commute by metis
qed

lemma elem_sup_prime_iff_fin_irr:"elem_sup_prime x \<longleftrightarrow> fin_sup_irr x"
  using elem_sup_prime_fin_irr fin_irr_elem_sup_prime by blast

lemma sup_prime_lcro_iff_fin_irr:"x \<in> X \<Longrightarrow> sup_prime (lcro R X x) \<longleftrightarrow> fin_sup_irr x"
  by (simp add:sup_prime_lcro_iff elem_sup_prime_iff_fin_irr)

end



locale lattice_bot = lattice_on + poset_bot
locale bounded_lattice = lattice_top + lattice_bot
locale distributive_lattice_bot = distributive_lattice + lattice_bot
locale distributive_lattice_top = distributive_lattice + lattice_top
locale bounded_distributive_lattice = distributive_lattice_top + distributive_lattice_bot

context lattice_bot
begin

lemma pfilter_filter:"pfilter F \<Longrightarrow> filter_on R X F"
  and pfilter_bt:"pfilter F \<Longrightarrow> bt \<notin> F"
  by (auto simp:pfilter_def)

lemma pfilter_inf_bt:"\<lbrakk>pfilter F; a \<in> F; b \<in> X; a \<and>' b = bt\<rbrakk> \<Longrightarrow> b \<notin> F"
  using filter_inf_closed[OF pfilter_filter] pfilter_bt by metis

end

context distributive_lattice_bot
begin


theorem maximal_pfilter_prime:
  assumes max:"is_maximal subset_order {F. pfilter F} F"
  shows "sup_prime F"
proof (rule sup_primeI, rule ccontr)
  fix a b assume ab:"a \<in> X" "b \<in> X" and s:"a \<or>' b \<in> F" and n:"\<not> (a \<in> F \<or> b \<in> F)"
  have pF:"pfilter F" using max by (simp add:is_maximal_def)
  have F:"filter_on R X F" and btF:"bt \<notin> F" using pF by (simp_all add:pfilter_def)
  have deez:"\<exists>y\<in>F. y \<and>' c = bt" if c:"c \<in> X" "c \<notin> F" for c
  proof -
    let ?G = "fsup F (lcro R X c)"
    have G:"filter_on R X ?G" by (intro fsup_filter F lcro_filter c)
    have FG:"F \<subseteq> ?G" by (rule fsup_ge1[OF F lcro_filter[OF c(1)]])
    have cG:"c \<in> ?G" using fsup_ge2[OF F lcro_filter[OF c(1)]] lcro_base[OF c(1)] by blast
    have "\<not> pfilter ?G"
    proof
      assume "pfilter ?G"
      then have "?G = F" using max FG by (auto simp:is_maximal_def)
      then show False using cG c(2) by simp
    qed
    then have "bt \<in> ?G" using G by (simp add:pfilter_def)
    then obtain y where y:"y \<in> F" "y \<and>' c \<le>' bt" using fsup_lcro[OF F c(1)] by auto
    have "y \<in> X" using y F filter_base by blast
    then have "y \<and>' c = bt" using y c bt_least bt_base by (intro antisym) auto
    then show ?thesis using y by blast
  qed
  obtain y where y:"y \<in> F" "y \<and>' a = bt" using deez[OF ab(1)] n by blast
  obtain z where z:"z \<in> F" "z \<and>' b = bt" using deez[OF ab(2)] n by blast
  have yX:"y \<in> X" and zX:"z \<in> X" using y z F filter_base by blast+
  let ?w = "y \<and>' z"
  have wF:"?w \<in> F" by (rule filter_inf_closed[OF F y(1) z(1)])
  have wX:"?w \<in> X" using yX zX by simp
  have "?w \<and>' (a \<or>' b) = (?w \<and>' a) \<or>' (?w \<and>' b)" by (rule distrib[OF wX ab])
  moreover have "?w \<and>' a \<le>' y \<and>' a" using yX zX ab by (intro inf_iso) auto
  moreover have "?w \<and>' b \<le>' z \<and>' b" using yX zX ab by (intro inf_iso) auto
  ultimately have "?w \<and>' (a \<or>' b) \<le>' bt \<or>' bt"
    using y(2) z(2) wX ab bt_base by (simp add:sup_iso)
  then have "?w \<and>' (a \<or>' b) \<le>' bt" using bt_base by simp
  then have "?w \<and>' (a \<or>' b) = bt" using wX ab bt_least bt_base by (intro antisym) auto
  moreover have "?w \<and>' (a \<or>' b) \<in> F" by (rule filter_inf_closed[OF F wF s])
  ultimately show False using btF by simp
qed


theorem prime_filter_theorem:
  assumes "pfilter F"
  obtains U where "pfilter U" "sup_prime U" "F \<subseteq> U"
proof -
  obtain U where U:"pfilter U" "F \<subseteq> U" and max:"\<And>G. \<lbrakk>pfilter G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U"
    using ultrafilter_lemma[OF assms] by blast
  have "is_maximal subset_order {F. pfilter F} U" using U(1) max by (auto simp:is_maximal_def)
  then have "sup_prime U" by (rule maximal_pfilter_prime)
  then show thesis by (rule that[OF U(1) _ U(2)])
qed

end



context lattice_top
begin

sublocale filters:algebraic_closure_system X filters
proof
  fix D assume "D \<subseteq> filters" "D \<noteq> {}" "is_dir subset_order D"
  then show "\<Union>D \<in> filters" using filter_dir_Union by simp
qed

lemma lcro_cl:"x \<in> X \<Longrightarrow> filters.cl {x} = lcro R X x"
proof -
  assume x:"x \<in> X"
  have "filters.cl {x} = fcl {x}" using x by (intro filters_cl_eq) auto
  also have "\<dots> = lcro R X x"
  proof (intro subset_antisym)
    show "fcl {x} \<subseteq> lcro R X x" by (rule fcl_least[OF lcro_filter[OF x]]) (simp add:x)
    have f:"filter_on R X (fcl {x})" using x by (intro fcl_filter) auto
    have xf:"x \<in> fcl {x}" using fcl_extensive[of "{x}"] x by auto
    show "lcro R X x \<subseteq> fcl {x}"
    proof
      fix y assume "y \<in> lcro R X x"
      then have "y \<in> X" "x \<le>' y" by auto
      then show "y \<in> fcl {x}" by (rule filter_upD[OF f xf])
    qed
  qed
  finally show ?thesis .
qed

theorem compact_filter_iff_principal:
  assumes F:"filter_on R X F"
  shows "filters.closed.compact F \<longleftrightarrow> (\<exists>x\<in>X. F = lcro R X x)"
proof
  assume c:"filters.closed.compact F"
  let ?D = "lcro R X ` F"
  have FX:"F \<subseteq> X" by (rule filter_base[OF F])
  have D:"?D \<subseteq> filters" "?D \<noteq> {}" using FX filter_ne[OF F] lcro_filter by auto
  have dir:"is_dir subset_order ?D"
  proof (rule is_dirI)
    fix U V assume "U \<in> ?D" "V \<in> ?D"
    then obtain a b where ab:"a \<in> F" "b \<in> F" "U = lcro R X a" "V = lcro R X b" by blast
    have abX:"a \<in> X" "b \<in> X" using ab FX by blast+
    have "a \<and>' b \<in> F" by (rule filter_inf_closed[OF F ab(1,2)])
    moreover have "lcro R X a \<subseteq> lcro R X (a \<and>' b)" "lcro R X b \<subseteq> lcro R X (a \<and>' b)"
      using abX by (auto simp:lcro_anti_iff[symmetric])
    ultimately show "\<exists>c\<in>?D. (U, c) \<in> subset_order \<and> (V, c) \<in> subset_order"
      unfolding ab(3,4) by (intro bexI[where x = "lcro R X (a \<and>' b)"]) auto
  qed
  have "filters.closed.SupIn ?D = \<Union>?D" by (rule filters.SupIn_dir[OF D dir])
  also have "\<Union>?D = F"
  proof (intro subset_antisym)
    show "\<Union>?D \<subseteq> F" using filter_upD[OF F] by auto
    show "F \<subseteq> \<Union>?D" using lcro_base FX by blast
  qed
  finally have "F \<subseteq> filters.closed.SupIn ?D" by simp
  then obtain U where "U \<in> ?D" "F \<subseteq> U" using filters.closed.compact_dir[OF c dir D] by blast
  then obtain x where x:"x \<in> F" "F \<subseteq> lcro R X x" by blast
  have "lcro R X x \<subseteq> F" using filter_upD[OF F x(1)] by auto
  with x FX show "\<exists>x\<in>X. F = lcro R X x" by blast
next
  assume "\<exists>x\<in>X. F = lcro R X x"
  then obtain x where x:"x \<in> X" "F = lcro R X x" by blast
  have "filters.closed.compact (filters.cl {x})" using x by (intro filters.cl_finite_compact) auto
  then show "filters.closed.compact F" unfolding x(2) by (simp add:lcro_cl[OF x(1)])
qed

lemma filters_compactly_generated:"filters.closed.join_dense filters.closed.compacts"
  by (rule filters.closed.compactly_generated)

end


context distributive_lattice_top
begin

lemma filters_SupIn_dist:
  assumes F:"\<F> \<subseteq> filters" "\<F> \<noteq> {}" "finite \<F>"
  shows "filters.closed.SupIn \<F> = {InfIn (g ` \<F>)|g. \<forall>F\<in>\<F>. g F \<in> F}" (is "?L = ?R")
proof
  have fil:"\<And>F. F \<in> \<F> \<Longrightarrow> filter_on R X F"
    using F(1) by blast
  show "?L \<subseteq> ?R"
  proof
    fix x assume "x \<in> ?L"
    then obtain g where x:"x \<in> X" and g:"\<forall>F\<in>\<F>. g F \<in> F" and le:"InfIn (g ` \<F>) \<le>' x"
      using filters_SupIn_finite[OF F] by blast
    have gX:"g ` \<F> \<subseteq> X"
      using g fil filter_base by blast
    have iX:"InfIn (g ` \<F>) \<in> X"
      using F(2,3) gX by (intro finite_InfIn_base) auto
    have "x = x \<or>' InfIn (g ` \<F>)"
      using le_iff_sup[OF iX x] le sup_commute[of x] by simp
    also have "... = InfIn ((\<lambda>a. x \<or>' a) ` (g ` \<F>))"
      using F(2,3) gX by (intro sup_InfIn_finite[OF x]) auto
    also have "... = InfIn ((\<lambda>F. x \<or>' g F) ` \<F>)"
      by (simp add:image_image)
    finally have B0:"x = InfIn ((\<lambda>F. x \<or>' g F) ` \<F>)" .
    have "\<forall>F\<in>\<F>. x \<or>' g F \<in> F"
    proof
      fix F assume Fm:"F \<in> \<F>"
      have "g F \<in> X"
        using g Fm gX by blast
      then have "g F \<le>' x \<or>' g F" and "x \<or>' g F \<in> X"
        using x sup_ge2 sup_closed by simp_all
      then show "x \<or>' g F \<in> F"
        using fil[OF Fm] g Fm unfolding filter_on_def by blast
    qed
    then show "x \<in> ?R"
      using B0 by blast
  qed
  show "?R \<subseteq> ?L"
  proof
    fix x assume "x \<in> ?R"
    then obtain g where g:"\<forall>F\<in>\<F>. g F \<in> F" and x:"x = InfIn (g ` \<F>)"
      by blast
    have gX:"g ` \<F> \<subseteq> X"
      using g fil filter_base by blast
    have "InfIn (g ` \<F>) \<in> X"
      using F(2,3) gX by (intro finite_InfIn_base) auto
    then show "x \<in> ?L"
      using filters_SupIn_finite[OF F] g x refl by blast
  qed
qed

lemma filters_SupIn_dist2:
  assumes F:"\<F> \<subseteq> filters" "\<F> \<noteq> {}"
  shows "filters.closed.SupIn \<F> = {InfIn G|G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> \<Union>\<F>}" (is "?L = ?R")
proof
  have fil:"\<And>F. F \<in> \<F> \<Longrightarrow> filter_on R X F"
    using F(1) by blast
  have UX:"\<Union>\<F> \<subseteq> X"
    using fil filter_base by blast
  have B0:"?L = fcl (\<Union>\<F>)"
    by (rule filters_SupIn_eq[OF F])
  show "?L \<subseteq> ?R"
  proof
    fix x assume "x \<in> ?L"
    then obtain G where x:"x \<in> X" and G:"G \<subseteq> \<Union>\<F>" "finite G" "G \<noteq> {}" and le:"InfIn G \<le>' x"
      using B0 by (auto simp:fcl_def)
    have GX:"G \<subseteq> X"
      using G UX by blast
    have iX:"InfIn G \<in> X"
      using G GX by (intro finite_InfIn_base) auto
    have "x = x \<or>' InfIn G"
      using le_iff_sup[OF iX x] le sup_commute[of x] by simp
    also have "... = InfIn ((\<lambda>a. x \<or>' a) ` G)"
      using G GX by (intro sup_InfIn_finite[OF x]) auto
    finally have B1:"x = InfIn ((\<lambda>a. x \<or>' a) ` G)" .
    have "(\<lambda>a. x \<or>' a) ` G \<subseteq> \<Union>\<F>"
    proof
      fix y assume "y \<in> (\<lambda>a. x \<or>' a) ` G"
      then obtain a where a:"a \<in> G" and y:"y = x \<or>' a"
        by blast
      then obtain F where Fm:"F \<in> \<F>" and aF:"a \<in> F"
        using G(1) by blast
      have "a \<in> X"
        using a GX by blast
      then have "a \<le>' x \<or>' a" and "x \<or>' a \<in> X"
        using x sup_ge2 sup_closed by simp_all
      then have "x \<or>' a \<in> F"
        using fil[OF Fm] aF unfolding filter_on_def by blast
      then show "y \<in> \<Union>\<F>"
        using Fm y by blast
    qed
    moreover have "finite ((\<lambda>a. x \<or>' a) ` G)" and "(\<lambda>a. x \<or>' a) ` G \<noteq> {}"
      using G by simp_all
    ultimately show "x \<in> ?R"
      using B1 by blast
  qed
  show "?R \<subseteq> ?L"
  proof
    fix x assume "x \<in> ?R"
    then obtain G where G:"G \<subseteq> \<Union>\<F>" "finite G" "G \<noteq> {}" and x:"x = InfIn G"
      by blast
    have "InfIn G \<in> X"
      using G UX by (intro finite_InfIn_base) auto
    then show "x \<in> ?L"
      using B0 G x refl by (auto simp:fcl_def)
  qed
qed

lemma meet_irr_filter_prime:
  assumes F:"filter_on R X F" and irr:"filters.closed.meet_irr F"
  shows "sup_prime F"
proof (rule sup_primeI, rule ccontr)
  fix a b assume ab:"a \<in> X" "b \<in> X" and s:"a \<or>' b \<in> F" and n:"\<not> (a \<in> F \<or> b \<in> F)"
  interpret fl:distributive_lattice subset_order filters by (rule filters_distributive)
  have la:"lcro R X a \<in> filters" and lb:"lcro R X b \<in> filters" and lab:"lcro R X (a \<or>' b) \<in> filters"
    using lcro_filter ab by auto
  have Ff:"F \<in> filters" using F by simp
  let ?G = "fsup F (lcro R X a)" and ?H = "fsup F (lcro R X b)"
  have G:"filter_on R X ?G" and H:"filter_on R X ?H" using fsup_filter[OF F] lcro_filter ab by auto
  have Gs:"sup subset_order filters F (lcro R X a) = ?G" and Hs:"sup subset_order filters F (lcro R X b) = ?H"
    using filters_sup_eq[OF F lcro_filter[OF ab(1)]] filters_sup_eq[OF F lcro_filter[OF ab(2)]] by simp_all
  have i1:"inf subset_order filters (lcro R X a) (lcro R X b) = lcro R X (a \<or>' b)"
    using filters_inf_eq[OF lcro_filter[OF ab(1)] lcro_filter[OF ab(2)]] lcro_sup[OF ab] by simp
  have i2:"lcro R X (a \<or>' b) \<subseteq> F" using filter_upD[OF F s] by auto
  have i3:"sup subset_order filters F (lcro R X (a \<or>' b)) = F"
    using filters.closed.le_iff_sup[OF lab Ff] i2 filters.closed.sup_commute[of F "lcro R X (a \<or>' b)"] by simp
  have "sup subset_order filters F (inf subset_order filters (lcro R X a) (lcro R X b)) =
    inf subset_order filters (sup subset_order filters F (lcro R X a)) (sup subset_order filters F (lcro R X b))"
    by (rule fl.distrib_dual[OF Ff la lb])
  then have eq:"?G \<inter> ?H = F" unfolding i1 i3 Gs Hs using filters_inf_eq[OF G H] by simp
  have "F \<subseteq> ?G" "F \<subseteq> ?H" using fsup_ge1[OF F lcro_filter[OF ab(1)]] fsup_ge1[OF F lcro_filter[OF ab(2)]] .
  moreover have "a \<in> ?G" "b \<in> ?H"
    using fsup_ge2[OF F lcro_filter[OF ab(1)]] fsup_ge2[OF F lcro_filter[OF ab(2)]] lcro_base[OF ab(1)] lcro_base[OF ab(2)] by blast+
  ultimately have "F \<notin> {?G, ?H}" using n by blast
  moreover have "is_inf subset_order filters {?G, ?H} F" using Int_is_inf[OF G H] eq by simp
  ultimately have "filters.closed.meet_reducible F"
    using G H by (intro filters.closed.meet_reducibleI[of "{?G, ?H}"]) auto
  with irr show False by (simp add:filters.closed.meet_irr_def)
qed

theorem pfilter_Inter_primes:
  assumes F:"filter_on R X F" and ne:"F \<noteq> X"
  shows "F = \<Inter>{P \<in> filters. sup_prime P \<and> P \<noteq> X \<and> F \<subseteq> P}"
proof -
  let ?M = "{P \<in> filters. filters.closed.meet_irr P \<and> F \<subseteq> P}"
  let ?M' = "?M - {X}"
  let ?P = "{P \<in> filters. sup_prime P \<and> P \<noteq> X \<and> F \<subseteq> P}"
  have Ff:"F \<in> filters" using F by simp
  have Xf:"X \<in> filters" using filter_whole tp_base by blast
  have M:"is_inf subset_order filters ?M F" using filters.closed.meet_irr_rep[OF Ff] by simp
  have lbM:"F \<subseteq> P" if "P \<in> ?M" for P using that by blast
  have Mne:"?M \<noteq> {}"
  proof
    assume "?M = {}"
    then have "X \<subseteq> F" using M Xf by (auto simp:is_sup_iff)
    then show False using ne filter_base[OF F] by blast
  qed
  have tpM:"tp \<in> \<Inter>?M" using tp_in_filter by blast
  have "filter_on R X (\<Inter>?M)" using Mne tpM by (intro filter_Inter) auto
  then have "\<Inter>?M \<subseteq> F" using M by (auto simp:is_sup_iff)
  moreover have "F \<subseteq> \<Inter>?M" using lbM by blast
  ultimately have FM:"F = \<Inter>?M" by blast
  have M'ne:"?M' \<noteq> {}"
  proof
    assume "?M' = {}"
    then have "?M = {X}" using Mne by blast
    then show False using FM ne by simp
  qed
  have FM':"F = \<Inter>?M'"
  proof (intro subset_antisym)
    show "F \<subseteq> \<Inter>?M'" using lbM by blast
    show "\<Inter>?M' \<subseteq> F"
    proof
      fix x assume x:"x \<in> \<Inter>?M'"
      obtain P0 where P0:"P0 \<in> ?M'" using M'ne by blast
      have "x \<in> X" using x P0 filter_base by blast
      then have "x \<in> \<Inter>?M" using x by blast
      then show "x \<in> F" by (subst FM)
    qed
  qed
  have sub:"?M' \<subseteq> ?P" using meet_irr_filter_prime by auto
  have 1:"\<Inter>?P \<subseteq> \<Inter>?M'" by (rule Inter_anti_mono[OF sub])
  have 2:"F \<subseteq> \<Inter>?P" by blast
  show ?thesis using 1 2 FM' by (intro subset_antisym) simp_all
qed

end



lemma pow_bounded_distributive:"bounded_distributive_lattice subset_order (Pow X) X {}"
proof -
  interpret d:distributive_lattice subset_order "Pow X" by (rule pow_distributive)
  have top:"lattice_top subset_order (Pow X) X"
    by (rule lattice_top.intro[OF d.lattice_on_axioms]) (unfold_locales, auto)
  have bot:"poset_bot subset_order (Pow X) {}"
    by (rule poset_bot.intro[OF d.poset_axioms]) (unfold_locales, auto)
  show ?thesis
    by (intro bounded_distributive_lattice.intro distributive_lattice_bot.intro distributive_lattice_top.intro
        lattice_bot.intro d.distributive_lattice_axioms d.lattice_on_axioms top bot)
qed

locale powerset =
  fixes X::"'a set"
begin

sublocale pow:bounded_distributive_lattice subset_order "Pow X" X "{}"
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  apply (simp add: pow_bounded_distributive)
  by auto

lemma set_filter_iff:
  "filter_on subset_order (Pow X) F \<longleftrightarrow>
    F \<subseteq> Pow X \<and> F \<noteq> {} \<and> (\<forall>A\<in>F. \<forall>B\<in>F. A \<inter> B \<in> F) \<and> (\<forall>A\<in>F. \<forall>B\<in>Pow X. A \<subseteq> B \<longrightarrow> B \<in> F)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  then have FP:"F \<subseteq> Pow X" and ne:"F \<noteq> {}" and i:"\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> inf subset_order (Pow X) A B \<in> F"
    and up:"\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F" by (auto simp:pow.filter_iff)
  have "A \<inter> B \<in> F" if "A \<in> F" "B \<in> F" for A B
  proof -
    have "A \<subseteq> X" "B \<subseteq> X" using that FP by auto
    then show ?thesis using i[OF that] by (simp add:inf_pow)
  qed
  show ?R
    by (meson FP \<open>\<And>B A. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<inter> B \<in> F\<close> ne up)
next
  assume R:?R
  then have FP:"F \<subseteq> Pow X" by simp
  have i:"inf subset_order (Pow X) A B \<in> F" if "A \<in> F" "B \<in> F" for A B
  proof -
    have "A \<subseteq> X" "B \<subseteq> X" using that FP by auto
    then show ?thesis using R that by (simp add:inf_pow)
  qed
  show ?L
    unfolding pow.filter_iff
  proof (intro conjI ballI impI)
    show "F \<subseteq> Pow X" "F \<noteq> {}" using R by simp_all
    show "inf subset_order (Pow X) a b \<in> F" if "a \<in> F" "b \<in> F" for a b by (rule i[OF that])
    show "b \<in> F" if "a \<in> F" "b \<in> Pow X" "a \<subseteq> b" for a b using R that by blast
  qed
qed

lemma set_filterI:
  "\<lbrakk>F \<subseteq> Pow X; F \<noteq> {}; \<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F; \<And>A B. \<lbrakk>A \<in> F; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F\<rbrakk>
    \<Longrightarrow> filter_on subset_order (Pow X) F"
  by (simp add:set_filter_iff)

lemma set_filter_Int:"\<lbrakk>filter_on subset_order (Pow X) F; A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F"
  and set_filter_up:"\<lbrakk>filter_on subset_order (Pow X) F; A \<in> F; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F"
  and set_filter_whole:"filter_on subset_order (Pow X) F \<Longrightarrow> X \<in> F"
  and set_filter_base:"filter_on subset_order (Pow X) F \<Longrightarrow> F \<subseteq> Pow X"
  by (auto simp:set_filter_iff)

lemma set_filter_Inter:
  assumes fil:"filter_on subset_order (Pow X) F"
  shows "\<lbrakk>finite \<A>; \<A> \<noteq> {}; \<A> \<subseteq> F\<rbrakk> \<Longrightarrow> \<Inter>\<A> \<in> F"
proof (induct \<A> rule:finite_ne_induct)
  case (singleton A)
  then show ?case by simp
next
  case (insert A \<A>)
  then have "A \<in> F" "\<Inter>\<A> \<in> F" by auto
  then have "A \<inter> \<Inter>\<A> \<in> F" by (rule set_filter_Int[OF fil])
  then show ?case by simp
qed


lemma set_pfilter_iff:"pow.pfilter F \<longleftrightarrow> filter_on subset_order (Pow X) F \<and> {} \<notin> F"
  by (simp add:pow.pfilter_def)

lemma set_pfilter_ne:"pow.pfilter F \<Longrightarrow> A \<in> F \<Longrightarrow> A \<noteq> {}"
  by (auto simp:pow.pfilter_def)

lemma set_pfilter_compl:"\<lbrakk>pow.pfilter F; A \<in> F\<rbrakk> \<Longrightarrow> X - A \<notin> F"
  using set_filter_Int[of F A "X - A"] by (auto simp:pow.pfilter_def)

lemma set_pfilter_disj:"\<lbrakk>pow.pfilter F; A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<noteq> {}"
  using set_filter_Int[of F A B] by (auto simp:pow.pfilter_def)

lemma set_pfilter_Inter:
  assumes ne:"\<E> \<noteq> {}" and fil:"\<And>F. F \<in> \<E> \<Longrightarrow> pow.pfilter F"
  shows "pow.pfilter (\<Inter>\<E>)"
proof -
  have "X \<in> \<Inter>\<E>" using fil set_filter_whole by (auto simp:pow.pfilter_def)
  then have "filter_on subset_order (Pow X) (\<Inter>\<E>)" using fil ne by (intro pow.filter_Inter) (auto simp:pow.pfilter_def)
  moreover have "{} \<notin> \<Inter>\<E>" using fil ne by (auto simp:pow.pfilter_def)
  ultimately show ?thesis by (simp add:pow.pfilter_def)
qed


lemma set_lcro:"A \<subseteq> X \<Longrightarrow> lcro subset_order (Pow X) A = {B. A \<subseteq> B \<and> B \<subseteq> X}"
  by auto

lemma set_lcro_pfilter:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> pow.pfilter (lcro subset_order (Pow X) A)"
  by (auto simp:pow.pfilter_def intro:pow.lcro_filter)


lemma finite_set_pfilter_principal:
  assumes fin:"finite X" and F:"pow.pfilter F"
  shows "F = lcro subset_order (Pow X) (\<Inter>F)" and "\<Inter>F \<noteq> {}" and "\<Inter>F \<subseteq> X"
proof -
  have fil:"filter_on subset_order (Pow X) F" using F by (simp add:pow.pfilter_def)
  have FP:"F \<subseteq> Pow X" and Fne:"F \<noteq> {}" using fil by (auto simp:set_filter_iff)
  have finF:"finite F" using fin FP by (simp add:finite_subset)
  have IF:"\<Inter>F \<in> F" by (rule set_filter_Inter[OF fil finF Fne subset_refl])
  show "\<Inter>F \<noteq> {}" by (rule set_pfilter_ne[OF F IF])
  show IX:"\<Inter>F \<subseteq> X" using IF FP by blast
  show "F = lcro subset_order (Pow X) (\<Inter>F)"
  proof (intro subset_antisym subsetI)
    fix A assume "A \<in> F"
    then show "A \<in> lcro subset_order (Pow X) (\<Inter>F)" using FP by auto
  next
    fix A assume "A \<in> lcro subset_order (Pow X) (\<Inter>F)"
    then show "A \<in> F" using set_filter_up[OF fil IF] by auto
  qed
qed

lemma finite_set_pfilters:
  assumes "finite X"
  shows "{F. pow.pfilter F} = {lcro subset_order (Pow X) A | A. A \<subseteq> X \<and> A \<noteq> {}}"
proof (intro subset_antisym subsetI)
  fix F assume "F \<in> {F. pow.pfilter F}"
  then show "F \<in> {lcro subset_order (Pow X) A | A. A \<subseteq> X \<and> A \<noteq> {}}"
    using finite_set_pfilter_principal[OF assms, of F] by auto
next
  fix F assume "F \<in> {lcro subset_order (Pow X) A | A. A \<subseteq> X \<and> A \<noteq> {}}"
  then show "F \<in> {F. pow.pfilter F}" using set_lcro_pfilter by auto
qed


definition ultrafilter::"'a set set \<Rightarrow> bool"
  where "ultrafilter U \<longleftrightarrow> is_maximal subset_order {F. pow.pfilter F} U"

lemma ultrafilter_pfilter:"ultrafilter U \<Longrightarrow> pow.pfilter U"
  and ultrafilter_max:"\<lbrakk>ultrafilter U; pow.pfilter G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U"
  by (auto simp:ultrafilter_def is_maximal_def)

lemma ultrafilter_exists:assumes "pow.pfilter F" shows "\<exists>U. ultrafilter U \<and> F \<subseteq> U"
proof -
  obtain U where "pow.pfilter U" "F \<subseteq> U" "\<And>G. \<lbrakk>pow.pfilter G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U"
    using pow.ultrafilter_lemma[OF assms] by blast
  then show ?thesis by (auto simp:ultrafilter_def is_maximal_def)
qed

lemma ultrafilter_prime:"ultrafilter U \<Longrightarrow> pow.sup_prime U"
  unfolding ultrafilter_def by (rule pow.maximal_pfilter_prime)


lemma finer_pfilter:
  assumes F:"pow.pfilter F" and A:"A \<subseteq> X" and mesh:"\<And>B. B \<in> F \<Longrightarrow> A \<inter> B \<noteq> {}"
  shows "pow.pfilter (pow.fsup F (lcro subset_order (Pow X) A))" and "A \<in> pow.fsup F (lcro subset_order (Pow X) A)"
proof -
  have fil:"filter_on subset_order (Pow X) F" using F by (simp add:pow.pfilter_def)
  have lf:"filter_on subset_order (Pow X) (lcro subset_order (Pow X) A)" using A by (intro pow.lcro_filter) simp
  show "A \<in> pow.fsup F (lcro subset_order (Pow X) A)"
    using pow.fsup_ge2[OF fil lf] A by auto
  have "{} \<notin> pow.fsup F (lcro subset_order (Pow X) A)"
  proof
    assume "{} \<in> pow.fsup F (lcro subset_order (Pow X) A)"
    then obtain B where B:"B \<in> F" "inf subset_order (Pow X) B A \<subseteq> {}"
      using pow.fsup_lcro[OF fil, of A] A by auto
    have "B \<subseteq> X" using B(1) set_filter_base[OF fil] by blast
    then have "B \<inter> A \<subseteq> {}" using B(2) A by (simp add:inf_pow)
    then show False using mesh[OF B(1)] by blast
  qed
  then show "pow.pfilter (pow.fsup F (lcro subset_order (Pow X) A))"
    using pow.fsup_filter[OF fil lf] by (simp add:pow.pfilter_def)
qed


theorem ultrafilter_compl:
  assumes U:"ultrafilter U" and A:"A \<subseteq> X"
  shows "A \<in> U \<or> X - A \<in> U"
proof (rule ccontr)
  assume n:"\<not> (A \<in> U \<or> X - A \<in> U)"
  have pU:"pow.pfilter U" by (rule ultrafilter_pfilter[OF U])
  have fil:"filter_on subset_order (Pow X) U" using pU by (simp add:pow.pfilter_def)
  have "A \<inter> B \<noteq> {}" if B:"B \<in> U" for B
  proof
    assume "A \<inter> B = {}"
    then have "B \<subseteq> X - A" using B set_filter_base[OF fil] by blast
    then have "X - A \<in> U" using set_filter_up[OF fil B] by blast
    with n show False by simp
  qed
  then have "pow.pfilter (pow.fsup U (lcro subset_order (Pow X) A))" "A \<in> pow.fsup U (lcro subset_order (Pow X) A)"
    using finer_pfilter[OF pU A] by blast+
  moreover have "U \<subseteq> pow.fsup U (lcro subset_order (Pow X) A)"
    using pow.fsup_ge1[OF fil pow.lcro_filter] A by auto
  ultimately have "pow.fsup U (lcro subset_order (Pow X) A) = U" using ultrafilter_max[OF U] by blast
  then show False using n \<open>A \<in> pow.fsup U (lcro subset_order (Pow X) A)\<close> by simp
qed

theorem ultrafilter_iff_compl:
  "ultrafilter U \<longleftrightarrow> pow.pfilter U \<and> (\<forall>A\<in>Pow X. A \<in> U \<or> X - A \<in> U)"
proof
  assume U:"ultrafilter U"
  then show "pow.pfilter U \<and> (\<forall>A\<in>Pow X. A \<in> U \<or> X - A \<in> U)" using ultrafilter_pfilter ultrafilter_compl by blast
next
  assume h:"pow.pfilter U \<and> (\<forall>A\<in>Pow X. A \<in> U \<or> X - A \<in> U)"
  show "ultrafilter U"
    unfolding ultrafilter_def is_maximal_def
  proof (intro conjI ballI impI)
    show "U \<in> {F. pow.pfilter F}" using h by simp
    fix G assume G:"G \<in> {F. pow.pfilter F}" and UG0:"(U, G) \<in> subset_order"
    have UG:"U \<subseteq> G" using UG0 by simp
    show "G = U"
    proof (rule ccontr)
      assume "G \<noteq> U"
      then obtain A where A:"A \<in> G" "A \<notin> U" using UG by blast
      have "A \<subseteq> X" using A G set_filter_base by (auto simp:pow.pfilter_def)
      then have "X - A \<in> U" using h A by blast
      then have "X - A \<in> G" using UG by blast
      then show False using set_pfilter_compl[of G A] G A by simp
    qed
  qed
qed

lemma ultrafilter_Un:
  assumes U:"ultrafilter U" and A:"A \<subseteq> X" and B:"B \<subseteq> X" and AB:"A \<union> B \<in> U"
  shows "A \<in> U \<or> B \<in> U"
proof -
  have "sup subset_order (Pow X) A B \<in> U" using AB A B by (simp add:sup_pow)
  then show ?thesis using pow.sup_primeD[OF ultrafilter_prime[OF U]] A B by simp
qed


lemma principal_ultrafilter:
  assumes x:"x \<in> X"
  shows "ultrafilter (lcro subset_order (Pow X) {x})"
  unfolding ultrafilter_iff_compl
proof (intro conjI ballI)
  show "pow.pfilter (lcro subset_order (Pow X) {x})" using x by (intro set_lcro_pfilter) auto
  fix A assume "A \<in> Pow X"
  then show "A \<in> lcro subset_order (Pow X) {x} \<or> X - A \<in> lcro subset_order (Pow X) {x}" using x by auto
qed

lemma principal_ultrafilter_iff:"x \<in> X \<Longrightarrow> A \<in> lcro subset_order (Pow X) {x} \<longleftrightarrow> A \<subseteq> X \<and> x \<in> A"
  by auto

theorem pfilter_Inter_ultrafilters:
  assumes F:"pow.pfilter F"
  shows "F = \<Inter>{U. ultrafilter U \<and> F \<subseteq> U}"
proof (intro subset_antisym subsetI)
  fix A assume "A \<in> F"
  then show "A \<in> \<Inter>{U. ultrafilter U \<and> F \<subseteq> U}" by blast
next
  fix A assume A:"A \<in> \<Inter>{U. ultrafilter U \<and> F \<subseteq> U}"
  obtain U0 where U0:"ultrafilter U0" "F \<subseteq> U0" using ultrafilter_exists[OF F] by blast
  have "A \<in> U0" using A U0 by blast
  then have AX:"A \<subseteq> X" using ultrafilter_pfilter[OF U0(1)] set_filter_base by (auto simp:pow.pfilter_def)
  show "A \<in> F"
  proof (rule ccontr)
    assume nA:"A \<notin> F"
    have fil:"filter_on subset_order (Pow X) F" using F by (simp add:pow.pfilter_def)
    have mesh:"(X - A) \<inter> B \<noteq> {}" if B:"B \<in> F" for B
    proof
      assume "(X - A) \<inter> B = {}"
      then have "B \<subseteq> A" using B set_filter_base[OF fil] by blast
      then have "A \<in> F" by (rule set_filter_up[OF fil B AX])
      with nA show False ..
    qed
    let ?G = "pow.fsup F (lcro subset_order (Pow X) (X - A))"
    have G:"pow.pfilter ?G" "X - A \<in> ?G" using finer_pfilter[OF F _ mesh] by auto
    obtain U where U:"ultrafilter U" "?G \<subseteq> U" using ultrafilter_exists[OF G(1)] by blast
    have "F \<subseteq> U" using pow.fsup_ge1[OF fil pow.lcro_filter] U(2) by auto
    then have "A \<in> U" using A U(1) by blast
    moreover have "X - A \<in> U" using G(2) U(2) by blast
    ultimately show False using set_pfilter_disj[OF ultrafilter_pfilter[OF U(1)]] by blast
  qed
qed

definition mesh::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool"  (infixl "#" 70)
  where "\<A> # \<B> \<longleftrightarrow> (\<forall>A\<in>\<A>. \<forall>B\<in>\<B>. A \<inter> B \<noteq> {})"

lemma mesh_sym:"\<A> # \<B> \<longleftrightarrow> \<B> # \<A>"
  by (auto simp:mesh_def Int_commute)

lemma mesh_sub:"\<lbrakk>\<A> # \<B>; \<A>' \<subseteq> \<A>; \<B>' \<subseteq> \<B>\<rbrakk> \<Longrightarrow> \<A>' # \<B>'"
  by (auto simp:mesh_def)

lemma grill_iff:"B \<in> grill X \<A> \<longleftrightarrow> B \<subseteq> X \<and> (\<forall>A\<in>\<A>. A \<inter> B \<noteq> {})"
  by (auto simp:grill_def lgc_from_rel_def meshes_def)

lemma mesh_iff_grill:"\<A> \<subseteq> Pow X \<Longrightarrow> \<A> # \<B> \<longleftrightarrow> \<A> \<subseteq> grill X \<B>"
  by (auto simp:mesh_def grill_iff Int_commute subset_iff)

lemma grill_base:"grill X \<A> \<subseteq> Pow X"
  by (auto simp:grill_iff)

lemma grill_up_closed:"up_closed subset_order (Pow X) (grill X \<A>)"
  unfolding up_closed_def
proof (intro ballI impI)
  fix a b assume a:"a \<in> grill X \<A>" and b:"b \<in> Pow X" and ab:"(a, b) \<in> subset_order"
  show "b \<in> grill X \<A>"
    unfolding grill_iff
  proof (intro conjI ballI)
    show "b \<subseteq> X" using b by simp
    fix A assume "A \<in> \<A>"
    then have "A \<inter> a \<noteq> {}" using a by (simp add:grill_iff)
    then show "A \<inter> b \<noteq> {}" using ab by auto
  qed
qed

lemma grill_singleton:"x \<in> X \<Longrightarrow> grill X {{x}} = lcro subset_order (Pow X) {x}"
  by (auto simp:grill_iff lcro_iff)

lemma grill_empty:"grill X {} = Pow X"
  and grill_whole:"grill X {X} = {B. B \<subseteq> X \<and> B \<noteq> {}}"
  by (auto simp:grill_iff Int_absorb1)

lemma grill_mem_empty:"{} \<in> \<A> \<Longrightarrow> grill X \<A> = {}"
  by (auto simp:grill_iff)

lemma grill_reform:
  assumes A:"\<A> \<subseteq> Pow X" and up:"up_closed subset_order (Pow X) \<A>" and B:"B \<subseteq> X"
  shows "B \<in> grill X \<A> \<longleftrightarrow> X - B \<notin> \<A>"
proof
  assume "B \<in> grill X \<A>"
  then have "(X - B) \<inter> B \<noteq> {}" if "X - B \<in> \<A>" using that by (auto simp:grill_iff)
  then show "X - B \<notin> \<A>" by blast
next
  assume n:"X - B \<notin> \<A>"
  show "B \<in> grill X \<A>"
    unfolding grill_iff
  proof (intro conjI ballI B)
    fix C assume C:"C \<in> \<A>"
    show "C \<inter> B \<noteq> {}"
    proof
      assume "C \<inter> B = {}"
      then have "C \<subseteq> X - B" using C A by blast
      then have "X - B \<in> \<A>" using up_closedD[OF up C] by auto
      with n show False ..
    qed
  qed
qed


theorem double_grill:
  assumes A:"\<A> \<subseteq> Pow X"
  shows "grill X (grill X \<A>) = \<A> \<longleftrightarrow> up_closed subset_order (Pow X) \<A>"
proof
  assume "grill X (grill X \<A>) = \<A>"
  then show "up_closed subset_order (Pow X) \<A>" using grill_up_closed[of "grill X \<A>"] by simp
next
  assume up:"up_closed subset_order (Pow X) \<A>"
  show "grill X (grill X \<A>) = \<A>"
  proof (intro set_eqI)
    fix B
    show "B \<in> grill X (grill X \<A>) \<longleftrightarrow> B \<in> \<A>"
    proof (cases "B \<subseteq> X")
      case True
      have "B \<in> grill X (grill X \<A>) \<longleftrightarrow> X - B \<notin> grill X \<A>"
        by (rule grill_reform[OF grill_base grill_up_closed True])
      also have "\<dots> \<longleftrightarrow> \<not> (X - (X - B) \<notin> \<A>)" by (simp add:grill_reform[OF A up])
      also have "\<dots> \<longleftrightarrow> B \<in> \<A>" using True by (simp add:Diff_Diff_Int Int_absorb1)
      finally show ?thesis .
    next
      case False
      then show ?thesis using A grill_base[of "grill X \<A>"] by blast
    qed
  qed
qed

lemma grill_union_Inter:"\<AA> \<noteq> {} \<Longrightarrow> grill X (\<Union>\<AA>) = \<Inter>(grill X ` \<AA>)"
  by (auto simp:grill_iff)

lemma grill_Un:"grill X (\<A> \<union> \<B>) = grill X \<A> \<inter> grill X \<B>"
  by (auto simp:grill_iff)

lemma grill_pfilter_iff:
  assumes F:"pow.pfilter F" and B:"B \<subseteq> X"
  shows "B \<in> grill X F \<longleftrightarrow> X - B \<notin> F"
  using F by (intro grill_reform[OF _ _ B]) (auto simp:pow.pfilter_def set_filter_iff up_closed_def)

lemma grill_pfilter_Un:
  assumes F:"pow.pfilter F" and A:"A \<subseteq> X" and B:"B \<subseteq> X" and AB:"A \<union> B \<in> grill X F"
  shows "A \<in> grill X F \<or> B \<in> grill X F"
proof (rule ccontr)
  assume "\<not> (A \<in> grill X F \<or> B \<in> grill X F)"
  then have "X - A \<in> F" "X - B \<in> F" using grill_pfilter_iff[OF F A] grill_pfilter_iff[OF F B] by simp_all
  then have "(X - A) \<inter> (X - B) \<in> F" using set_filter_Int F by (auto simp:pow.pfilter_def)
  then have "X - (A \<union> B) \<in> F" by (simp add:Diff_Un)
  with AB show False using grill_pfilter_iff[OF F] A B by auto
qed

lemma pfilter_mesh_self:assumes "pow.pfilter F" shows "F # F"
  unfolding mesh_def
proof (intro ballI)
  fix A B assume "A \<in> F" "B \<in> F"
  then show "A \<inter> B \<noteq> {}" by (rule set_pfilter_disj[OF assms])
qed

lemma pfilter_sub_grill:"pow.pfilter F \<Longrightarrow> F \<subseteq> grill X F"
  using pfilter_mesh_self mesh_iff_grill set_filter_base by (auto simp:pow.pfilter_def)

theorem grill_of_pfilter_iff:
  assumes G:"\<G> \<subseteq> Pow X" and ne:"\<G> \<noteq> {}" and e:"{} \<notin> \<G>"
  shows "(\<exists>F. pow.pfilter F \<and> \<G> = grill X F) \<longleftrightarrow>
    up_closed subset_order (Pow X) \<G> \<and> (\<forall>A\<in>Pow X. \<forall>B\<in>Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>)"
proof
  assume "\<exists>F. pow.pfilter F \<and> \<G> = grill X F"
  then obtain F where F:"pow.pfilter F" "\<G> = grill X F" by blast
  show "up_closed subset_order (Pow X) \<G> \<and> (\<forall>A\<in>Pow X. \<forall>B\<in>Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>)"
    unfolding F(2) using grill_up_closed grill_pfilter_Un[OF F(1)] by blast
next
  assume h:"up_closed subset_order (Pow X) \<G> \<and> (\<forall>A\<in>Pow X. \<forall>B\<in>Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>)"
  let ?F = "grill X \<G>"
  have GF:"\<G> = grill X ?F" using double_grill[OF G] h by simp
  have "pow.pfilter ?F"
    unfolding pow.pfilter_def
  proof (intro conjI set_filterI)
    show "?F \<subseteq> Pow X" by (rule grill_base)
    show "{} \<notin> ?F" using ne by (auto simp:grill_iff)
    show "?F \<noteq> {}" using e grill_reform[OF G _ subset_refl] h by auto
    have up:"up_closed subset_order (Pow X) \<G>" using h by simp
    show "A \<inter> B \<in> ?F" if A:"A \<in> ?F" and B:"B \<in> ?F" for A B
    proof -
      have AX:"A \<subseteq> X" and BX:"B \<subseteq> X" using A B by (auto simp:grill_iff)
      have ABX:"A \<inter> B \<subseteq> X" using AX by blast
      have "X - A \<notin> \<G>" "X - B \<notin> \<G>" using grill_reform[OF G up AX] grill_reform[OF G up BX] A B by simp_all
      then have "(X - A) \<union> (X - B) \<notin> \<G>" using h by auto
      then have "X - (A \<inter> B) \<notin> \<G>" by (simp add:Diff_Int)
      then show ?thesis using grill_reform[OF G up ABX] by simp
    qed
    show "B \<in> ?F" if "A \<in> ?F" "B \<subseteq> X" "A \<subseteq> B" for A B
      using up_closedD[OF grill_up_closed that(1)] that(2,3) by simp
  qed
  with GF show "\<exists>F. pow.pfilter F \<and> \<G> = grill X F" by blast
qed


theorem ultrafilter_mesh:
  assumes U:"ultrafilter U" and F:"pow.pfilter F" and mesh:"F # U"
  shows "F \<subseteq> U"
proof
  fix A assume A:"A \<in> F"
  have AX:"A \<subseteq> X" using A F set_filter_base by (auto simp:pow.pfilter_def)
  show "A \<in> U"
  proof (rule ccontr)
    assume "A \<notin> U"
    then have "X - A \<in> U" using ultrafilter_compl[OF U AX] by simp
    then have "A \<inter> (X - A) \<noteq> {}" using mesh A by (auto simp:mesh_def)
    then show False by blast
  qed
qed

lemma ultrafilter_grill:"ultrafilter U \<Longrightarrow> grill X U = U"
proof (intro set_eqI)
  fix B assume U:"ultrafilter U"
  have pU:"pow.pfilter U" by (rule ultrafilter_pfilter[OF U])
  show "B \<in> grill X U \<longleftrightarrow> B \<in> U"
  proof (cases "B \<subseteq> X")
    case True
    then show ?thesis using grill_pfilter_iff[OF pU True] ultrafilter_compl[OF U True] set_pfilter_compl[OF pU] by blast
  next
    case False
    have "B \<notin> U" using False set_filter_base pU by (auto simp:pow.pfilter_def)
    moreover have "B \<notin> grill X U" using False grill_base by blast
    ultimately show ?thesis by simp
  qed
qed

end


context poset
begin

lemma wf_iff_minimal:
  "wf_on X (strict_part R X) \<longleftrightarrow> (\<forall>A. A \<subseteq> X \<longrightarrow> A \<noteq> {} \<longrightarrow> (\<exists>m. is_minimal R A m))"
proof -
  have "(\<exists>z\<in>A. \<forall>y. (y, z) \<in> strict_part R X \<longrightarrow> y \<notin> A) \<longleftrightarrow> (\<exists>m. is_minimal R A m)" if A:"A \<subseteq> X" for A
  proof
    assume "\<exists>z\<in>A. \<forall>y. (y, z) \<in> strict_part R X \<longrightarrow> y \<notin> A"
    then obtain z where z:"z \<in> A" "\<And>y. (y, z) \<in> strict_part R X \<Longrightarrow> y \<notin> A" by blast
    have "is_minimal R A z"
      unfolding is_maximal_def
    proof (intro conjI ballI impI z(1))
      fix a assume a:"a \<in> A" and az:"(z, a) \<in> dual R"
      show "a = z"
      proof (rule ccontr)
        assume "a \<noteq> z"
        then have "(a, z) \<in> strict_part R X" using a z(1) A az by auto
        then have "a \<notin> A" by (rule z(2))
        then show False using a by simp
      qed
    qed
    then show "\<exists>m. is_minimal R A m" ..
  next
    assume "\<exists>m. is_minimal R A m"
    then obtain m where m:"m \<in> A" "\<And>a. \<lbrakk>a \<in> A; a \<le>' m\<rbrakk> \<Longrightarrow> a = m" by (auto simp:is_maximal_def)
    have "y \<notin> A" if "(y, m) \<in> strict_part R X" for y using that m(2)[of y] by auto
    then show "\<exists>z\<in>A. \<forall>y. (y, z) \<in> strict_part R X \<longrightarrow> y \<notin> A" using m(1) by blast
  qed
  then show ?thesis unfolding wf_on_iff_ex_minimal by blast
qed

lemma wf_induct:
  assumes wf:"wf_on X (strict_part R X)" and x:"x \<in> X"
    and step:"\<And>x. \<lbrakk>x \<in> X; \<And>y. \<lbrakk>y \<in> X; y <' x\<rbrakk> \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof (rule wf_on_induct[OF wf x])
  fix x assume xX:"x \<in> X" and ih:"\<And>y. \<lbrakk>y \<in> X; (y, x) \<in> strict_part R X\<rbrakk> \<Longrightarrow> P y"
  show "P x" by (rule step[OF xX]) (use ih xX in simp)
qed

lemma poset_sub:assumes Y:"Y \<subseteq> X" shows "poset R Y"
proof unfold_locales
  show "(x, x) \<in> R" if "x \<in> Y" for x using that Y by auto
  show "(x, z) \<in> R" if "(x, y) \<in> R" "(y, z) \<in> R" "x \<in> Y" "y \<in> Y" "z \<in> Y" for x y z
    using that Y trans[of x y z] by blast
  show "x = y" if "(x, y) \<in> R" "(y, x) \<in> R" "x \<in> Y" "y \<in> Y" for x y using that Y antisym[of x y] by blast
qed

end

locale total_order = poset +
  assumes total:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<le>' y \<or> y \<le>' x"
begin

lemma not_le_iff:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> \<not> x \<le>' y \<longleftrightarrow> y <' x"
  using total[of x y] by (auto intro:antisym)

lemma total_sub:assumes "Y \<subseteq> X" shows "total_order R Y"
  by (rule total_order.intro[OF poset_sub[OF assms]]) (unfold_locales, use assms total in blast)

lemma strictly_isotone_embedding:
  assumes S:"poset S Y" and fm:"f ` X \<subseteq> Y" and si:"strictly_isotone R X S f"
  shows "order_embedding R X S f"
proof-
  interpret cod:poset S Y
    by (rule S)
  show ?thesis
    unfolding order_embedding_def
  proof(intro ballI)
    fix x y assume x:"x \<in> X" and y:"y \<in> X"
    show "(x, y) \<in> R \<longleftrightarrow> (f x, f y) \<in> S"
    proof
      assume "(x, y) \<in> R"
      then show "(f x, f y) \<in> S"
        using si x y fm by (cases "x = y") (auto simp:strictly_isotone_def)
    next
      assume A0:"(f x, f y) \<in> S"
      show "(x, y) \<in> R"
      proof(rule ccontr)
        assume "(x, y) \<notin> R"
        then have "(y, x) \<in> R" and "x \<noteq> y"
          using total[OF x y] x by auto
        then have B0:"(f y, f x) \<in> S" and B1:"f y \<noteq> f x"
          using si x y by (auto simp:strictly_isotone_def)
        have "f x \<in> Y" and "f y \<in> Y"
          using fm x y by auto
        then have "f x = f y"
          using cod.antisym[OF A0 B0] by simp
        then show False
          using B1 by simp
      qed
    qed
  qed
qed

lemma strictly_isotone_inj:
  assumes S:"poset S Y" and fm:"f ` X \<subseteq> Y" and si:"strictly_isotone R X S f"
  shows "inj_on f X"
  using order_embedding_inj[OF strictly_isotone_embedding[OF S fm si]] poset.refl[OF S] fm by blast

lemma strictly_isotone_total:
  assumes S:"poset S Y" and fm:"f ` X = Y" and si:"strictly_isotone R X S f"
  shows "total_order S Y"
proof(rule total_order.intro[OF S], unfold_locales)
  fix u v assume "u \<in> Y" and "v \<in> Y"
  then obtain x y where x:"x \<in> X" and y:"y \<in> X" and u:"u = f x" and v:"v = f y"
    using fm by blast
  have emb:"order_embedding R X S f"
    using strictly_isotone_embedding[OF S _ si] fm by blast
  then show "(u, v) \<in> S \<or> (v, u) \<in> S"
    using total[OF x y] x y u v by (auto simp:order_embedding_def)
qed

end

locale woset = poset +
  assumes least_ex:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m. is_least R A m"
begin

sublocale total_order
proof
  fix x y assume "x \<in> X" "y \<in> X"
  then obtain m where "is_least R {x, y} m" using least_ex[of "{x, y}"] by blast
  then show "x \<le>' y \<or> y \<le>' x" by (auto simp:is_greatest_def)
qed

definition least::"'a set \<Rightarrow> 'a"
  where "least A = (THE m. is_least R A m)"

lemma least_eq:"\<lbrakk>A \<subseteq> X; is_least R A m\<rbrakk> \<Longrightarrow> least A = m"
  unfolding least_def by (rule the_equality) (auto intro:is_least_unique)

lemma is_least_least:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_least R A (least A)"
  using least_ex least_eq by blast

lemma least_mem:"\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> least A \<in> A"
  and least_le:"\<lbrakk>A \<subseteq> X; A \<noteq> {}; a \<in> A\<rbrakk> \<Longrightarrow> least A \<le>' a"
  using is_least_least by (auto simp:is_greatest_def)

lemma woset_sub:assumes "Y \<subseteq> X" shows "woset R Y"
  by (rule woset.intro[OF poset_sub[OF assms]]) (unfold_locales, use assms least_ex in blast)

lemma wf:"wf_on X (strict_part R X)"
  unfolding wf_iff_minimal using least_ex is_least_minimal by blast

lemma woset_induct:
  assumes "x \<in> X" and "\<And>x. \<lbrakk>x \<in> X; \<And>y. \<lbrakk>y \<in> X; y <' x\<rbrakk> \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
  by (rule wf_induct[OF wf assms])


definition seg::"'a \<Rightarrow> 'a set"
  where "seg x = {y \<in> X. y <' x}"

abbreviation segs::"'a set set" where "segs \<equiv> seg ` X"

lemma seg_iff[simp]:"y \<in> seg x \<longleftrightarrow> y \<in> X \<and> y <' x"
  by (simp add:seg_def)

lemma seg_sub:"seg x \<subseteq> X"
  and seg_notin:"x \<notin> seg x"
  and seg_proper:"x \<in> X \<Longrightarrow> seg x \<noteq> X"
  by auto

lemma seg_down_closed:assumes x:"x \<in> X" shows "down_closed R X (seg x)"
  unfolding up_closed_def
proof (intro ballI impI)
  fix a b assume a:"a \<in> seg x" and b:"b \<in> X" and ba:"(a, b) \<in> dual R"
  have "b <' x" using le_lt_trans[of b a x] a b ba x by auto
  then show "b \<in> seg x" using b by simp
qed


lemma seg_mono_iff:assumes x:"x \<in> X" and y:"y \<in> X" shows "x \<le>' y \<longleftrightarrow> seg x \<subseteq> seg y"
proof
  assume xy:"x \<le>' y"
  show "seg x \<subseteq> seg y"
  proof
    fix z assume "z \<in> seg x"
    then have z:"z \<in> X" "z <' x" by auto
    then have "z <' y" using lt_le_trans[of z x y] xy x y by auto
    then show "z \<in> seg y" using z(1) by simp
  qed
next
  assume s:"seg x \<subseteq> seg y"
  show "x \<le>' y"
  proof (rule ccontr)
    assume "\<not> x \<le>' y"
    then have "y <' x" using not_le_iff[OF x y] by simp
    then have "y \<in> seg x" using y by simp
    then have "y <' y" using s by auto
    then show False by simp
  qed
qed

lemma seg_inj:"\<lbrakk>x \<in> X; y \<in> X; seg x = seg y\<rbrakk> \<Longrightarrow> x = y"
  using seg_mono_iff by (blast intro:antisym)

lemma seg_lt_iff:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x <' y \<longleftrightarrow> seg x \<subset> seg y"
  using seg_mono_iff seg_inj by blast

lemma seg_seg:assumes xy:"x \<in> X" "y \<in> X" "y <' x" shows "woset.seg R (seg x) y = seg y"
proof -
  have "woset.seg R (seg x) y = {z \<in> seg x. z <' y}" by (rule woset.seg_def[OF woset_sub[OF seg_sub]])
  also have "\<dots> = seg y"
  proof (intro set_eqI iffI)
    fix z assume "z \<in> {z \<in> seg x. z <' y}"
    then show "z \<in> seg y" by simp
  next
    fix z assume "z \<in> seg y"
    then have z:"z \<in> X" "z <' y" by simp_all
    then have "z <' x" using lt_trans[of z y x] xy by auto
    then show "z \<in> {z \<in> seg x. z <' y}" using z by simp
  qed
  finally show ?thesis .
qed


lemma down_closed_seg:
  assumes D:"D \<subseteq> X" and ne:"D \<noteq> X" and dc:"down_closed R X D"
  shows "D = seg (least (X - D))"
proof -
  let ?m = "least (X - D)"
  have XD:"X - D \<subseteq> X" "X - D \<noteq> {}" using D ne by blast+
  have m:"?m \<in> X - D" "\<And>a. a \<in> X - D \<Longrightarrow> ?m \<le>' a" using least_mem[OF XD] least_le[OF XD] by auto
  show ?thesis
  proof (intro subset_antisym subsetI)
    fix d assume d:"d \<in> D"
    have dX:"d \<in> X" using d D by blast
    have mX:"?m \<in> X" using m(1) by blast
    have "d <' ?m"
    proof (rule ccontr)
      assume "\<not> d <' ?m"
      then have "?m \<le>' d" using not_le_iff[OF mX dX] by auto
      then have "?m \<in> D" using up_closedD[OF dc d mX] by simp
      with m(1) show False by blast
    qed
    with dX show "d \<in> seg ?m" by simp
  next
    fix y assume "y \<in> seg ?m"
    then have y:"y \<in> X" "y <' ?m" by auto
    show "y \<in> D"
    proof (rule ccontr)
      assume "y \<notin> D"
      then have "?m \<le>' y" using m(2) y(1) by blast
      with y show False using m(1) by (auto intro:antisym)
    qed
  qed
qed

lemma down_closed_iff_seg:
  assumes D:"D \<subseteq> X" and ne:"D \<noteq> X"
  shows "down_closed R X D \<longleftrightarrow> D \<in> segs"
proof
  show "D \<in> segs" if "down_closed R X D"
    using down_closed_seg[OF D ne that] least_mem[of "X - D"] D ne by blast
  show "down_closed R X D" if "D \<in> segs" using that seg_down_closed by auto
qed


lemma seg_order_iso:"order_iso R X subset_order segs seg"
  by (rule order_isoI) (auto simp:seg_mono_iff)

lemma segs_woset:"woset subset_order segs"
proof unfold_locales
  fix A assume A:"A \<subseteq> segs" "A \<noteq> {}"
  let ?E = "{x \<in> X. seg x \<in> A}"
  have "A = seg ` ?E" using A by auto
  have E:"?E \<subseteq> X" "?E \<noteq> {}" using A by auto
  have "is_least subset_order A (seg (least ?E))"
    unfolding is_greatest_def
  proof (intro conjI ballI)
    show "seg (least ?E) \<in> A" using least_mem[OF E] by simp
    fix B assume "B \<in> A"
    then obtain x where x:"x \<in> ?E" "B = seg x" using A by auto
    have "least ?E \<le>' x" using least_le[OF E x(1)] .
    then show "(B, seg (least ?E)) \<in> dual subset_order" unfolding x(2) using least_mem[OF E] x(1) by (simp add:seg_mono_iff)
  qed
  then show "\<exists>m. is_least subset_order A m" ..
qed (auto intro:trans antisym)

end


lemma unique_least_woset:
  assumes R:"R \<subseteq> X \<times> X"
    and ex:"\<And>A. \<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m\<in>A. \<forall>x\<in>A. (m, x) \<in> R"
    and uniq:"\<And>A m n. \<lbrakk>A \<subseteq> X; m \<in> A; n \<in> A; \<forall>x\<in>A. (m, x) \<in> R; \<forall>x\<in>A. (n, x) \<in> R\<rbrakk> \<Longrightarrow> m = n"
  shows "woset R X"
proof -
  have refl:"(x, x) \<in> R" if "x \<in> X" for x using ex[of "{x}"] that by blast
  have antisym:"x = y" if "(x, y) \<in> R" "(y, x) \<in> R" "x \<in> X" "y \<in> X" for x y
    using uniq[of "{x, y}" x y] that refl by simp
  have trans:"(x, z) \<in> R" if xy:"(x, y) \<in> R" and yz:"(y, z) \<in> R" and X:"x \<in> X" "y \<in> X" "z \<in> X" for x y z
  proof -
    obtain m where m:"m \<in> {x, y, z}" "\<forall>a\<in>{x, y, z}. (m, a) \<in> R" using ex[of "{x, y, z}"] X by blast
    consider "m = x" | "m = y" | "m = z" using m(1) by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using m(2) by simp
    next
      case 2
      then have "(y, x) \<in> R" using m(2) by simp
      then have "x = y" using antisym xy X by blast
      then show ?thesis using yz by simp
    next
      case 3
      then have "(z, y) \<in> R" using m(2) by simp
      then have "y = z" using antisym yz X by blast
      then show ?thesis using xy by simp
    qed
  qed
  show ?thesis
  proof unfold_locales
    fix A assume "A \<subseteq> X" "A \<noteq> {}"
    then obtain m where "m \<in> A" "\<forall>x\<in>A. (m, x) \<in> R" using ex by blast
    then show "\<exists>m. is_least R A m" by (auto simp:is_greatest_def)
  qed (auto intro:refl antisym trans)
qed

lemma unique_least_woset':
  assumes R:"R \<subseteq> X \<times> X" and ul:"\<And>A. \<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>!m. m \<in> A \<and> (\<forall>x\<in>A. (m, x) \<in> R)"
  shows "woset R X"
proof (rule unique_least_woset[OF R])
  fix A assume A:"A \<subseteq> X" "A \<noteq> {}"
  show "\<exists>m\<in>A. \<forall>x\<in>A. (m, x) \<in> R" using ul[OF A] by (auto simp:Ex1_def)
next
  fix A m n assume A:"A \<subseteq> X" and m:"m \<in> A" "\<forall>x\<in>A. (m, x) \<in> R" and n:"n \<in> A" "\<forall>x\<in>A. (n, x) \<in> R"
  have "A \<noteq> {}" using m by blast
  then show "m = n" using ul[OF A] m n unfolding Ex1_def by (metis)
qed


lemma (in woset) strict_woset:
  shows "\<And>x y. \<lbrakk>(x, y) \<in> strict_part R X\<rbrakk> \<Longrightarrow> (y, x) \<notin> strict_part R X"
    and "\<And>A. \<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m\<in>A. \<forall>x\<in>A. x \<noteq> m \<longrightarrow> (m, x) \<in> strict_part R X"
proof -
  show "(y, x) \<notin> strict_part R X" if "(x, y) \<in> strict_part R X" for x y using that by (auto intro:antisym)
  fix A assume A:"A \<subseteq> X" "A \<noteq> {}"
  show "\<exists>m\<in>A. \<forall>x\<in>A. x \<noteq> m \<longrightarrow> (m, x) \<in> strict_part R X"
    using least_mem[OF A] least_le[OF A] A by (intro bexI[where x = "least A"]) (auto simp:subset_iff)
qed

lemma strict_woset_reflcl:
  assumes S:"S \<subseteq> X \<times> X" and asym:"\<And>x y. (x, y) \<in> S \<Longrightarrow> (y, x) \<notin> S"
    and least:"\<And>A. \<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m\<in>A. \<forall>x\<in>A. x \<noteq> m \<longrightarrow> (m, x) \<in> S"
  shows "woset (reflcl_on S X) X"
proof (rule unique_least_woset')
  show "reflcl_on S X \<subseteq> X \<times> X" by auto
  fix A assume A:"A \<subseteq> X" "A \<noteq> {}"
  obtain m where m:"m \<in> A" "\<And>x. \<lbrakk>x \<in> A; x \<noteq> m\<rbrakk> \<Longrightarrow> (m, x) \<in> S" using least[OF A] by blast
  show "\<exists>!m. m \<in> A \<and> (\<forall>x\<in>A. (m, x) \<in> reflcl_on S X)"
  proof (intro ex1I[of _ m] conjI ballI)
    show "m \<in> A" by fact
    show "(m, x) \<in> reflcl_on S X" if "x \<in> A" for x using m(2)[OF that] that m(1) A by auto
    fix n assume n:"n \<in> A \<and> (\<forall>x\<in>A. (n, x) \<in> reflcl_on S X)"
    show "n = m"
    proof (rule ccontr)
      assume "n \<noteq> m"
      then have "(m, n) \<in> S" "(n, m) \<in> S" using m n by (auto simp:reflcl_on_def)
      then show False using asym by blast
    qed
  qed
qed


context woset
begin


lemma strictly_isotone_extensive:
  assumes f:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> X" and iso:"strictly_isotone R X R f" and x:"x \<in> X"
  shows "x \<le>' f x"
proof (rule ccontr)
  assume "\<not> x \<le>' f x"
  let ?B = "{x \<in> X. \<not> x \<le>' f x}"
  have B:"?B \<subseteq> X" "?B \<noteq> {}" using x \<open>\<not> x \<le>' f x\<close> by auto
  let ?m = "least ?B"
  have m:"?m \<in> X" "\<not> ?m \<le>' f ?m" using least_mem[OF B] by auto
  have fm:"f ?m <' ?m" using not_le_iff[OF m(1) f[OF m(1)]] m(2) by simp
  then have "f (f ?m) <' f ?m" using iso m(1) f[OF m(1)] by (auto simp:strictly_isotone_def)
  then have "f ?m \<in> ?B" using f[OF m(1)] f[OF f[OF m(1)]] by (auto intro:antisym)
  then have "?m \<le>' f ?m" using least_le[OF B] by blast
  with fm show False using m(1) f[OF m(1)] by (auto intro:antisym)
qed


theorem no_iso_onto_seg:
  assumes x:"x \<in> X"
  shows "\<not> (\<exists>f. order_iso R X R (seg x) f)"
proof
  assume "\<exists>f. order_iso R X R (seg x) f"
  then obtain f where f:"order_iso R X R (seg x) f" by blast
  have maps:"f y \<in> seg x" if "y \<in> X" for y using order_iso_maps[OF f that] .
  have inj:"inj_on f X" by (rule order_embedding_inj[OF f[unfolded order_iso_def, THEN conjunct2]]) (auto dest:maps)
  have si:"strictly_isotone R X R f" by (rule order_iso_strictly_isotone[OF f inj])
  have "x \<le>' f x" using strictly_isotone_extensive[OF _ si x] maps by auto
  moreover have "f x <' x" using maps[OF x] by simp
  ultimately show False using x maps[OF x] by (auto intro:antisym)
qed



theorem segs_not_iso:
  assumes a:"a \<in> X" and b:"b \<in> X" and ne:"a \<noteq> b"
  shows "\<not> (\<exists>f. order_iso R (seg a) R (seg b) f)"
proof -
  have one:"\<not> (\<exists>f. order_iso R (seg y) R (seg x) f)" if xy:"x \<in> X" "y \<in> X" "x <' y" for x y
  proof -
    interpret s:woset R "seg y" by (rule woset_sub[OF seg_sub])
    have "x \<in> seg y" using xy by simp
    then have "\<not> (\<exists>f. order_iso R (seg y) R (s.seg x) f)" by (rule s.no_iso_onto_seg)
    then show ?thesis using seg_seg[OF xy(2,1,3)] by simp
  qed
  have two:"\<not> (\<exists>f. order_iso R (seg x) R (seg y) f)" if xy:"x \<in> X" "y \<in> X" "x <' y" for x y
  proof
    assume "\<exists>f. order_iso R (seg x) R (seg y) f"
    then obtain f where f:"order_iso R (seg x) R (seg y) f" by blast
    interpret s:woset R "seg x" by (rule woset_sub[OF seg_sub])
    interpret t:poset R "seg y" by (rule woset.axioms(1)[OF woset_sub[OF seg_sub]])
    have "order_iso R (seg y) R (seg x) (inv_into (seg x) f)" by (rule s.order_iso_poset[OF f t.poset_axioms])
    then show False using one[OF xy] by blast
  qed
  show ?thesis using one[of a b] one[of b a] two[of a b] two[of b a] total[OF a b] ne a b by blast
qed


theorem auto_id:
  assumes f:"order_iso R X R X f" and x:"x \<in> X"
  shows "f x = x"
proof -
  have inj:"inj_on f X" by (rule order_iso_inj[OF f poset_axioms])
  have maps:"\<And>y. y \<in> X \<Longrightarrow> f y \<in> X" using order_iso_maps[OF f] .
  have "x \<le>' f x" by (rule strictly_isotone_extensive[OF maps order_iso_strictly_isotone[OF f inj] x])
  moreover have "f x \<le>' x"
  proof -
    let ?g = "inv_into X f"
    have g:"order_iso R X R X ?g" by (rule order_iso_inv[OF f inj])
    have gmaps:"\<And>y. y \<in> X \<Longrightarrow> ?g y \<in> X" using order_iso_maps[OF g] .
    have ginj:"inj_on ?g X" by (rule order_iso_inj[OF g poset_axioms])
    have "x \<le>' ?g x" by (rule strictly_isotone_extensive[OF gmaps order_iso_strictly_isotone[OF g ginj] x])
    then have "f x \<le>' f (?g x)" using order_iso_embed[OF f x gmaps[OF x]] by simp
    also have "x \<in> f ` X" using x order_iso_image[OF f] by simp
    then have "f (?g x) = x" by (rule f_inv_into_f)
    finally show ?thesis .
  qed
  ultimately show ?thesis using x maps[OF x] by (intro antisym)
qed

end


end
