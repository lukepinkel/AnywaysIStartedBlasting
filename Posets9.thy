theory Posets9
  imports Main
begin

hide_const top bot
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev sup inf Sup Inf trans refl Greatest asym
declare [[show_consts, show_results]]
declare [[show_abbrevs=true]]

abbreviation dual where
  "dual R \<equiv> (converse R)"

definition ubd :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "ubd R X A = {b \<in> X. \<forall>a\<in>A. (a, b) \<in> R}"

definition is_sup :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_sup R X A s \<longleftrightarrow> s \<in> ubd R X A \<and> (\<forall>b \<in> ubd R X A. (s, b) \<in> R)"

abbreviation lbd :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "lbd R X \<equiv> ubd (dual R) X"

abbreviation is_inf :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_inf R X \<equiv> is_sup (dual R) X"

lemma ubd_iff [simp]: "b \<in> ubd R X A \<longleftrightarrow> b \<in> X \<and> (\<forall>a\<in>A. (a, b) \<in> R)"
  by (simp add: ubd_def)

definition Sup :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "Sup R X A = (THE s. is_sup R X A s)"

definition Inf :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "Inf R X = Sup (dual R) X"

definition sup :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "sup R X a b = Sup R X {a, b}"

definition inf :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "inf R X = sup (dual R) X"

lemma is_sup_iff:
  "is_sup R X A s \<longleftrightarrow> s \<in> X \<and> (\<forall>a\<in>A. (a, s) \<in> R) \<and> (\<forall>b\<in>X. (\<forall>a\<in>A. (a, b) \<in> R) \<longrightarrow> (s, b) \<in> R)"
  by (auto simp: is_sup_def)

lemma dual_ops:
  "Sup (dual R) X = Inf R X" 
  "Inf (dual R) X = Sup R X"
  "sup (dual R) X = inf R X" 
  "inf (dual R) X = sup R X"
  by (simp_all add: Inf_def inf_def)



locale poset =
  fixes R :: "'a rel" and X :: "'a set"
  assumes refl[simp, intro]: "x \<in> X \<Longrightarrow> (x, x) \<in> R"
    and   trans[trans]     : "\<lbrakk>(x, y) \<in> R; (y, z) \<in> R; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (x, z) \<in> R"
    and   antisym          : "\<lbrakk>(x, y) \<in> R; (y, x) \<in> R; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x = y"
begin

abbreviation leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<le>''" 50) where "x \<le>' y \<equiv> (x, y) \<in> R"
abbreviation SupIn :: "'a set \<Rightarrow> 'a" where "SupIn \<equiv> Sup R X"
abbreviation InfIn :: "'a set \<Rightarrow> 'a" where "InfIn \<equiv> Inf R X"

lemma is_sup_unique: "\<lbrakk>is_sup R X A s; is_sup R X A t\<rbrakk> \<Longrightarrow> s = t"
  by (auto simp: is_sup_iff intro: antisym)

lemma SupIn_eqI: "is_sup R X A s \<Longrightarrow> SupIn A = s"
  unfolding Sup_def by (blast intro: is_sup_unique)

lemma is_sup_SupIn: "\<exists>s. is_sup R X A s \<Longrightarrow> is_sup R X A (SupIn A)"
  using SupIn_eqI by fastforce

lemma SupIn_props:
  assumes "\<exists>s. is_sup R X A s"
  shows SupIn_base [simp, intro]: "SupIn A \<in> X"
    and SupIn_upper: "a \<in> A \<Longrightarrow> a \<le>' SupIn A"
    and SupIn_least: "\<lbrakk>b \<in> X; \<And>a. a \<in> A \<Longrightarrow> a \<le>' b\<rbrakk> \<Longrightarrow> SupIn A \<le>' b"
  using is_sup_SupIn[OF assms] by (auto simp: is_sup_iff)

end


sublocale poset \<subseteq> dual: poset "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "poset (dual R) X"
    by unfold_locales (auto intro: trans antisym)
qed (simp_all add: dual_ops)

context poset
begin

lemma is_inf_unique: "\<lbrakk>is_inf R X A s; is_inf R X A t\<rbrakk> \<Longrightarrow> s = t"
  and InfIn_eqI: "is_inf R X A s \<Longrightarrow> InfIn A = s"
  and is_inf_InfIn: "\<exists>s. is_inf R X A s \<Longrightarrow> is_inf R X A (InfIn A)"
  and InfIn_base: "\<exists>s. is_inf R X A s \<Longrightarrow> InfIn A \<in> X"
  and InfIn_lower: "\<lbrakk>\<exists>s. is_inf R X A s; a \<in> A\<rbrakk> \<Longrightarrow> InfIn A \<le>' a"
  and InfIn_greatest: "\<lbrakk>\<exists>s. is_inf R X A s; b \<in> X; \<And>a. a \<in> A \<Longrightarrow> b \<le>' a\<rbrakk> \<Longrightarrow> b \<le>' InfIn A"
  by (fact dual.is_sup_unique dual.SupIn_eqI dual.is_sup_SupIn dual.SupIn_base dual.SupIn_upper dual.SupIn_least)+

end


locale lattice_on = poset +
  assumes ex_sup: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X {a, b} s"
    and ex_inf: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X {a, b} s"
begin

abbreviation supin :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<or>''" 65) where "a \<or>' b \<equiv> sup R X a b"
abbreviation infin :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<and>''" 70) where "a \<and>' b \<equiv> inf R X a b"

lemma sup_is_sup: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {a, b} (a \<or>' b)"
  unfolding sup_def by (intro is_sup_SupIn ex_sup)

lemma sup_closed [simp, intro]: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<in> X"
  and sup_ge1 [simp, intro]: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<le>' a \<or>' b"
  and sup_ge2 [simp, intro]: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> b \<le>' a \<or>' b"
  and sup_least: "\<lbrakk>a \<le>' c; b \<le>' c; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<le>' c"
  using sup_is_sup[of a b] by (auto simp: is_sup_iff)

lemma sup_le_iff [simp]: "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<or>' b \<le>' c \<longleftrightarrow> a \<le>' c \<and> b \<le>' c"
  by (blast intro: sup_least trans[OF sup_ge1] trans[OF sup_ge2])

lemma le_supI1: "\<lbrakk>x \<le>' a; x \<in> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> x \<le>' a \<or>' b"
  by (rule trans[OF _ sup_ge1]) simp_all

lemma le_supI2: "\<lbrakk>x \<le>' b; x \<in> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> x \<le>' a \<or>' b"
  by (rule trans[OF _ sup_ge2]) simp_all

end

sublocale lattice_on \<subseteq> dual: lattice_on "dual R" X
  rewrites "dual (dual R) = R" and "\<And>a b. (a, b) \<in> dual R \<longleftrightarrow> (b, a) \<in> R"
    and "Sup (dual R) X = Inf R X" and "Inf (dual R) X = Sup R X"
    and "sup (dual R) X = inf R X" and "inf (dual R) X = sup R X"
proof -
  show "lattice_on (dual R) X"
    by unfold_locales (simp_all add: ex_sup ex_inf)
qed (simp_all add: dual_ops)

context lattice_on
begin


lemma sup_commute: "a \<or>' b = b \<or>' a"
  by (simp add: sup_def insert_commute)

lemma sup_assoc: "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<or>' b) \<or>' c = a \<or>' (b \<or>' c)"
  by (rule antisym) (auto intro: le_supI1 le_supI2)

lemma sup_absorb: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<or>' (a \<and>' b) = a"
  by (rule antisym) simp_all

lemma le_iff_sup:
  assumes "a \<in> X" "b \<in> X"
  shows "a \<le>' b \<longleftrightarrow> a \<or>' b = b"
proof
  show "a \<or>' b = b" if "a \<le>' b" using assms that by (intro antisym) simp_all
  show "a \<le>' b" if "a \<or>' b = b" using sup_ge1[OF assms] that by simp
qed

end

context lattice_on
begin

lemma inf_commute: "a \<and>' b = b \<and>' a"
  and inf_assoc: "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<and>' b) \<and>' c = a \<and>' (b \<and>' c)"
  and inf_absorb: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<and>' (a \<or>' b) = a"
  and le_iff_inf: "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> b \<le>' a \<longleftrightarrow> a \<and>' b = b"
  by (fact dual.sup_commute dual.sup_assoc dual.sup_absorb dual.le_iff_sup)+

end


locale complete_lattice_on = poset +
  assumes ex_SupIn: "A \<subseteq> X \<Longrightarrow> \<exists>s. is_sup R X A s"
begin

lemma ex_InfIn: assumes "A \<subseteq> X" shows "\<exists>s. is_inf R X A s"
proof -
  have "\<exists>s. is_sup R X (lbd R X A) s" by (rule ex_SupIn) auto
  then obtain s where "is_sup R X (lbd R X A) s" ..
  with assms have "is_inf R X A s" by (auto simp: is_sup_iff)
  then show ?thesis
    by auto 
qed

end

sublocale complete_lattice_on \<subseteq> lattice_on
  by unfold_locales (simp_all add: ex_SupIn ex_InfIn)


definition subset_order :: "'a set rel"
  where "subset_order = {(A, B). A \<subseteq> B}"

lemma subset_order_iff[simp]: "(A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  by (simp add: subset_order_def)


locale closure_op = poset +
  fixes cl :: "'a \<Rightarrow> 'a"
  assumes cl_base [simp, intro]: "x \<in> X \<Longrightarrow> cl x \<in> X"
    and cl_extensive: "x \<in> X \<Longrightarrow> x \<le>' cl x"
    and cl_iso: "\<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> cl x \<le>' cl y"
    and cl_idem [simp]: "x \<in> X \<Longrightarrow> cl (cl x) = cl x"
begin

definition closed :: "'a set"
  where "closed = {c \<in> X. cl c = c}"

lemma closed_iff: "c \<in> closed \<longleftrightarrow> c \<in> X \<and> cl c = c"
  by (simp add: closed_def)

lemma closed_base: "closed \<subseteq> X"
  by (auto simp: closed_def)

lemma cl_closed [simp, intro]: "x \<in> X \<Longrightarrow> cl x \<in> closed"
  by (simp add: closed_def)

lemma closed_range: "closed = cl ` X"
proof
  show "closed \<subseteq> cl ` X"
  proof
    fix c assume "c \<in> closed"
    then have c: "c \<in> X" "cl c = c" by (simp_all add: closed_iff)
    then have "c = cl c" by simp
    from this c(1) show "c \<in> cl ` X" by (rule image_eqI)
  qed
  show "cl ` X \<subseteq> closed" by (auto simp: closed_def)
qed

lemma cl_least: "\<lbrakk>x \<le>' c; x \<in> X; c \<in> closed\<rbrakk> \<Longrightarrow> cl x \<le>' c"
proof -
  assume "x \<le>' c" "x \<in> X" "c \<in> closed"
  then have "cl x \<le>' cl c" using closed_base by (intro cl_iso) auto
  with \<open>c \<in> closed\<close> show "cl x \<le>' c" by (simp add: closed_iff)
qed

text \<open>\<open>cl x\<close> is the least closed element above \<open>x\<close> (\<open>clrD2\<close>, \<open>cl_from_clr\<close> in the original).\<close>

lemma cl_is_sup_closed: "x \<in> X \<Longrightarrow> is_sup R closed {x} (cl x)"
  by (auto simp: is_sup_iff intro: cl_extensive cl_least)

end

lemma interior_contractive: "\<lbrakk>closure_op (dual R) X i; x \<in> X\<rbrakk> \<Longrightarrow> (i x, x) \<in> R"
  by (drule closure_op.cl_extensive) simp_all


context poset
begin

lemma Sup_sub_eqI: assumes "C \<subseteq> X" and s: "is_sup R C A s" shows "Sup R C A = s"
proof -
  have uniq: "t = s" if t: "is_sup R C A t" for t
  proof (rule antisym)
    show "t \<le>' s" and "s \<le>' t" using t s by (auto simp: is_sup_iff)
    show "t \<in> X" and "s \<in> X" using t s \<open>C \<subseteq> X\<close> by (auto simp: is_sup_iff)
  qed
  show ?thesis unfolding Sup_def by (rule the_equality) (rule s, rule uniq)
qed

end

lemma (in poset) Inf_sub_eqI: "\<lbrakk>C \<subseteq> X; is_inf R C A s\<rbrakk> \<Longrightarrow> Inf R C A = s"
  unfolding Inf_def by (rule dual.Sup_sub_eqI)

locale closure_range = poset +
  fixes C :: "'a set"
  assumes C_base: "C \<subseteq> X"
    and ex_cl: "x \<in> X \<Longrightarrow> \<exists>c. is_sup R C {x} c"
begin

definition cl :: "'a \<Rightarrow> 'a"
  where "cl x = Sup R C {x}"

lemma cl_is_sup: assumes "x \<in> X" shows "is_sup R C {x} (cl x)"
proof -
  obtain s where s: "is_sup R C {x} s" using ex_cl[OF assms] ..
  then show ?thesis unfolding cl_def by (simp add: Sup_sub_eqI[OF C_base s])
qed

lemma cl_closed [simp, intro]: "x \<in> X \<Longrightarrow> cl x \<in> C"
  and cl_extensive: "x \<in> X \<Longrightarrow> x \<le>' cl x"
  and cl_least: "\<lbrakk>x \<le>' c; x \<in> X; c \<in> C\<rbrakk> \<Longrightarrow> cl x \<le>' c"
  using cl_is_sup[of x] by (auto simp: is_sup_iff)

lemma cl_base [simp, intro]: "x \<in> X \<Longrightarrow> cl x \<in> X"
  using cl_closed C_base by blast

lemma cl_fixed [simp]: assumes c: "c \<in> C" shows "cl c = c"
proof -
  have cX: "c \<in> X" using c C_base by blast
  show ?thesis by (rule antisym) (auto intro: cl_least[OF refl] cl_extensive simp: c cX)
qed

lemma cl_iso: "\<lbrakk>x \<le>' y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> cl x \<le>' cl y"
  by (rule cl_least) (auto intro: trans[OF _ cl_extensive])

lemma cl_idem [simp]: "x \<in> X \<Longrightarrow> cl (cl x) = cl x"
  by (intro cl_fixed cl_closed)

sublocale op: closure_op R X cl
  by unfold_locales (auto intro: cl_extensive cl_iso)

lemma closed_eq [simp]: "op.closed = C"
proof
  show "op.closed \<subseteq> C"
  proof
    fix c assume "c \<in> op.closed"
    then have "c \<in> X" "cl c = c" by (simp_all add: op.closed_iff)
    then show "c \<in> C" using cl_closed[of c] by simp
  qed
  show "C \<subseteq> op.closed" using C_base by (auto simp: op.closed_iff)
qed

end
context closure_op
begin

lemma range_closure_range: "closure_range R X closed"
  by unfold_locales (auto simp: closed_iff intro: cl_is_sup_closed)

lemma range_cl_eq: assumes "x \<in> X" shows "closure_range.cl R closed x = cl x"
proof -
  interpret cr: closure_range R X closed by (rule range_closure_range)
  show ?thesis
    unfolding cr.cl_def by (rule Sup_sub_eqI[OF closed_base cl_is_sup_closed[OF assms]])
qed

end


locale complete_closure_range = closure_range + complete_lattice_on
begin

lemma InfIn_closed: assumes A: "A \<subseteq> C" shows "InfIn A \<in> C"
proof -
  have AX: "A \<subseteq> X" using A C_base by blast
  note ex = ex_InfIn[OF AX]
  have g: "InfIn A \<in> X" by (rule InfIn_base[OF ex])
  have "cl (InfIn A) \<le>' InfIn A"
  proof (rule InfIn_greatest[OF ex])
    show "cl (InfIn A) \<in> X" using g by simp
    fix a assume a: "a \<in> A"
    have "InfIn A \<le>' a" by (rule InfIn_lower[OF ex a])
    then show "cl (InfIn A) \<le>' a" using g a A by (intro cl_least) auto
  qed
  then have "cl (InfIn A) = InfIn A" using g by (intro antisym) (auto intro: cl_extensive)
  then show ?thesis using cl_closed[OF g] by simp
qed

lemma is_sup_closed_cl: assumes A: "A \<subseteq> C" shows "is_sup R C A (cl (SupIn A))"
proof -
  have AX: "A \<subseteq> X" using A C_base by blast
  note ex = ex_SupIn[OF AX]
  have L1: "SupIn A \<in> X" by (rule SupIn_base[OF ex])
  have L2: "a \<le>' SupIn A" if "a \<in> A" for a by (rule SupIn_upper[OF ex that])
  have L3: "SupIn A \<le>' b" if "b \<in> X" "\<And>a. a \<in> A \<Longrightarrow> a \<le>' b" for b by (rule SupIn_least[OF ex that])
  have 1: "cl (SupIn A) \<in> C" using L1 by simp
  have 2: "a \<le>' cl (SupIn A)" if a: "a \<in> A" for a
    by (rule trans[OF L2[OF a] cl_extensive]) (simp_all add: L1 subsetD[OF AX a])
  have 3: "cl (SupIn A) \<le>' b" if b: "b \<in> C" and ub: "\<And>a. a \<in> A \<Longrightarrow> a \<le>' b" for b
  proof -
    have bX: "b \<in> X" using b C_base by blast
    have "SupIn A \<le>' b" by (rule L3[OF bX ub])
    then have "cl (SupIn A) \<le>' cl b" by (rule cl_iso) (simp_all add: L1 bX)
    then show ?thesis using b by simp
  qed
  show ?thesis unfolding is_sup_iff using 1 2 3 by blast
qed

lemma is_inf_closed: assumes A: "A \<subseteq> C" shows "is_inf R C A (InfIn A)"
proof -
  have AX: "A \<subseteq> X" using A C_base by blast
  note ex = ex_InfIn[OF AX]
  show ?thesis
    unfolding is_sup_iff
    using InfIn_closed[OF A] InfIn_lower[OF ex] InfIn_greatest[OF ex] C_base by auto
qed


lemma closed_complete: "complete_lattice_on R C"
proof (rule complete_lattice_on.intro)
  show "poset R C" by unfold_locales (auto intro: trans antisym dest: subsetD[OF C_base])
  show "complete_lattice_on_axioms R C"
    by (rule complete_lattice_on_axioms.intro) (blast intro: is_sup_closed_cl)
qed

lemma closed_Sup_eq: "A \<subseteq> C \<Longrightarrow> Sup R C A = cl (SupIn A)"
  by (rule Sup_sub_eqI[OF C_base is_sup_closed_cl])

lemma closed_Inf_eq: "A \<subseteq> C \<Longrightarrow> Inf R C A = InfIn A"
  by (rule Inf_sub_eqI[OF C_base is_inf_closed])

end

locale inf_closed = complete_lattice_on +
  fixes C :: "'a set"
  assumes C_base: "C \<subseteq> X"
    and InfIn_closed: "A \<subseteq> C \<Longrightarrow> InfIn A \<in> C"
begin

lemma is_sup_above: assumes x: "x \<in> X" shows "is_sup R C {x} (InfIn {c \<in> C. x \<le>' c})"
proof -
  let ?U = "{c \<in> C. x \<le>' c}"
  have U: "?U \<subseteq> C" by blast
  have UX: "?U \<subseteq> X" using C_base by blast
  note ex = ex_InfIn[OF UX]
  have 1: "InfIn ?U \<in> C" by (rule InfIn_closed[OF U])
  have 2: "x \<le>' InfIn ?U" by (rule InfIn_greatest[OF ex x]) simp
  have 3: "InfIn ?U \<le>' c" if "c \<in> C" "x \<le>' c" for c by (rule InfIn_lower[OF ex]) (simp add: that)
  show ?thesis unfolding is_sup_iff using 1 2 3 by blast
qed

sublocale cr: complete_closure_range R X C
proof (rule complete_closure_range.intro)
  show "closure_range R X C"
  proof (rule closure_range.intro[OF poset_axioms], rule closure_range_axioms.intro)
    show "C \<subseteq> X" by (rule C_base)
    show "\<exists>c. is_sup R C {x} c" if "x \<in> X" for x using is_sup_above[OF that] ..
  qed
  show "complete_lattice_on R X" by (rule complete_lattice_on_axioms)
qed

lemma cl_eq_InfIn: "x \<in> X \<Longrightarrow> cr.cl x = InfIn {c \<in> C. x \<le>' c}"
  unfolding cr.cl_def by (rule Sup_sub_eqI[OF C_base is_sup_above])

end



lemma pow_poset: "poset subset_order (Pow X)"
  by unfold_locales auto

lemma is_inf_pow: "is_inf subset_order (Pow X) A (X \<inter> \<Inter>A)"
  by (auto simp: is_sup_iff)

lemma is_sup_pow: "A \<subseteq> Pow X \<Longrightarrow> is_sup subset_order (Pow X) A (\<Union>A)"
  by (auto simp: is_sup_iff)

lemma pow_complete: "complete_lattice_on subset_order (Pow X)"
  by (rule complete_lattice_on.intro[OF pow_poset])
     (blast intro: complete_lattice_on_axioms.intro is_sup_pow)

lemma Inf_pow: "Inf subset_order (Pow X) = (\<lambda>A. X \<inter> \<Inter>A)"
proof (rule ext)
  interpret pow: poset subset_order "Pow X" by (rule pow_poset)
  fix A show "Inf subset_order (Pow X) A = X \<inter> \<Inter>A" by (rule pow.InfIn_eqI[OF is_inf_pow])
qed

lemma Sup_pow: "A \<subseteq> Pow X \<Longrightarrow> Sup subset_order (Pow X) A = \<Union>A"
proof -
  interpret pow: poset subset_order "Pow X" by (rule pow_poset)
  assume "A \<subseteq> Pow X" then show ?thesis by (rule pow.SupIn_eqI[OF is_sup_pow])
qed

locale moore_family =
  fixes X :: "'a set" and C :: "'a set set"
  assumes base: "C \<subseteq> Pow X"
    and whole: "X \<in> C"
    and Inter_closed: "\<lbrakk>E \<subseteq> C; E \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>E \<in> C"
begin

definition cl :: "'a set \<Rightarrow> 'a set"
  where "cl A = \<Inter>{c \<in> C. A \<subseteq> c}"

lemma cl_closed [simp, intro]: "A \<subseteq> X \<Longrightarrow> cl A \<in> C"
  unfolding cl_def using whole by (intro Inter_closed) auto

lemma cl_extensive: "A \<subseteq> cl A"
  and cl_least: "\<lbrakk>c \<in> C; A \<subseteq> c\<rbrakk> \<Longrightarrow> cl A \<subseteq> c"
  and cl_iso: "A \<subseteq> B \<Longrightarrow> cl A \<subseteq> cl B"
  by (auto simp: cl_def)

lemma cl_fixed [simp]: "c \<in> C \<Longrightarrow> cl c = c"
  using cl_extensive[of c] cl_least[of c c] by auto

lemma cl_idem: "A \<subseteq> X \<Longrightarrow> cl (cl A) = cl A"
  by simp

lemma is_sup_cl: assumes "E \<subseteq> C" shows "is_sup subset_order C E (cl (\<Union>E))"
proof -
  have "\<Union>E \<subseteq> X" using assms base by blast
  then show ?thesis
    using cl_extensive[of "\<Union>E"] cl_least[of _ "\<Union>E"] by (simp add: is_sup_iff) blast
qed

end

sublocale moore_family \<subseteq> closed: complete_lattice_on subset_order C
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
proof -
  show "complete_lattice_on subset_order C"
    by unfold_locales (auto intro: is_sup_cl)
qed simp

context moore_family
begin

lemma SupIn_closed_eq: "E \<subseteq> C \<Longrightarrow> closed.SupIn E = cl (\<Union>E)"
  by (rule closed.SupIn_eqI) (rule is_sup_cl)

lemma InfIn_closed_eq: "\<lbrakk>E \<subseteq> C; E \<noteq> {}\<rbrakk> \<Longrightarrow> closed.InfIn E = \<Inter>E"
  by (rule closed.InfIn_eqI) (auto simp: is_sup_iff Inter_closed)

end



definition filter_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "filter_on R X F \<longleftrightarrow>
    F \<subseteq> X \<and> F \<noteq> {} \<and> (\<forall>a\<in>F. \<forall>b\<in>F. \<exists>c\<in>F. (c, a) \<in> R \<and> (c, b) \<in> R) \<and> (\<forall>a\<in>F. \<forall>b\<in>X. (a, b) \<in> R \<longrightarrow> b \<in> F)"

abbreviation ideal_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "ideal_on R X \<equiv> filter_on (dual R) X"

context lattice_on
begin

lemma filter_iff:
  "filter_on R X F \<longleftrightarrow>
    F \<subseteq> X \<and> F \<noteq> {} \<and> (\<forall>a\<in>F. \<forall>b\<in>F. a \<and>' b \<in> F) \<and> (\<forall>a\<in>F. \<forall>b\<in>X. a \<le>' b \<longrightarrow> b \<in> F)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then have F: "F \<subseteq> X" "F \<noteq> {}" and up: "\<And>a b. \<lbrakk>a \<in> F; b \<in> X; a \<le>' b\<rbrakk> \<Longrightarrow> b \<in> F"
    and dir: "\<And>a b. \<lbrakk>a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> \<exists>c\<in>F. c \<le>' a \<and> c \<le>' b"
    by (auto simp: filter_on_def)
  have "a \<and>' b \<in> F" if ab: "a \<in> F" "b \<in> F" for a b
  proof -
    obtain c where c: "c \<in> F" "c \<le>' a" "c \<le>' b" using dir ab by blast
    from F ab c have X: "a \<in> X" "b \<in> X" "c \<in> X" by auto
    with c have "c \<le>' a \<and>' b" by simp
    with c(1) X show ?thesis by (blast intro: up)
  qed
  with F up show ?R by blast
next
  assume R: ?R
  then have "\<exists>c\<in>F. c \<le>' a \<and> c \<le>' b" if "a \<in> F" "b \<in> F" for a b
    using that by (intro bexI[of _ "a \<and>' b"]) auto
  with R show ?L unfolding filter_on_def by blast
qed

end

locale lattice_top = lattice_on +
  fixes tp :: 'a
  assumes tp_base: "tp \<in> X" and tp_greatest: "x \<in> X \<Longrightarrow> x \<le>' tp"
begin

abbreviation filters :: "'a set set" where "filters \<equiv> {F. filter_on R X F}"

lemma tp_in_filter: "filter_on R X F \<Longrightarrow> tp \<in> F"
  unfolding filter_on_def using tp_base tp_greatest by blast

sublocale filters: moore_family X filters
proof
  show "filters \<subseteq> Pow X" by (auto simp: filter_on_def)
  have "X \<noteq> {}" using tp_base by blast
  then show "X \<in> filters" by (auto simp: filter_iff)
  show "\<Inter>E \<in> filters" if E: "E \<subseteq> filters" "E \<noteq> {}" for E
  proof -
    have fil: "filter_on R X F" if "F \<in> E" for F using E(1) that by blast
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
  fixes bt :: 'a
  assumes bt_base: "bt \<in> X" and bt_least: "x \<in> X \<Longrightarrow> bt \<le>' x"
begin

definition pfilter :: "'a set \<Rightarrow> bool"
  where "pfilter F \<longleftrightarrow> filter_on R X F \<and> bt \<notin> F"

theorem ultrafilter_lemma:
  assumes "pfilter F"
  obtains U where "pfilter U" "F \<subseteq> U" "\<And>G. \<lbrakk>pfilter G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U"
proof -
  let ?\<A> = "{G. pfilter G \<and> F \<subseteq> G}"
  have "\<exists>U\<in>?\<A>. \<forall>G\<in>?\<A>. U \<subseteq> G \<longrightarrow> G = U"
  proof (rule subset_Zorn_nonempty)
    show "?\<A> \<noteq> {}" using assms by blast
    fix \<C> assume "\<C> \<noteq> {}" and chain: "subset.chain ?\<A> \<C>"
    then obtain G0 where G0: "G0 \<in> \<C>" by blast
    from chain have lin: "\<And>G H. \<lbrakk>G \<in> \<C>; H \<in> \<C>\<rbrakk> \<Longrightarrow> G \<subseteq> H \<or> H \<subseteq> G"
      and fil: "\<And>G. G \<in> \<C> \<Longrightarrow> filter_on R X G"
      and rest: "\<And>G. G \<in> \<C> \<Longrightarrow> bt \<notin> G \<and> F \<subseteq> G"
      by (auto simp: subset_chain_def pfilter_def)
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
    with G0 rest show "\<Union>\<C> \<in> ?\<A>" by (auto simp: pfilter_def)
  qed
  then obtain U where U: "pfilter U" "F \<subseteq> U"
    and max: "\<And>G. \<lbrakk>pfilter G; F \<subseteq> G; U \<subseteq> G\<rbrakk> \<Longrightarrow> G = U" by auto
  show thesis
  proof (rule that[OF U])
    show "G = U" if "pfilter G" "U \<subseteq> G" for G using max[of G] that U(2) by blast
  qed
qed

end


definition lgc_from_rel :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "lgc_from_rel R Y X = {t \<in> Y. \<forall>s\<in>X. (s, t) \<in> R}"

lemma lgc_from_rel_galois: "\<lbrakk>A \<subseteq> X; B \<subseteq> Y\<rbrakk> \<Longrightarrow> B \<subseteq> lgc_from_rel R Y A \<longleftrightarrow> A \<subseteq> lgc_from_rel (dual R) X B"
  and lgc_from_rel_mono_decreasing: "A \<subseteq> A' \<Longrightarrow> lgc_from_rel R Y A' \<subseteq> lgc_from_rel R Y A"
  and lgc_from_rel_extensive: "A \<subseteq> X \<Longrightarrow> A \<subseteq> lgc_from_rel (dual R) X (lgc_from_rel R Y A)"
  and lgc_from_rel_triple: "A \<subseteq> X \<Longrightarrow> lgc_from_rel R Y (lgc_from_rel (dual R) X (lgc_from_rel R Y A)) = lgc_from_rel R Y A"
  by (auto simp: lgc_from_rel_def)

definition meshes :: "'a set rel"
  where "meshes = {(A, B). A \<inter> B \<noteq> {}}"

definition grill :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "grill X \<A> = lgc_from_rel meshes (Pow X) \<A>"

lemma meshes_sym [simp]: "dual meshes = meshes"
  by (auto simp: meshes_def)

lemma grill_antiiso: "\<A> \<subseteq> \<B> \<Longrightarrow> grill X \<B> \<subseteq> grill X \<A>"
  and grill_grill_extensive: "\<A> \<subseteq> Pow X \<Longrightarrow> \<A> \<subseteq> grill X (grill X \<A>)"
  and grill_triple: "\<A> \<subseteq> Pow X \<Longrightarrow> grill X (grill X (grill X \<A>)) = grill X \<A>"
  unfolding grill_def
  using lgc_from_rel_mono_decreasing[of \<A> \<B> meshes "Pow X"] lgc_from_rel_extensive[of \<A> "Pow X" meshes "Pow X"]
    lgc_from_rel_triple[of \<A> "Pow X" meshes "Pow X"]
  by simp_all



sublocale moore_family \<subseteq> cs: inf_closed subset_order "Pow X" C
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "Inf subset_order (Pow X) = (\<lambda>A. X \<inter> \<Inter>A)"
proof -
  show "inf_closed subset_order (Pow X) C"
  proof (rule inf_closed.intro[OF pow_complete], rule inf_closed_axioms.intro)
    show "C \<subseteq> Pow X" by (rule base)
    fix A assume A: "A \<subseteq> C"
    show "Inf subset_order (Pow X) A \<in> C"
    proof (cases "A = {}")
      case True
      then show ?thesis using whole by (simp add: Inf_pow)
    next
      case False
      then obtain a where a: "a \<in> A" by blast
      have "\<Inter>A \<subseteq> X" using a A base by blast
      then have "Inf subset_order (Pow X) A = \<Inter>A" by (simp add: Inf_pow Int_absorb1)
      then show ?thesis using Inter_closed[OF A False] by simp
    qed
  qed
qed (simp_all add: Inf_pow)

context moore_family
begin


lemma cl_eq_general: assumes A: "A \<subseteq> X" shows "cs.cr.cl A = cl A"
proof -
  have "cs.cr.cl A = X \<inter> \<Inter>{c \<in> C. A \<subseteq> c}" using A by (simp add: cs.cl_eq_InfIn)
  also have "\<dots> = \<Inter>{c \<in> C. A \<subseteq> c}" using whole A by (intro Int_absorb1 Inter_lower) simp
  finally show ?thesis by (simp add: cl_def)
qed


lemma "\<lbrakk>c \<in> C; A \<subseteq> c\<rbrakk> \<Longrightarrow> cl A \<subseteq> c"
  and "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> cl A \<subseteq> cl B"
  and "E \<subseteq> C \<Longrightarrow> closed.SupIn E = cl (\<Union>E)"
proof -
  show "\<lbrakk>c \<in> C; A \<subseteq> c\<rbrakk> \<Longrightarrow> cl A \<subseteq> c"
  proof -
    assume c: "c \<in> C" and Ac: "A \<subseteq> c"
    have AX: "A \<subseteq> X" using c Ac base by blast
    have "cs.cr.cl A \<subseteq> c" by (rule cs.cr.cl_least) (simp_all add: Ac AX c)
    then show "cl A \<subseteq> c" by (simp add: cl_eq_general[OF AX])
  qed
  show "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> cl A \<subseteq> cl B"
  proof -
    assume AB: "A \<subseteq> B" and BX: "B \<subseteq> X"
    have AX: "A \<subseteq> X" using AB BX by blast
    have "cs.cr.cl A \<subseteq> cs.cr.cl B" by (rule cs.cr.cl_iso) (simp_all add: AB AX BX)
    then show "cl A \<subseteq> cl B" by (simp add: cl_eq_general[OF AX] cl_eq_general[OF BX])
  qed
  show "E \<subseteq> C \<Longrightarrow> closed.SupIn E = cl (\<Union>E)"
  proof -
    assume E: "E \<subseteq> C"
    have UX: "\<Union>E \<subseteq> X" using E base by blast
    have 1: "closed.SupIn E = cs.cr.cl (Sup subset_order (Pow X) E)" by (rule cs.cr.closed_Sup_eq[OF E])
    have 2: "Sup subset_order (Pow X) E = \<Union>E" using E base by (intro Sup_pow) blast
    show "closed.SupIn E = cl (\<Union>E)" by (simp add: 1 2 cl_eq_general[OF UX])
  qed
qed

end


locale galois_conn = dom: poset R X + cod: poset S Y
  for R :: "'a rel" and X :: "'a set" and S :: "'b rel" and Y :: "'b set" +
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes f_maps [simp, intro]: "x \<in> X \<Longrightarrow> f x \<in> Y"
    and g_maps [simp, intro]: "y \<in> Y \<Longrightarrow> g y \<in> X"
    and cl_cond: "\<lbrakk>x \<in> X; y \<in> Y\<rbrakk> \<Longrightarrow> (x, g y) \<in> R \<longleftrightarrow> (y, f x) \<in> S"
begin

lemma ext_f: "x \<in> X \<Longrightarrow> (x, g (f x)) \<in> R"
  by (simp add: cl_cond)

lemma ext_g: "y \<in> Y \<Longrightarrow> (y, f (g y)) \<in> S"
  using cl_cond[of "g y" y] by simp

lemma anti_f: assumes xx: "(x, x') \<in> R" and x: "x \<in> X" and x': "x' \<in> X" shows "(f x', f x) \<in> S"
proof -
  have "(x, g (f x')) \<in> R" by (rule dom.trans[OF xx ext_f[OF x']]) (simp_all add: x x')
  then show ?thesis using cl_cond[OF x f_maps[OF x']] by simp
qed

lemma anti_g: assumes yy: "(y, y') \<in> S" and y: "y \<in> Y" and y': "y' \<in> Y" shows "(g y', g y) \<in> R"
proof -
  have "(y, f (g y')) \<in> S" by (rule cod.trans[OF yy ext_g[OF y']]) (simp_all add: y y')
  then show ?thesis using cl_cond[OF g_maps[OF y'] y] by simp
qed

lemma idem_f: assumes x: "x \<in> X" shows "f (g (f x)) = f x"
proof (rule cod.antisym)
  show "(f (g (f x)), f x) \<in> S" by (rule anti_f[OF ext_f[OF x] x]) (simp add: x)
  show "(f x, f (g (f x))) \<in> S" by (rule ext_g) (simp add: x)
qed (simp_all add: x)

sublocale closure: closure_op R X "g \<circ> f"
  by unfold_locales (auto simp: ext_f idem_f intro: anti_g anti_f)

end

lemma lgc_from_rel_galois_conn: "galois_conn subset_order (Pow S) subset_order (Pow T) (lgc_from_rel R T) (lgc_from_rel (R\<inverse>) S)"
  by unfold_locales (auto simp: lgc_from_rel_def)

lemma double_lgc_from_rel_closure_op: "closure_op subset_order (Pow S) (lgc_from_rel (R\<inverse>) S \<circ> lgc_from_rel R T)"
proof -
  interpret galois_conn subset_order "Pow S" subset_order "Pow T" "lgc_from_rel R T" "lgc_from_rel (R\<inverse>) S"
    by (rule lgc_from_rel_galois_conn)
  show ?thesis by (rule closure.closure_op_axioms)
qed

lemma double_grill_closure_op: "closure_op subset_order (Pow (Pow X)) (grill X \<circ> grill X)"
  using double_lgc_from_rel_closure_op[where R = meshes and S = "Pow X" and T = "Pow X"]
  by (simp add: grill_def[abs_def])



end