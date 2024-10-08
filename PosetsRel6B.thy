theory PosetsRel6B
  imports Main
begin

declare [[show_consts, show_results, show_types]]
declare [[show_abbrevs=true]]

hide_const map
hide_const partition



no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)
section DisjointSets


definition surj_into::"('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "surj_into f Y \<equiv> (\<forall>y \<in> Y. \<exists>x. f x = y)"

lemma surj_intoI:
  "(\<And>y. y \<in> Y \<Longrightarrow> (\<exists>x. f x = y)) \<Longrightarrow> surj_into f Y"
  by (simp add: surj_into_def)

lemma surj_intoI1:
  "(\<And>y. y \<in> Y \<Longrightarrow> (\<exists>x. y = f x )) \<Longrightarrow> surj_into f Y"
 by(auto simp add:surj_into_def)

lemma surj_fiber_nonempty:
  "surj_into f Y \<Longrightarrow> y \<in> Y \<Longrightarrow> vimage f {y} \<noteq> {}"
  unfolding surj_into_def by auto

lemma surj_intoE1:
  "surj_into f Y \<Longrightarrow> y \<in> Y \<Longrightarrow> (\<exists>x. f x = y)"
  by (simp add: surj_into_def)
  
lemma surj_intoE2:
  "surj_into f Y \<Longrightarrow> y \<in> Y \<Longrightarrow> (\<exists>x. y= f x)"
  using surj_intoE1 by fastforce
 
lemma surj_into_obtains:
  assumes "surj_into f Y" and "y \<in> Y"
  obtains x where "f x = y"
  using assms unfolding surj_into_def by blast

definition is_fun::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_fun f X Y \<equiv> f`X \<subseteq> Y"

section RightInverse

definition is_right_inv::"'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_right_inv Y f s \<equiv> (\<forall>y \<in> Y.  f (s y) = y)"


lemma is_right_invI:
  "(\<And>y. y \<in> Y \<Longrightarrow> f (s y) = y) \<Longrightarrow> is_right_inv Y f s"
  unfolding  is_right_inv_def by blast

lemma is_right_invI1:
  "(\<And>y. y \<in> Y \<Longrightarrow> y = f (s y)) \<Longrightarrow> is_right_inv Y f s"
  by (simp add: is_right_invI)

lemma is_right_invE1:
  "is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> f (s y) = y"
  by (simp add: is_right_inv_def)

lemma is_right_invE2:
  "is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> y = f (s y) "
  by (simp add: is_right_inv_def)

lemma ex_rinv_imp_surj:
  "\<exists>s. is_right_inv Y f s \<Longrightarrow> surj_into f Y"
  unfolding surj_into_def is_right_inv_def by(auto)

lemma is_rinv_imp_surj:
  "is_right_inv Y f s \<Longrightarrow> surj_into f Y"
  using ex_rinv_imp_surj by blast

lemma surj_implies_ex_rinv:
  "surj_into f Y \<Longrightarrow> \<exists>s. is_right_inv Y f s"
proof-
  assume onto:"surj_into f Y"
  have "\<exists>s. \<forall>y \<in> Y. y = f (s y)"
  proof(rule bchoice[of Y "\<lambda>a b. a = f b"])
    show "\<forall>y::'b\<in>Y. \<exists>ya::'a. y = f ya"
    using onto unfolding surj_into_def by fastforce
  qed
  then show "\<exists>s. is_right_inv Y f s" 
  using is_right_invI1[of Y f] by blast
qed


section LeftInverse


definition is_left_inv::"'a set \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_left_inv X f r \<equiv> (\<forall>x \<in> X.  r (f x) = x)"

lemma is_left_invI:
  "(\<And>x. x \<in> X \<Longrightarrow> r (f x) = x) \<Longrightarrow> is_left_inv X f r"
  unfolding  is_left_inv_def by blast

lemma is_left_invI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x = r (f x)) \<Longrightarrow> is_left_inv X f r"
  by (simp add: is_left_invI)

lemma is_left_invE1:
  "is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> r (f x) = x"
  by (simp add: is_left_inv_def)

lemma linv_cancel:
  assumes linv:"is_left_inv X f r" and elem:"x1 \<in> X""x2 \<in> X" and eq_under:"f x1 = f x2"
  shows "x1 = x2"
proof-
  from linv elem(1) have "x1 =r (f x1)"
    by (simp add: is_left_invE1)
  also have "... = r (f x2)"
    by (simp add: eq_under)
  also have "... = x2"
    using linv elem(2) by (simp add: is_left_invE1)
  finally show ?thesis
    by simp
qed
  
lemma ex_linv_implies_inj:
  "\<exists>s. is_left_inv X f r \<Longrightarrow> inj_on f X"
  by (simp add: inj_on_def linv_cancel)

lemma is_linv_implies_inj:
  "is_left_inv X f r \<Longrightarrow> inj_on f X"
  by (simp add: inj_on_def linv_cancel)

lemma inj_implies_ex_linv:
  "inj_on f X \<Longrightarrow> \<exists>r. is_left_inv X f r"
  unfolding is_left_inv_def using inv_into_f_f[of f X] by blast


section LeftRightInverses

lemma left_inv_target:
  "is_left_inv X f r \<Longrightarrow> r`(f`X) = X "
  unfolding is_left_inv_def  by (simp add: image_comp)

lemma right_inv_target:
  "is_right_inv Y f s \<Longrightarrow> f`(s`Y) = Y"
  unfolding is_right_inv_def  by (simp add: image_comp)

lemma rinv_l:
  "is_left_inv X f r \<Longrightarrow> is_right_inv X r f"
  by (simp add: is_left_invE1 is_right_inv_def)

lemma linv_r:
  "is_right_inv (Y::'b set) f s \<Longrightarrow> is_left_inv Y s f"
  by (simp add: is_left_inv_def is_right_invE1)

lemma rinv_surj:
  "is_left_inv X f r \<Longrightarrow> surj_into r X"
  using ex_rinv_imp_surj rinv_l by blast

lemma linv_inj:
  "is_right_inv (Y::'b set) f s \<Longrightarrow> inj_on s Y"
  using is_linv_implies_inj linv_r by blast

lemma rinv_unique:
  assumes a1: "is_right_inv Y f s2" and a2: "s1 ` Y = s2 ` Y" and  a3: "is_right_inv Y f s1"
  shows "\<And>y. y \<in> Y \<Longrightarrow> s1 y = s2 y"
proof-
  fix y assume a4:"y \<in> Y"
  then have "\<exists>t \<in> Y. s1 y = s2 t"
    using a2 by auto
  then obtain t where b0:"t \<in> Y" and b1:"s1 y = s2 t"
    by blast
  have "y = f (s1 y)"
    using a3 a4 is_right_invE2[of Y f s1 y] by blast
  also have "... = f (s2 t)"
    by (simp add: b1)
  also have "... = t"
    using a1 b0 a3 is_right_invE1[of Y f s2 t] by blast
  finally show "s1 y = s2 y"
    using b1 by blast
qed

definition fun_section :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'a"
  where "fun_section f X Y \<equiv> (\<lambda>y. SOME x.  x \<in> X \<and> f x = y)"

lemma section_is_rinv:
  assumes A0:"surj_into f Y" and A1:"image f X = Y"
  shows "is_right_inv Y f (fun_section f X Y)"
proof-
  let ?A="vimage f Y"
  let ?s=" (fun_section f X Y)"
  show ?thesis
  proof(rule is_right_invI1)
    fix y assume A2:"y \<in> Y" 
    show "y = f (?s y)"
    unfolding fun_section_def
    proof(rule someI2_ex)
      show "\<exists>a::'a. a \<in> X \<and> f a = y"
        using A0 A1 A2 unfolding surj_into_def by(auto)
      show "\<And>x::'a. x \<in> X \<and> f x = y \<Longrightarrow> y = f x"
        by simp
    qed
  qed
qed


lemma section_is_into:
  assumes A0:"surj_into f Y" and A1:"image f X = Y" and A2:"y \<in> Y"
  shows "(fun_section f X Y) y \<in> X"
  unfolding fun_section_def
  proof(rule someI2_ex)
    show  "\<exists>a::'a. a \<in> X \<and> f a = y"
      using A1 A2 by blast
    show "\<And>x::'a. x \<in> X \<and> f x = y \<Longrightarrow> x \<in> X"
      by simp
qed



definition is_disjoint::"'a set set \<Rightarrow> bool" where
  "is_disjoint P \<equiv> (\<forall>p \<in> P. \<forall>q \<in> P. p \<inter> q \<noteq> {} \<longrightarrow> p =q)"

lemma is_disjointI1:
  "(\<And>p q. \<lbrakk>p \<in> P; q \<in> P; p \<inter> q \<noteq> {}\<rbrakk> \<Longrightarrow> p=q) \<Longrightarrow> is_disjoint P"
  by (simp add: is_disjoint_def)

lemma is_disjointE1:
  "is_disjoint P \<Longrightarrow> \<lbrakk>p \<in> P; q \<in> P; x \<in>p; x \<in> q\<rbrakk> \<Longrightarrow> p=q"
  unfolding is_disjoint_def by blast

lemma is_disjointE2:
  "\<lbrakk>is_disjoint P; p \<in> P; q \<in> P\<rbrakk> \<Longrightarrow> p=q \<or> p \<inter> q = {} "
  unfolding is_disjoint_def by blast

section Partitions

definition is_part::"'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_part X P \<equiv> is_disjoint P \<and> \<Union>P=X \<and> {} \<notin> P"

lemma is_partI1:
  "\<Union>P=X \<Longrightarrow> is_disjoint P \<Longrightarrow> {} \<notin> P \<Longrightarrow> is_part X P"
  by (simp add: is_part_def)

lemma is_partE1:
  assumes A0:"is_part X P" and A1:"x \<in> X"
  obtains p where "p \<in> P" and "x \<in> p"
  by (metis A0 A1 UnionE is_part_def)

lemma is_partE2:
  "\<lbrakk>is_part X P; p \<in> P\<rbrakk> \<Longrightarrow> p \<subseteq> X"
  unfolding is_part_def by auto

lemma is_part_ex1:
  "\<lbrakk>is_part X P; x \<in>X\<rbrakk> \<Longrightarrow> (\<exists>p \<in> P. x \<in> p)"
  by (meson is_partE1)

lemma is_part_ex2:
  "\<lbrakk>is_part X P; x \<in>X; p \<in> P; x \<in> p; q \<in> P; x \<in> q \<rbrakk> \<Longrightarrow> p=q"
  unfolding is_part_def is_disjoint_def by auto

lemma is_part_unique:
  "\<lbrakk>is_part X P; x \<in>X\<rbrakk> \<Longrightarrow> (\<exists>!p \<in> P. x \<in> p)"
proof(rule ex_ex1I)
  show "is_part X P \<Longrightarrow> x \<in> X \<Longrightarrow> \<exists>p. p \<in> P \<and> x \<in> p"
    using is_part_ex1[of X P x] by auto
  show "\<And>p y. is_part X P \<Longrightarrow> x \<in> X \<Longrightarrow> p \<in> P \<and> x \<in> p \<Longrightarrow> y \<in> P \<and> x \<in> y \<Longrightarrow> p = y"
    using is_part_ex2[of X P x ] by presburger
qed
    

section EquivalenceRelation
subsection EquivalenceClasses
definition is_eqrel::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "is_eqrel X R \<equiv> refl_on X R \<and> sym R \<and> trans R"

lemma converse_fst_snd:
  "fst`R=snd`(converse R)"
  by (simp add: fst_eq_Domain snd_eq_Range)

lemma is_eqrelI1:
  "\<lbrakk>refl_on X R; sym R; trans R\<rbrakk> \<Longrightarrow> is_eqrel X R"
  using is_eqrel_def by blast

lemma is_eqrelI2:
  assumes A0:"fst`R=X" and A1:"R=converse R" and A2:"(relcomp R R) = R"
  shows "is_eqrel X R"
proof-
  from A1 obtain B0:"sym R" 
    using sym_conv_converse_eq[of R] by blast
  from A2 obtain B1:"trans R"
    using relcomp.relcompI transI[of R] by blast
  from A0 B0 A1 obtain "fst`R=snd`R"
    by (simp add: converse_fst_snd)
  then obtain B2a:"R \<subseteq> X \<times> X"
    using A0 subset_fst_snd[of R] by presburger
  also have B2b:"\<And>x. x \<in> X \<Longrightarrow> (x, x)\<in>R"
  proof-
    fix x assume C0:"x \<in> X"
    then obtain y where C1:"(x, y)\<in>R"
      using A0 by force
    then obtain "(y, x)\<in>R"
       using A1 by blast
    then show "(x,x)\<in>R"
      using A2 C1 by blast
  qed
  from B2a B2b have B2:"refl_on X R"
    unfolding refl_on_def  by auto
  from B0 B1 B2 show "is_eqrel X R"
    by (simp add: is_eqrelI1)
qed

lemma is_eqrelE1:
  "is_eqrel X R \<Longrightarrow> refl_on X R"
  by (simp add: is_eqrel_def)
 
lemma is_eqrelE2:
  "is_eqrel X R \<Longrightarrow> sym R"
  by (simp add: is_eqrel_def)

lemma is_eqrelE3:
  "is_eqrel X R \<Longrightarrow> trans R"
  by (simp add: is_eqrel_def)

lemma is_eqrelE12:
  assumes A0:"is_eqrel X R "
  shows "fst`R=X"
proof
  show "fst`R \<subseteq> X"
  proof
    fix x assume "x \<in> fst`R"
    then show "x \<in> X"
      using assms is_eqrelE1 refl_on_domain by fastforce
  qed
  next show "X \<subseteq> fst`R"
  proof
    fix x assume "x \<in> X"
    then obtain "(x,x)\<in>R"
      using A0 is_eqrelE1[of X R] refl_onD[of X R x] by auto
    then show "x \<in> fst`R"
      by (simp add: Domain.DomainI fst_eq_Domain)
  qed
qed

lemma is_eqrelE22:
  "is_eqrel X R \<Longrightarrow> R=converse R"
  by (simp add: is_eqrel_def sym_conv_converse_eq)

lemma is_eqrelE32:
  "is_eqrel X R \<Longrightarrow> (relcomp R R)= R"
proof -
  assume a1: "is_eqrel X R"
  then have "trans R"
    using is_eqrelE3 by blast
  then have f2: "relcomp R R \<subseteq> R"
    by (simp add: trans_O_subset)
  have "R =converse R"
    using a1 by (simp add: is_eqrelE22)
  then show ?thesis
    using f2 by auto
qed

lemma eqrelE4:
  "\<lbrakk>is_eqrel X R; (x, y)\<in>R\<rbrakk> \<Longrightarrow> x \<in> X \<and> y \<in> X"
  unfolding is_eqrel_def using refl_on_domain[of X R x y] by auto

lemma eqrelE4b:
  "is_eqrel X R \<Longrightarrow> R \<subseteq> X \<times> X"
  by (simp add: is_eqrel_def refl_on_def)

lemma eqrel_class1:
  "\<lbrakk>is_eqrel X R; (x, y)\<in>R\<rbrakk> \<Longrightarrow>R``{y} \<subseteq> R``{x}"
  using is_eqrelE32 by fastforce

lemma eqrel_class1b:
  "\<lbrakk>is_eqrel X R; (x, y)\<in>R\<rbrakk> \<Longrightarrow>R``{x} \<subseteq> R``{y}"
  by (meson eqrel_class1 is_eqrelE2 symD)

lemma eqrel_class2:
  "\<lbrakk>is_eqrel X R; (x, y)\<in>R\<rbrakk> \<Longrightarrow>R``{y} = R``{x}"
  by (simp add: eqrel_class1 is_eqrelE2 subset_antisym symD)

lemma eqrel_class3:
  "\<lbrakk>is_eqrel X R; x \<in> X\<rbrakk> \<Longrightarrow> x \<in> R``{x}"
  using is_eqrelE1 refl_onD by fastforce

lemma eqrel_class3b:
  "\<lbrakk>is_eqrel X R; R``{y} \<subseteq> R``{x}; y \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  using eqrel_class3 by fastforce

lemma eqrel_class3c:
  "\<lbrakk>is_eqrel X R; R``{x}=R``{y}; y \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  using eqrel_class3 by fastforce

lemma eqrel_class3d:
  "\<lbrakk>is_eqrel X R; z \<in> R``{x} \<inter> R``{y}\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  unfolding is_eqrel_def trans_def sym_def by(blast)

lemma eqrel_class3e:
  "is_eqrel X R \<Longrightarrow> (x, y)\<in> R \<longleftrightarrow> R``{x}=R``{y} \<and> x \<in> X \<and> y \<in> X"
  by (meson eqrelE4 eqrel_class2 eqrel_class3c)

lemma eqrel_class3f:
  "is_eqrel X R \<Longrightarrow> (x, y)\<notin> R \<longleftrightarrow> R``{x} \<inter> R``{y} = {}"
  using eqrel_class3e by fastforce

lemma eqrel_class3g:
  "\<lbrakk>is_eqrel X R;  R``{x} \<inter> R``{y} \<noteq> {}\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  by (meson eqrel_class3f)

lemma eqrel_class3h:
  "\<lbrakk>is_eqrel X R; z \<in> R``{x} \<inter> R``{y}\<rbrakk> \<Longrightarrow> R``{x}=R``{y}"
  by (simp add: eqrel_class3e)

lemma eqrel_class3i:
  "\<lbrakk>is_eqrel X R; R``{x} \<inter> R``{y} \<noteq> {}\<rbrakk> \<Longrightarrow> R``{x}=R``{y}"
  using eqrel_class3e by fastforce

lemma eqrel_class4:
  "\<lbrakk>is_eqrel X R; x \<in> X;R``{x}=R``{y}\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  by (metis Image_singleton_iff eqrel_class3 is_eqrelE2 symE)

subsection QuotientSet

definition quotient::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set" (infixl "'/" 75) where
  "quotient X R \<equiv> (\<Union>x \<in> X. {R``{x}})"

lemma quotientI1:
  "x \<in> X \<Longrightarrow> R``{x} \<in> quotient X R"
  unfolding quotient_def by auto

lemma quotientE1:
  "t \<in> quotient X R \<Longrightarrow> (\<And>x. t=R``{x} \<Longrightarrow> x \<in> X \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding quotient_def by blast

lemma quotientE1b:
  "t \<in> quotient X R \<Longrightarrow> (\<And>x. t=R``{x} \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding quotient_def by blast

lemma quotientE2:
  "t \<in> quotient X R \<Longrightarrow> \<exists>x \<in> X. t=R``{x}"
  by (meson quotientE1)

lemma quotientE3:
  "t \<in> quotient X R \<Longrightarrow> \<exists>x. t=R``{x}"
  by (meson quotientE1)

lemma quotientE4:
  assumes A0:"t \<in> quotient X R"
  obtains x where "x \<in> X" and "t=R``{x}"
  by (meson assms quotientE1)

lemma quotientE5:
  "t \<in> quotient X R \<Longrightarrow> (\<And>x. \<exists>x. t=R``{x}  \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding quotient_def by blast

lemma quotient_un:
  "is_eqrel X R \<Longrightarrow> \<Union>(quotient X R) = X"
  unfolding is_eqrel_def quotient_def refl_on_def by(auto)


lemma quotient_mem_elem:
  assumes A0:"is_eqrel X R" and 
          A1:"t \<in> quotient X R" and
          A2:"x \<in> t" and
          A3:"y \<in> t"
  shows "(x, y) \<in> R"
proof-
  obtain z where "z \<in> X" and "R``{z} = t"
    using A0 A1 quotientE2 by blast  
  then obtain "(z, x) \<in> R" and rzy:"(z, y) \<in> R" 
    using A2 A3 by blast
  then obtain "(x, z) \<in> R" 
    using A0 is_eqrelE22 by fastforce 
  then show "(x, y) \<in> R"
    using A0  rzy transD[of R x z y] unfolding is_eqrel_def by blast
qed

lemma quotient_disj:
  assumes A0:"is_eqrel X R" and 
          A1:"t \<in> quotient X R" and
          A2:"s \<in> quotient X R"
  shows quotient_disj1:"\<lbrakk>x \<in> t; y \<in> s; (x, y)\<in> R\<rbrakk> \<Longrightarrow> t=s" and
        quotient_disj2:"\<lbrakk>x \<in> t; y \<in> s; t=s\<rbrakk> \<Longrightarrow> (x,y)\<in>R" and
        quotient_disj3:"t \<inter> s \<noteq> {} \<Longrightarrow> t=s"
proof-
  obtain a b where A3:"a \<in> X" and A4:"t=R``{a}" and A5:"b \<in> X" and A6:"s=R``{b}"
    by (meson A1 A2 quotientE1)
  show P0:"\<lbrakk>x \<in> t; y \<in> s; (x, y)\<in> R\<rbrakk> \<Longrightarrow> t=s"
    by (metis A0 A4 A6 Image_singleton_iff eqrel_class2)
   show P1:"\<lbrakk>x \<in> t; y \<in> s; t=s\<rbrakk> \<Longrightarrow> (x,y)\<in>R"
     by (metis A0 Image_singleton_iff \<open>\<And>thesis. (\<And>a b. \<lbrakk>a \<in> X; t = R `` {a}; b \<in> X; s = R `` {b}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> eqrel_class2)
  show P2:"t \<inter> s \<noteq> {} \<Longrightarrow> t=s"
    by (metis A0 A4 A6 eqrel_class3i)
qed

lemma classes_eq_or_disj:
  "\<lbrakk>is_eqrel X R; t \<in> X/R; s \<in> X/R\<rbrakk> \<Longrightarrow> t \<inter> s= {} \<or>  t = s "
  using quotient_disj3 by blast

lemma classes_eq_or_disj2:
  "\<lbrakk>is_eqrel X R; t \<in> X/R; s \<in> X/R; x \<in> s; x \<in> t\<rbrakk> \<Longrightarrow> t = s "
  by (simp add: quotient_disj1 quotient_disj2)

lemma classes_eqI:
  assumes A0:"is_eqrel X R" and A1:"t\<in>X/R" and A2:"s\<in>X/R" and A3:"x\<in>t" and A4:"x\<in>s" 
  shows "t = s"  
  using A0 A1 A2 A3 A4 classes_eq_or_disj2[of X R t s x] by blast

lemma unique_class0:
  assumes A0:"is_eqrel X R" and A1:"x \<in> X"
  shows "\<exists>t \<in> (X/R). x \<in> t"
proof-
  let ?t="R``{x}"
  have B0:"?t \<in> X/R"
    by (simp add: A1 quotientI1)
  have B1:"x \<in> ?t"
    using A0 A1 eqrel_class3[of X R x] by blast
  then show "\<exists>t\<in>(X/R). x \<in> t"
    using B0 by blast
qed

lemma unique_class1:
  assumes A0:"is_eqrel X R" and A1:"x \<in> X" 
  shows "\<And>s::'a set. \<lbrakk>s \<in> (X/R); x\<in>s\<rbrakk> \<Longrightarrow> s = R `` {x}"
proof-
  fix s assume C0:"s \<in> (X/R)" and C1:"x\<in>s"
  then obtain y where C2:"y \<in> X" and C3:"R``{y} = s"
    using quotientE2[of s X R] by blast
  then obtain "(x, y) \<in> R"
    using A0 C1 is_eqrelE22 by auto
  then show "s = R``{x}"
    using A0 C3 by (simp add: eqrel_class3e) 
qed

lemma unique_class:
  assumes A0:"is_eqrel X R" and A1:"x \<in> X"
  shows "\<exists>!t \<in> (X/R). x \<in> t"
proof(rule ex1I[where ?a="R``{x}"])
  show C0:"(R``{x})\<in>(X/R) \<and> x\<in>(R``{x})"
    using A0 A1 eqrel_class3[of X R x] quotientI1[of x X R] by blast
  show "\<And>s::'a set. s \<in> X / R \<and> x \<in> s \<Longrightarrow> s = R `` {x}"
    using A0 A1 unique_class1[of X R x] by auto
qed

lemma quotient_to_partition:
  assumes A0:"is_eqrel X R"
  shows "is_part X (quotient X R)"
proof(rule is_partI1)
  show " \<Union> (PosetsRel6B.quotient X R) = X"
    by (simp add: assms quotient_un)
  show "is_disjoint (quotient X R)"
    unfolding is_disjoint_def   using assms quotient_disj3 by blast
   show "{} \<notin> quotient X R"
     by (metis assms empty_iff eqrel_class3 quotientE1)
qed

abbreviation eqcls_to_eqrel:: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a \<times> 'a) set" where
  "eqcls_to_eqrel X P \<equiv> {(x, y) \<in> X \<times> X. \<exists>p \<in> P. {x,y}\<subseteq>p}"

lemma eqcls_to_eqrel_memI1:
  "\<lbrakk>x \<in> X; y \<in> X; p \<in> P; {x,y} \<subseteq> p\<rbrakk> \<Longrightarrow> (x, y) \<in> eqcls_to_eqrel X P"
  by blast

lemma eqcls_to_eqrel_memI2:
  "\<lbrakk>x \<in> X; y \<in> X; p \<in> P; x \<in> p; y \<in> p\<rbrakk> \<Longrightarrow> (x, y) \<in> eqcls_to_eqrel X P"
  by blast

lemma eqcls_to_eqrel_memD1:
  "(x, y) \<in> eqcls_to_eqrel X P \<Longrightarrow> x \<in> X \<and> y \<in> X \<and> (\<exists>p \<in> P. x \<in> p \<and> y \<in> p)"
  by auto

lemma partition_to_quotient:
  assumes A0:"is_part X P"
  shows "is_eqrel X (eqcls_to_eqrel X P)"
proof-
  let ?R="eqcls_to_eqrel X P"
  show ?thesis
  proof(rule is_eqrelI1)   
    show "refl_on X ?R"
  proof(rule refl_onI)
    show "?R \<subseteq> X \<times> X"
      by blast
    show "\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> ?R"
    proof-
      fix x assume xmem:"x \<in> X"
      then obtain p where "p \<in> P" and "x \<in> p"
        using A0 is_partE1[of X P x] by blast
      then show "(x,x)\<in>?R"
         using xmem by blast
    qed
  qed
 show "sym ?R"
  unfolding sym_def by auto
 show "trans ?R"
 proof(rule transI)
  fix x y z assume C0:"(x, y) \<in> ?R" and C1:"(y, z) \<in> ?R"
  then obtain pxy pyz where C2:"pxy \<in> P" and C3:"{x, y}\<subseteq>pxy" and C4:"pyz \<in>P" and C5:"{y,z}\<subseteq>pyz"
     by auto
  then obtain C6:"y \<in> pxy \<inter> pyz"
    by blast
  then obtain C7:"pxy=pyz"
    by (metis A0 C2 C4 empty_iff is_disjoint_def is_part_def)
  then obtain "{x,z}\<subseteq> pxy"
    using C3 C5 by blast
  then show "(x, z) \<in> ?R"
    using C0 C1 C2  by blast
  qed
 qed
qed

lemma quotient_to_partition2:
  assumes A0:"is_eqrel X R" 
  shows "eqcls_to_eqrel X (quotient X R) = R"
proof-
  let ?XR="(quotient X R)" let ?RXR="eqcls_to_eqrel X ?XR"
  show ?thesis
  proof
    show "?RXR \<subseteq> R"
      using assms quotient_disj2 by fastforce
    next
    show "R \<subseteq> ?RXR"
    proof
      fix z assume B0:"z \<in> R"
      then obtain x y where B1:"(x, y)\<in>R" and B2:"z=(x,y)"
        by (metis prod.exhaust_sel) 
      then obtain B3:"{x,y}\<subseteq> R``{x}" and B4:"R``{x}=R``{y}" and B5:"(x, y) \<in> X \<times> X"
        using assms eqrelE4 eqrel_class2 eqrel_class3 by fastforce
      have B6:"R``{x}\<in>?XR"
        by (meson B5 SigmaE2 quotientI1)
      then show "z \<in> ?RXR"
        using B2 B3 B5 by blast
    qed
  qed
qed
  

lemma partition_to_quotient2:
  assumes A0:"is_part X P"
  shows "quotient X (eqcls_to_eqrel X P) = P"
proof-
  let ?RP="(eqcls_to_eqrel X P)" let ?PRP="quotient X ?RP"
  show ?thesis
  proof
    show "?PRP \<subseteq> P"
    proof
      fix z assume B0:"z \<in> ?PRP"
      then obtain x where C0:"x \<in> X" and C1:"z=?RP``{x}"
        by (meson quotientE4)
      then obtain p where C2:"p \<in> P" and C3:"x \<in> p"
        by (meson assms is_partE1)
      have C4:"\<And>q. q \<in> P \<Longrightarrow> x \<in> q \<Longrightarrow> p=q"
        by (meson C0 C2 C3 assms is_part_ex2)
      then have C5:"\<And>y. y \<in> z \<Longrightarrow> y \<in> p "
        using A0 C1 by blast
      also have B6:"\<And>y. y \<in> p \<Longrightarrow> y \<in> z"
        using C0 C1 C2 C3 A0 is_partE2 by(auto)
      then obtain "z=p"
        by (simp add: calculation equalityI subsetI)
      then show "z \<in> P"
        using C2 by blast
    qed
    show "P \<subseteq> ?PRP"
    proof
      fix z assume B0:"z \<in> P"
      then obtain x where C0:"x \<in> z"
        using assms is_part_def by fastforce 
      then obtain C1:"x \<in> X"
        using B0 assms is_partE2 by auto
      then obtain C2:"\<exists>!p \<in> P. x \<in> p"
        by (meson assms is_part_unique)
      have C3:"\<And>y. y \<in> z \<Longrightarrow> (x, y) \<in> ?RP"
        using B0 C0 assms is_partE2 by fastforce
      have C4:"\<And>y. y \<in> ?RP``{x} \<Longrightarrow> y \<in> z"
        using B0 C0 C2 by blast
      have "?RP``{x}=z"
        using B0 C0 C2 C3 by auto
      then show "z \<in> ?PRP"
        by (meson C1 quotientI1)
    qed
  qed
qed

lemma eqrel_class_sat:
  assumes "is_eqrel X R"
  shows "R``{x}=(\<Union>y \<in> R``{x}. R``{y})"
  (is "?LHS = ?RHS")
proof(rule subset_antisym)
  show "?LHS \<subseteq> ?RHS"
    using assms(1) eqrel_class1b by fastforce
  show "?RHS \<subseteq> ?LHS"
    using assms(1) eqrel_class3e by fastforce
qed
    

subsection Compat

definition eqr_compat_prop :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where 
  "eqr_compat_prop X R P \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. (P x) \<longrightarrow> (x, y) \<in> R \<longrightarrow> P y)"

lemma finer_eqrel1:
  "\<lbrakk>S \<subseteq> R; is_eqrel X R; is_eqrel X S\<rbrakk> \<Longrightarrow> S``(R``{x}) = R``{x}"
  by(auto simp add:eqrel_class3e)

lemma finer_eqrel2:
  "\<lbrakk>S \<subseteq> R; is_eqrel X R; is_eqrel X S\<rbrakk> \<Longrightarrow> R``(S``{x}) = R``{x}"
  by(auto simp add:eqrel_class3e)

lemma finer_eqrel3:
  "\<lbrakk>S \<subseteq> R; is_eqrel X R; is_eqrel X S\<rbrakk> \<Longrightarrow> quotient X R = (\<Union>x \<in> (quotient X S). {R``x})"
  by(auto simp add:quotient_def image_UN finer_eqrel2)



lemma eqr_compat_p:
  assumes A0:"is_eqrel X R" and A1:"t \<in> (X/R)" and A2:"eqr_compat_prop X R P"
  shows "(\<exists>x \<in> t. P x) \<longleftrightarrow> (\<forall>x \<in> t. P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume LHS:?lhs
  show ?rhs
  proof-
    obtain a where A3:"a \<in>t" and A4:"P a"
      using LHS by blast
    then obtain B1:"\<And>x. x \<in> t \<Longrightarrow> (a, x) \<in> R"
      by (meson A0 A1 quotient_disj2)
    have "\<And>x. x \<in> t \<Longrightarrow> P x"
    proof-
      fix x assume B2:"x \<in> t" 
      from B1 obtain B3:"(a, x) \<in> R"
        using B2 by auto
      obtain "x \<in> X" and "a \<in> X"
        by (meson A0 B3 eqrel_class3e)
       then show "P x" 
         by (meson A2 A4 B3 eqr_compat_prop_def) 
    qed
    then show ?thesis
      by simp
  qed
  next
  assume RHS:?rhs
  show ?lhs
    by (metis A0 A1 RHS eqrel_class3 quotientE1)
qed

   

definition is_eqr_compat::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "is_eqr_compat X R f \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. (x, y) \<in> R \<longrightarrow> f x = f y)"

lemma is_eqr_compatI1:
  "(\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> f x = f y) \<Longrightarrow> is_eqr_compat X R f"
  by (simp add: is_eqr_compat_def)

lemma is_eqr_compatI2:
  "is_eqrel X R \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; R``{x}=R``{y}\<rbrakk> \<Longrightarrow> f x = f y) \<Longrightarrow> is_eqr_compat X R f"
  by (meson eqrel_class3e is_eqr_compatI1)

lemma is_eqr_compatE1:
  "is_eqrel X R \<Longrightarrow> is_eqr_compat X R f \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> f x = f y"
  by (simp add: eqrelE4 is_eqr_compat_def)
                                                      
lemma is_eqr_compatE2:
  "is_eqrel X R \<Longrightarrow> is_eqr_compat X R f \<Longrightarrow> t \<in> (X/R) \<Longrightarrow> x \<in> t \<Longrightarrow> y \<in> t \<Longrightarrow> f x = f y"
  using quotient_mem_elem[of X R t x y] is_eqr_compatE1[of X R f x y] by blast

lemma is_eqr_compat_iff:
  "is_eqrel X R \<Longrightarrow> ((\<forall>x \<in> X. \<forall>y \<in> X. R``{x}=R``{y} \<longrightarrow> f x = f y)) \<longleftrightarrow> is_eqr_compat X R f "
  by (simp add: eqrel_class3e is_eqr_compat_def)

lemma is_eqr_compat_finer:
  "\<lbrakk>is_eqrel X R; is_eqrel X S; S \<subseteq> R; is_eqr_compat X R f\<rbrakk> \<Longrightarrow>is_eqr_compat X S f"
  by (simp add: in_mono is_eqr_compat_def)

definition  eqr_associated::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set" where
  "eqr_associated X f \<equiv> {(x, y) \<in> X \<times> X. f x = f y}"

lemma eqr_associated_sym:
  "sym (eqr_associated X f)"
  unfolding eqr_associated_def sym_def by auto

lemma eqr_associated_refl:
  "refl_on X (eqr_associated X f)"
  unfolding refl_on_def eqr_associated_def by(auto)
  
lemma eqr_associated_trans:
  "trans (eqr_associated X f)"
  unfolding trans_def eqr_associated_def by(auto)

lemma eqr_associated_is_eqr:
  "is_eqrel X (eqr_associated X f)"
   using eqr_associated_sym eqr_associated_refl eqr_associated_trans is_eqrelI1 by blast
  
lemma eqr_associated_compat:
  "is_eqr_compat X (eqr_associated X f) f"
  by (simp add: is_eqr_compat_def eqr_associated_def)

lemma eqr_associated_memD:
  "(x, y) \<in> eqr_associated X f \<Longrightarrow> f x= f y \<and> x \<in> X \<and> y \<in> X "
   unfolding eqr_associated_def by simp

lemma eqr_associated_memI:
  "\<lbrakk>f x= f y; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> eqr_associated X f  "
   unfolding eqr_associated_def by simp

lemma eqr_associated_mem_iff:
  "(x, y)\<in> (eqr_associated X f) \<longleftrightarrow> f x= f y\<and> x \<in> X \<and> y \<in> X"
  by(rule iffI,erule eqr_associated_memD, auto intro: eqr_associated_memI)

definition canonical_proj::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "canonical_proj X R \<equiv> (\<lambda>x. THE t. t \<in> (X/R) \<and>  x \<in> t)"


lemma canonical_proj_eq:
  assumes A0:"is_eqrel X R" and A1:"x \<in> X"
  shows "canonical_proj X R x = R``{x}"
  unfolding canonical_proj_def
proof(rule the_equality)
  show P0:"R `` {x} \<in> X / R \<and> x \<in> R `` {x}"
    using A0 A1 eqrel_class3[of X R x] quotientI1[of x X R] by fastforce
  show "\<And>t::'a set. t \<in> X / R \<and> x \<in> t \<Longrightarrow> t = R `` {x}"
  proof-
    fix t assume A2:"t \<in> X/R \<and> x \<in> t"
    show "t = R``{x}"
      using A0 A1 A2 P0 eqrel_class4[of X R x] quotient_disj1[of X R t] by blast
  qed
qed


lemma canonical_proj_props:
  assumes A0:"is_eqrel X R"
  shows canonical_proj_props1:"\<And>x. x \<in> X \<Longrightarrow> canonical_proj X R x \<in> X/R" and
        canonical_proj_props2:"\<And>t. t \<in> X/R \<Longrightarrow> (\<exists>x \<in> X.  canonical_proj X R x=t)" and
        canonical_proj_props3:"\<And>t. t \<in> X/R \<Longrightarrow> x \<in> t \<Longrightarrow> (canonical_proj X R x=t)" and
        canonical_proj_props4:"surj_into  (canonical_proj X R) (X/R)" and
        canonical_proj_props5:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R \<longleftrightarrow> (canonical_proj X R) x = (canonical_proj X R) y" and
        canonical_proj_props6:"(canonical_proj X R)`(X) =(X/R)"
proof-
  show P0:"\<And>x. x \<in> X \<Longrightarrow> canonical_proj X R x \<in> X/R"
    by (simp add: assms canonical_proj_eq quotientI1)
  show P1:"\<And>t. t \<in> X/R \<Longrightarrow> (\<exists>x \<in> X.  canonical_proj X R x=t)" 
 proof-
    fix t assume B0:"t \<in> X/R"
    then obtain x where B1:"x \<in> X" and B2:"t = R``{x}" 
      using quotientE2[of t X R] by blast
    then obtain "canonical_proj X R x = R``{x}"
      using A0 B1 canonical_proj_eq[of X R x] by blast
    then show "\<exists>x \<in> X. canonical_proj X R x=t"
      using B1 B2 by auto
  qed
  show P2:"\<And>t. t \<in> X/R \<Longrightarrow> x \<in> t \<Longrightarrow> (canonical_proj X R x=t)"
  proof-
    fix t assume B0:"t \<in> X/R" and B1:"x \<in> t"
    show "(canonical_proj X R x=t)"
    unfolding canonical_proj_def 
    proof(rule the_equality)
      show " t \<in> X / R \<and> x \<in> t"
        by (simp add: B0 B1)
      show "\<And>s.  s\<in>(X/R) \<and> x\<in>s \<Longrightarrow> s=t"
        using A0 B0 B1 classes_eqI[of X R t _ x] by blast
      qed
   qed
   show P3:"surj_into (canonical_proj X R) (X/R)"
     using P1 surj_intoI[of "X/R"  "(canonical_proj X R)"] by auto
   show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R \<longleftrightarrow> (canonical_proj X R) x = (canonical_proj X R) y"
     using A0 canonical_proj_eq[of X R] eqrel_class3e[of X R] by auto
   show P4:"(canonical_proj X R)`(X) =(X/R)"
     by (simp add: PosetsRel6B.quotient_def UNION_singleton_eq_range assms canonical_proj_eq)
qed

lemma is_eqr_compatI3:
  "is_eqrel X R \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (canonical_proj X R) x = (canonical_proj X R) y\<rbrakk> \<Longrightarrow> f x = f y) \<Longrightarrow> is_eqr_compat X R f"
  using canonical_proj_props5[of X R] is_eqr_compatI1[of X R f] by(blast)



lemma eqr_associated_mem_iff_singleton:
  "(x, y)\<in> (eqr_associated X f) \<longleftrightarrow> (eqr_associated X f)``{x}=(eqr_associated X f)``{y} \<and> x \<in> X \<and> y \<in> X"
  by (simp add: eqrel_class3e eqr_associated_is_eqr)


lemma prj_compat:
  "is_eqrel X R \<Longrightarrow> is_eqr_compat X R (canonical_proj X R)"
  by (simp add: canonical_proj_props5 is_eqr_compat_def)


lemma is_eqr_compat1:
  assumes A0:"is_eqrel X R" and A1:"is_eqr_compat X R f" and A2:"t \<in> quotient X R" and A3:"y \<in> t"
  shows "(\<exists>x \<in> t. f x = f y) \<longleftrightarrow> (\<forall>x \<in> t. f x = f y)"
proof
  assume L:"\<exists>x \<in> t. f x = f y"
  then obtain a where B0:"a \<in> t" and B1:"f a = f y"
    by blast
  have B2:"(y, a)\<in>R"
    by (meson A0 A2 A3 B0 quotient_disj2)
  show R:"\<forall>x \<in> t. f x = f y"
  proof
    fix x assume A4:"x \<in> t"
    then obtain B3:"(a, x)\<in>R"
      by (metis A0 A2 B0 quotient_disj2)
    then obtain "(y,x)\<in>R" and "x \<in> X" and "y \<in> X"
      by (meson A0 B2 eqrelE4 is_eqrelE3 transE)
    then show "f x = f y"
      using A1 unfolding is_eqr_compat_def by(auto)
  qed
  next
  assume R:"\<forall>x \<in> t. f x = f y"
  then show L:"\<exists>x \<in> t. f x = f y"
    using A3 by fastforce
qed


lemma factor_mapping:
  assumes gsurj:"surj_into g Y" and vim:"(image g X) = Y" and compat:"(\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
  shows "\<exists>h. \<forall>x \<in> X. f x = h (g x)"
proof-
  let ?s="fun_section g X Y"
  have rinv1:"is_right_inv Y g ?s"
    by (simp add: gsurj section_is_rinv vim)
  then obtain P0:"\<And>y. y \<in> Y \<Longrightarrow> g (?s y) = y"
    by (simp add: is_right_invE1)
  define h where  "h \<equiv> f \<circ>?s"
  have "\<And>x. x \<in> X \<Longrightarrow>  f x = h (g x)"
  proof-
    fix x assume A0:"x \<in> X"  then obtain B0:"g x \<in> Y"
      using vim by blast
      then obtain B0:"g x \<in> Y"  and B1:"?s (g x) \<in> X"
      by (metis (mono_tags, lifting) A0  fun_section_def someI_ex)
    then obtain B2:"g (?s (g x)) = g x"
      by (simp add: P0)
    then obtain "f (?s (g x)) = f x"
      using compat A0 B1 by blast
    then show "f x = h (g x) "
      unfolding h_def by simp
  qed
  then show ?thesis
    by auto
qed

definition proj_section::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "proj_section X R \<equiv> fun_section (canonical_proj X R) X (X/R)"


lemma proj_section1:
  assumes eqr:"is_eqrel X R"
  shows "is_right_inv (X/R) (canonical_proj X R) (proj_section X R)"
  by (simp add: canonical_proj_props4 canonical_proj_props6 eqr proj_section_def section_is_rinv)

lemma proj_section2:
  assumes eqr:"is_eqrel X R"
  shows "\<And>t. t \<in>(X/R) \<Longrightarrow> (proj_section X R) t \<in> X"
  by (simp add: canonical_proj_props4 canonical_proj_props6 eqr proj_section_def section_is_into)


lemma proj_section2b:
  "is_eqrel X R \<Longrightarrow> (proj_section X R)`(X/R) \<subseteq> X"
  by (simp add: image_subsetI proj_section2)

lemma proj_section3:
  assumes eqr:"is_eqrel X R"
  shows "\<And>t. t \<in>(X/R) \<Longrightarrow>  (canonical_proj X R) ((proj_section X R) t) = t"
  using eqr is_right_invE1[of "(X/R)" "(canonical_proj X R)"] proj_section1[of X R] by blast


lemma proj_section4:
  assumes eqr:"is_eqrel X R"
  shows "\<And>t. t \<in>(X/R) \<Longrightarrow> ((proj_section X R) t) \<in> t" 
  using  canonical_proj_eq[of X R] eqr eqrel_class3[of X R] proj_section2[of X R] proj_section3[of X R] by blast

lemma factor_mapping_eqrel1:
  fixes X::"'a set" and R::"'a rel"
  defines "\<pi> \<equiv> canonical_proj X R"
  assumes eqr:"is_eqrel X R" and  compat:"(\<forall>x \<in> X. \<forall>y \<in> X. \<pi> x = \<pi> y \<longrightarrow> f x = f y)"
  shows "\<exists>h. \<forall>x \<in> X. f x = h (\<pi> x)"
proof(rule factor_mapping[where ?Y="X/R"])
  show  "surj_into \<pi> (X / R)"
    unfolding \<pi>_def
    by (simp add: canonical_proj_props4 eqr)  
  show " \<pi> ` X = X / R"
    by (simp add: quotient_def UNION_singleton_eq_range \<pi>_def canonical_proj_eq eqr)
  show " \<forall>x::'a\<in>X. \<forall>y::'a\<in>X. \<pi> x = \<pi> y \<longrightarrow> f x = f y"
    using compat by blast
qed



lemma factor_mapping_eqrel2:
  fixes X::"'a set" and R::"'a rel"
  defines "\<pi> \<equiv> canonical_proj X R"
  assumes eqr:"is_eqrel X R" and  factorizable: "\<exists>h. \<forall>x \<in> X. f x = h (\<pi> x)"
  shows compat:"(\<forall>x \<in> X. \<forall>y \<in> X. \<pi> x = \<pi> y \<longrightarrow> f x = f y)"
  using factorizable by force



lemma factor_mapping_eqrel3:
  fixes X::"'a set" and R::"'a rel"
  defines "\<pi> \<equiv> canonical_proj X R"
  assumes eqr:"is_eqrel X R" 
  shows "is_eqr_compat X R f \<longleftrightarrow> (\<exists>h. \<forall>x \<in> X. f x = h (\<pi> x))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L0:?lhs  then show ?rhs using eqr factor_mapping_eqrel1[of X R f] unfolding is_eqr_compat_def \<pi>_def
    by (simp add: L0 canonical_proj_eq is_eqr_compat_iff)
  next
  assume R0:?rhs
  show ?lhs 
    using R0 eqr is_eqr_compatI3[of X R]  factor_mapping_eqrel2[of X R] \<pi>_def by blast
qed


lemma section_existence_concrete:
  assumes fmap:"f`X \<subseteq> Z" and gsurj:"g`X = Y" and compat:"(\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
  defines "h \<equiv> (\<lambda>y. f (SOME x. x \<in> X \<and> g x =y))"
  shows "\<And>x. x\<in>X \<Longrightarrow> f x = h (g x)"
proof-
  fix x assume C0:"x \<in> X"
  show "f x = h (g x)"
  unfolding h_def
  proof(rule someI2_ex)
    show "\<exists>a. a \<in> X \<and> g a = g x"
      using C0 by auto
    show "\<And>b. b \<in> X \<and> g b = g x \<Longrightarrow> f x = f b"
      using C0 compat by fastforce
  qed
qed


lemma canonical_proj_section_exists:
  "is_eqrel X R \<Longrightarrow> \<exists>s. is_right_inv (X/R) (canonical_proj X R) s"
  by(rule surj_implies_ex_rinv, erule canonical_proj_props4)

lemma section_existence_concrete2:
  assumes fmap:"f`X \<subseteq> Z" and gsurj:"surj_into f Y" and compat:"(\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
  defines "h \<equiv> (\<lambda>y. f (SOME x. x \<in> X \<and> g x =y))"
  shows "\<And>x. x\<in>X \<Longrightarrow> f x = h (g x)"
proof-
  fix x assume C0:"x \<in> X"
  show "f x = h (g x)"
  unfolding h_def
  proof(rule someI2_ex)
    show "\<exists>a. a \<in> X \<and> g a = g x"
      using C0 by auto
    show "\<And>b. b \<in> X \<and> g b = g x \<Longrightarrow> f x = f b"
      using C0 compat by fastforce
  qed
qed

lemma section_existence:
  assumes fmap:"f`X \<subseteq> Z" and gsurj:"g`X = Y" 
  shows "(\<exists>h::('b \<Rightarrow> 'c). \<forall>x \<in> X. f x = (h (g x))) \<longleftrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
proof-
  let ?LHS="\<exists>h::('b \<Rightarrow> 'c). \<forall>x \<in> X. f x = (h (g x))" let ?RHS=" (\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
  show ?thesis
  proof
    assume AL:?LHS
    then obtain h where B0:"\<forall>x \<in> X. f x = (h (g x))"
      by auto
    have "\<And>x y. \<lbrakk>x \<in> X; y \<in> X; g x = g y\<rbrakk> \<Longrightarrow> f x = f y"
    proof-
      fix x y assume B1:"x \<in> X" and B2:"y \<in> X" and B3:"g x = g y"
      have "f x = h (g x)"
        by (simp add: B0 B1)
      also have "... = h (g y)"
        by (simp add: B3)
      also have "... = f y"
        by (simp add: B0 B2)
      finally show "f x = f y"
        by simp
    qed
    then show ?RHS
      by blast
    next
    assume AR:?RHS
    show ?LHS
    proof-
      define s::"'b \<Rightarrow> 'a" where "s \<equiv> (\<lambda>y. SOME x. x \<in> X \<and> g x =y) "
      define h::"'b \<Rightarrow> 'c" where "h \<equiv> (\<lambda>y. f (s y))"
      have B1:"\<And>x. x\<in>X \<Longrightarrow> f x = h (g x)"
      proof-
        fix x assume C0:"x \<in> X"
        show "f x = h (g x)"
        unfolding h_def s_def
        proof(rule someI2_ex)
          show "\<exists>a. a \<in> X \<and> g a = g x"
            using C0 by auto
          show "\<And>b. b \<in> X \<and> g b = g x \<Longrightarrow> f x = f b"
            by (simp add: AR C0)
        qed
      qed
      then show ?thesis
        by auto
    qed
  qed
qed

lemma section_existence_alt:
  assumes fmap:"f`X \<subseteq> Z" and gsurj:"g`X = Y" 
  shows "(\<exists>h::('b \<Rightarrow> 'c). \<forall>x \<in> X. (h (g x)) =  f x) \<longleftrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
proof-
  have "(\<exists>h::('b \<Rightarrow> 'c). \<forall>x \<in> X. (h (g x)) =  f x) \<longleftrightarrow> (\<exists>h::('b \<Rightarrow> 'c). \<forall>x \<in> X. f x = (h (g x)))"
    by metis
  also have "... \<longleftrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
    using fmap gsurj section_existence[of f X Z g Y] by fastforce
  finally show ?thesis
    by blast
qed



lemma eqr_inj:
  assumes A0:"f`X \<subseteq> Y" 
  defines "R \<equiv> eqr_associated X f"
  defines "\<pi> \<equiv> canonical_proj X R"
  defines "s \<equiv> proj_section X R"
  defines "h \<equiv> f \<circ> s"
  shows "inj_on h (X/R)"
proof-
  obtain A1:"is_eqrel X R"
    by (simp add: R_def eqr_associated_is_eqr)
  obtain A5:"is_eqr_compat X R f"
    by (simp add: R_def eqr_associated_compat)
  have B0:"\<And>t1 t2. \<lbrakk>t1 \<in> (X/R); t2 \<in> (X/R); h t1 = h t2\<rbrakk> \<Longrightarrow> t1 = t2  "
  proof-
    fix t1 t2 assume A2:"t1 \<in> X/R" and A3:"t2 \<in>X/R" and A4:"h t1 = h t2"
    have B0:"\<And>t. t \<in> (X/R) \<Longrightarrow> h (\<pi> (s t)) = h t"
      by (simp add: A1 \<pi>_def proj_section3 s_def)
    then obtain B1:"f (s (\<pi> (s t1))) = f (s (\<pi> (s t2)))"
      using A2 A3 A4 h_def by auto
    then obtain x1 x2 where B2: "x1 \<in> t1" and B3:"x2 \<in> t2" and B4:"s t1 = x1" and B5:"s t2 = x2"
      using A1 A2 A3 proj_section4 s_def by blast 
    then obtain B6:"s (\<pi> (s t1)) = x1" and "s (\<pi> (s t2)) = x2"
      by (simp add: A1 A2 A3 \<pi>_def proj_section3 s_def)
    then obtain B7:"f x1 = f x2"
      using B1 by auto
    have B8:"\<And>x y. \<lbrakk>x \<in> t1; y \<in> t2\<rbrakk> \<Longrightarrow> f x = f y"
      by (metis A1 A2 A3 B2 B3 B7 R_def eqr_associated_mem_iff quotient_disj2)
    show "t1 = t2"
      by (metis A1 A2 A3 B2 B3 B4 B5 B7 R_def eqr_associated_mem_iff proj_section2 quotient_disj1 s_def)
  qed
  then show ?thesis
    by (simp add: inj_onI)
qed



definition fun_induced_quotient::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "fun_induced_quotient X R f \<equiv> f \<circ> (proj_section X R)"

lemma eqr_inj2:
   "inj_on (fun_induced_quotient X (eqr_associated X f) f)  (X/(eqr_associated X f))"
proof-
  let ?R="eqr_associated X f"
  let ?p="canonical_proj X ?R"
  let ?s="proj_section X ?R"
  let ?h="fun_induced_quotient X ?R f"
  obtain A1:"is_eqrel X ?R"
    by (simp add:  eqr_associated_is_eqr)
  obtain A5:"is_eqr_compat X ?R f"
    by (simp add:  eqr_associated_compat)
  have B0:"\<And>t1 t2. \<lbrakk>t1 \<in> (X/?R); t2 \<in> (X/?R); ?h t1 = ?h t2\<rbrakk> \<Longrightarrow> t1 = t2  "
  proof-
    fix t1 t2 assume A2:"t1 \<in> X/?R" and A3:"t2 \<in>X/?R" and A4:"?h t1 = ?h t2"
    have B0:"\<And>t. t \<in> (X/?R) \<Longrightarrow>?h (?p (?s t)) = ?h t"
      by (simp add: A1  proj_section3 )
    then obtain B1:"f (?s (?p (?s t1))) = f (?s (?p (?s t2)))"
      using A2 A3 A4 unfolding fun_induced_quotient_def by auto
    then obtain x1 x2 where B2: "x1 \<in> t1" and B3:"x2 \<in> t2" and B4:"?s t1 = x1" and B5:"?s t2 = x2"
      using A1 A2 A3 proj_section4 by blast 
    then obtain B6:"?s(?p (?s t1)) = x1" and "?s (?p (?s t2)) = x2"
      using A1 A2 A3 proj_section3 by fastforce
    then obtain B7:"f x1 = f x2"
      using B1 by auto
    have B8:"\<And>x y. \<lbrakk>x \<in> t1; y \<in> t2\<rbrakk> \<Longrightarrow> f x = f y"
      by (metis A1 A2 A3 B2 B3 B7 eqr_associated_mem_iff quotient_disj2)
    show "t1 = t2"
      by (metis A1 A2 A3 B2 B3 B4 B5 B7 eqr_associated_mem_iff proj_section2 quotient_disj1)
  qed
  then show ?thesis
    by (simp add: inj_onI)
qed




lemma fun_induced_quotient_im:
  assumes eqr:"is_eqrel X R" and compat:"is_eqr_compat X R f" and img:"f`X=Y"
  shows "(fun_induced_quotient X R f)`(X/R) = Y"
proof-
  let ?h="fun_induced_quotient X R f"
  let ?s="proj_section X R"
  let ?p="canonical_proj X R"
  have "\<And>y. y \<in> Y \<Longrightarrow> (\<exists>t \<in> (X/R). ?h t = y)"
  proof-
    fix y assume yin:"y \<in> Y"
    then obtain x where xin:"x \<in> X" and fxy:"f x = y"
      using img by blast
    obtain t where tin:"t \<in> X/R" and teq:"t = ?p x"
      by (simp add: \<open>(x::'a) \<in> (X::'a set)\<close> canonical_proj_props1 eqr)
    then obtain xin2:"x \<in> t"
      using eqr xin canonical_proj_eq[of X R x] eqrel_class3[of X R x] by blast
    obtain z where rin1:"z \<in> X" and req1:"?s t = z"
      using eqr proj_section2 tin by auto
    have zin2:"z \<in> t"
      using eqr proj_section4 req1 tin by auto
    have fzx:"f z = f x"
      using eqr is_eqr_compatE2[of X R f t z x] compat tin xin2 zin2 by blast
    have "?h t =  f (?s t)"
       by (simp add: fun_induced_quotient_def)
    also have "... = f z"
      by (simp add: req1)
    also have "... = y"
      by (simp add: fxy fzx)
    finally show " (\<exists>t \<in> (X/R). ?h t = y)"
      using tin by auto
  qed
  then obtain "Y \<subseteq> ?h`(X/R)"
    by blast
  also have "?h`(X/R) \<subseteq> Y"
    unfolding fun_induced_quotient_def using proj_section2b[of X R] img eqr by auto
  then show ?thesis
    using calculation by blast
qed


lemma fun_induced_quotient_val:
  assumes eqr:"is_eqrel X R" and compat:"is_eqr_compat X R f"
  shows "\<And>t. t \<in> X/R \<Longrightarrow> x \<in> t  \<Longrightarrow> (fun_induced_quotient X R f) t=f x"
proof-
 let ?s="proj_section X R"
  let ?h="fun_induced_quotient X R f"
  fix t assume tin:"t \<in> X/R" and xin:"x \<in> t"
  obtain z where rin1:"z \<in> X" and req1:"?s t = z"
     using eqr proj_section2 tin by auto
  have zin2:"z \<in> t"
    using eqr proj_section4 req1 tin by auto
  have fzx:"f z = f x"
     using eqr is_eqr_compatE2[of X R f t z x] compat tin xin zin2 by blast
  then show "?h t = f x"
    by (simp add: fun_induced_quotient_def req1)
qed
  

lemma is_eqr_compat_concrete:
  assumes A0:"is_eqrel X R" and A1:"is_eqr_compat X R f"
  shows "\<And>x. x \<in> X \<Longrightarrow>   (fun_induced_quotient X R f) ((canonical_proj X R) x) = f x"
proof-
  let ?p="(canonical_proj X R)"
  let ?s="proj_section X R"
  let ?h="fun_induced_quotient X R f"
  fix x assume xin:"x \<in> X"
  obtain t where tin:"t \<in> X/R" and xin:"x \<in> t"
    by (meson A0 unique_class0 xin)
  then obtain peq:"?p x = t"
    by (simp add: A0 canonical_proj_props3)
  obtain z where rin1:"z \<in> X" and req1:"?s t = z"
    using A0 proj_section2 tin by auto
  have zin2:"z \<in> t"
    using A0 proj_section4 req1 tin by auto
  have fzx:"f z = f x"
     using A0 is_eqr_compatE2[of X R f t z x] A1 tin xin zin2 by blast
  have "?h (?p x) = ?h t"
    using peq by auto
  also have "... = f (?s t)"
    by (simp add: fun_induced_quotient_def)
  also have "... = f z"
    by (simp add: req1)
  finally show "?h (?p x) = f x"
    using fzx by auto
qed


lemma quotient_of_quotient:
  assumes A0:"is_eqrel X R" and A1:"is_eqrel X S" and A2:"S \<subseteq> R"
  defines "f \<equiv>canonical_proj X R"  (*X \<longrightarrow> X/R*)
  defines "g \<equiv>canonical_proj X S"  (*X \<longrightarrow> X/S*)
  defines "h \<equiv> fun_induced_quotient X S f" (*X/S \<longrightarrow> X/R*)
  defines "T \<equiv> eqr_associated (X/S) h" (*(X/S) / (R / S) or (R /S)*)
  defines "h1 \<equiv> canonical_proj (X/S) T" (*(X/S) \<longrightarrow> (X/S) / (R /S)*)
  defines "h2 \<equiv> fun_induced_quotient (X/S) T h" (* (X/S) / (R /S) \<longrightarrow> (X / R)*)
  shows quotient_of_quotient1:"\<And>x y. (x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> T \<and> x \<in> X \<and> y \<in> X" and 
        quotient_of_quotient2:"\<And>x. x \<in> X \<Longrightarrow>h (g x) = f x" and
        quotient_of_quotient3:"\<And>t. t \<in> X/R\<Longrightarrow> (\<exists>x \<in> X/S. t = h x)" and
        quotient_of_quotient4:"\<And>t. t \<in> X/S\<Longrightarrow> (\<exists>x \<in> X. t = g x)" and
        quotient_of_quotient5:"\<And>t. t \<in> (X/S) \<Longrightarrow> (h2(h1 t))=h t" and
        quotient_of_quotient6:"inj_on h2 ((X/S)/T)" and
        quotient_of_quotient7:"surj_into  h2 (X/R)"
proof-
  obtain B0:"is_eqr_compat X R f" and B1:"is_eqr_compat X S g"
    by (simp add: A0 A1 f_def g_def prj_compat)
  then obtain B2:"is_eqr_compat X S f"
    using A0 A1 A2 is_eqr_compat_finer by blast
  have B3:"\<And>x y. (x,y)\<in>R  \<longleftrightarrow> f x = f y \<and>  x \<in> X \<and> y \<in> X"
    using A0 canonical_proj_props5[of X R] eqrelE4[of X R] f_def by blast
  have B4:"\<And>x y. (x,y)\<in>S  \<longleftrightarrow> g x = g y \<and>  x \<in> X \<and> y \<in> X"
    using A1 canonical_proj_props5[of X S] eqrelE4[of X S] g_def by blast
  have B5:"\<And>x y. (x,y)\<in>T  \<longleftrightarrow> h x = h y \<and>  x \<in> (X / S) \<and> y \<in> (X / S)"
    unfolding T_def  by (simp add: eqr_associated_mem_iff)
  have B6:"\<And>x. x \<in> X \<Longrightarrow>  h (g x) = f x"
    using is_eqr_compat_concrete[of X S f ] A1 B2 g_def h_def by presburger
  have B7:"\<And>x. x \<in> X \<Longrightarrow> g x \<in> X / S"
    by (simp add: A1 canonical_proj_props1 g_def)
  show P0:"\<And>x y. (x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> T \<and> x \<in> X \<and> y \<in> X"
  proof-
    fix x y 
    have "(x,y) \<in> R \<longleftrightarrow> f x = f y  \<and>  x \<in> X \<and> y \<in> X"
      by (simp add: B3)
    also have "... \<longleftrightarrow> h (g x) =  h (g y)  \<and>  x \<in> X \<and> y \<in> X"
      using B6 by blast
    also have "... \<longleftrightarrow>(g x, g y) \<in> T \<and> x \<in> X \<and> y \<in> X "
      using B5 B7 by blast
    finally show "(x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> T \<and> x \<in> X \<and> y \<in> X "
      by auto
  qed 
  show P1:"\<And>x. x \<in> X \<Longrightarrow>h (g x) = f x"
    by (simp add: B6)
  show P2:"\<And>t. t \<in> X/R\<Longrightarrow> (\<exists>x \<in> X/S. t = h x)"
    by (metis A0 B7 P1 canonical_proj_props2 f_def)
  show P3:"\<And>t. t \<in> X/S \<Longrightarrow> (\<exists>x \<in> X. t = g x)" 
  proof-
    fix t assume C0:"t \<in> quotient X S"
    show "(\<exists>x \<in> X. t = g x)"
      using A1 C0 canonical_proj_props2 g_def by blast
  qed
  show P4:"\<And>t. t \<in> (X/S) \<Longrightarrow> (h2(h1 t))=h t"
    by (simp add: T_def eqr_associated_compat eqr_associated_is_eqr h1_def h2_def is_eqr_compat_concrete) 
  show P5:"inj_on h2 ((X/S)/T)"
    by (simp add: T_def eqr_inj2 h2_def)
  show P6:"surj_into  h2 (X/R)"
    by (metis P2 P4 surj_intoI)
qed


locale quotient_equiv=
  fixes X::"'a set" and
        R::"'a rel" and
        S::"'a rel" 
  assumes Req:"is_eqrel X R" and
          Seq:"is_eqrel X S" and
          finer:"S \<subseteq> R"
begin


definition  f where "f \<equiv> (\<lambda>x. R``{x})" 
definition  g where "g \<equiv> (\<lambda>x. S``{x})" 
definition  h where "h \<equiv> (\<lambda>t. f (SOME x. x \<in> X \<and> S``{x} =t))"
abbreviation XS where "XS \<equiv> quotient X S"
abbreviation RS where "RS \<equiv> kernel XS h"
definition R_mod_S where "R_mod_S \<equiv> kernel (quotient X S) h"



lemma finer1:"\<And>x y. (x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> R_mod_S"  
  using quotient_of_quotient1[of X R S]  R_mod_S_def Req Seq f_def finer g_def h_def by presburger


lemma finer2:"\<And>x. x \<in> X \<Longrightarrow>h (g x) = f x" 
  using quotient_of_quotient2[of X R S]  Req Seq f_def finer g_def h_def by presburger

lemma temp1:"\<And>x. x \<in> X \<Longrightarrow> g x \<in> quotient X S"
  by (simp add: g_def quotientI1)

lemma temp2:"\<And>x. x \<in> X \<Longrightarrow> g x \<in> quotient X S"
  by (simp add: g_def quotientI1)

lemma finer3:
  assumes "t \<in> XS"
  shows "R_mod_S``{t}=h`{t}"

lemma  finer3:"\<And>t. t \<in> quotient X S \<Longrightarrow>  ((R_mod_S``{t})) = {h t}"

end


lemma quotient_of_quotient:
  assumes A0:"is_eqrel X R" and A1:"is_eqrel X S" and A2:"S \<subseteq> R"
  defines  "f \<equiv> (\<lambda>x. R``{x})" 
  defines  "g \<equiv> (\<lambda>x. S``{x})" 
  defines  "h \<equiv> (\<lambda>t. f (SOME x. x \<in> X \<and> S``{x} =t))"
  defines "R_mod_S \<equiv> kernel (quotient X S) h"
  shows quotient_of_quotient1:"\<And>x y. (x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> R_mod_S" and 
        quotient_of_quotient2:"\<And>x. x \<in> X \<Longrightarrow>h (g x) = f x" and
        quotient_of_quotient3:"\<And>t. t \<in> quotient X S \<Longrightarrow>  (R_mod_S``{t}) = (h t)"
proof-
  obtain B0:"is_eqr_compat X R f" and B1:"is_eqr_compat X S g"
    by (simp add: A0 A1 f_def g_def prj_compat)
  then obtain B2:"is_eqr_compat X S f"
    using A0 A1 A2 is_eqr_compat_finer by blast
  have B3:"\<And>x y. (x,y)\<in>R  \<longleftrightarrow> f x = f y \<and>  x \<in> X \<and> y \<in> X"
    by (simp add: A0 eqrel_class3e f_def)
  have B4:"\<And>x y. (x,y)\<in>S  \<longleftrightarrow> g x = g y \<and>  x \<in> X \<and> y \<in> X"
    by (simp add: A1 eqrel_class3e g_def)
  have B5:"\<And>x y. (x,y)\<in>R_mod_S  \<longleftrightarrow> h x = h y \<and>  x \<in> (X / S) \<and> y \<in> (X / S)"
    unfolding R_mod_S_def using kernel_mem_iff[of _ _ "X/S" h] by auto
  have B6:"\<And>x. x \<in> X \<Longrightarrow>  h (g x) = f x"
    using is_eqr_compat_concrete[of X S f ] A1 B2 g_def h_def by presburger
  have B7:"\<And>x. x \<in> X \<Longrightarrow> g x \<in> X / S"
    by (simp add: g_def quotientI1)
  have B8:"\<And>x. g x \<in> X / S \<Longrightarrow> x \<in> X"
    by (metis A1 B4 eqrel_class4 g_def quotientE1)
  show P0:"\<And>x y. (x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> R_mod_S"
  proof-
    fix x y 
    have "(x,y) \<in> R \<longleftrightarrow> f x = f y  \<and>  x \<in> X \<and> y \<in> X"
      by (simp add: B3)
    also have "... \<longleftrightarrow> h (g x) =  h (g y)  \<and>  x \<in> X \<and> y \<in> X"
      using B6 by blast
    also have "... \<longleftrightarrow>(g x, g y) \<in> R_mod_S "
      using B5 B7 B8 by blast
    finally show "(x, y) \<in> R \<longleftrightarrow> (g x, g y) \<in> R_mod_S"
      by auto
  qed 
  show P1:"\<And>x. x \<in> X \<Longrightarrow>h (g x) = f x"
    by (simp add: B6)



definition example_Z where 
  "example_Z \<equiv> {(1::nat, 2::nat)}"

definition example_X::"nat set" where
  "example_X \<equiv> {1,2,3,4,5}"

declare [[show_types=false]]
definition example_S::"(nat \<times> nat) set" where
  "example_S \<equiv> {
      (1,1), (1,2),
      (2,1), (2,2),
                   (3,3),
                         (4,4), (4, 5),
                          (5,4), (5,5)
              }"


definition grpiS :: "(nat \<times> nat set) set" where 
  "grpiS \<equiv> {
              (1, {1, 2}),
              (2, {1, 2}),  
                          (3, {3}), 
                                    (4, {4, 5}),
                                    (5, {4, 5})}"



definition grpiR :: "(nat \<times> nat set) set" where 
  "grpiR \<equiv> {
              (1, {1, 2, 3}),  
              (2, {1, 2, 3}),
              (3, {1, 2, 3}),
                               (4, {4, 5}),
                               (5, {4, 5})}"
 

definition piS::"nat \<Rightarrow> nat set" where 
  "piS x = (if x=1 then {1,2} else if x=2 then {1, 2} else if x=3 then {3} else if x=4 then {4, 5} else {4, 5})"


definition piR::"nat \<Rightarrow> nat set" where 
  "piR x = (if x=1 then {1,2,3} else if x=2 then {1, 2,3} else if x=3 then {1,2,3} else if x=4 then {4, 5} else {4, 5})"


definition piRS::"nat set \<Rightarrow> nat set" where 
  "piRS x = (if x={1,2} then {1,2,3} 
        else if x={3}   then {1,2,3}
        else if x={4,5} then {4,5}      else {4,5})"

definition exampleRS::"(nat set \<times> nat set) set" where 
  "exampleRS \<equiv> {
                  ({1, 2}, {1, 2}), ({1, 2}, {3    }),
                  ({3   }, {1, 2}), ({3   }, {3    }),
                                                       ({4, 5}, {4, 5})
              }"



definition example_R::"(nat \<times> nat) set" where
  "example_R \<equiv> {
      (1,1), (1,2), (1,3),
      (2,1), (2,2), (2,3),
      (3,1), (3,2), (3,3),
                          (4,4), (4, 5),
                          (5,4), (5,5)
              }"

definition exampleX_mod_R  :: "nat set set" where "exampleX_mod_R \<equiv> {{1, 2, 3}, {4, 5}}"
  
definition exampleX_mod_S  :: "nat set set" where "exampleX_mod_S \<equiv> {{1, 2}, {3}, {4, 5}}"

definition exampleXS_mod_RS:: "nat set set set" where "exampleXS_mod_RS \<equiv> {{{1, 2}, {3}}, {{4, 5}}}"

value "example_S \<subseteq> example_R"

value "\<Union>x \<in> example_X. {example_S``{x}}"

value "\<Union>x \<in> example_X. {example_R``{x}}"

lemma example_lem1:"is_eqrel example_X example_S"
  unfolding is_eqrel_def example_X_def example_S_def refl_on_def sym_def trans_def by(auto)

lemma example_lem2:"is_eqrel example_X example_R"
  unfolding is_eqrel_def example_X_def example_R_def refl_on_def sym_def trans_def by(auto)

value "quotient example_X example_S"
value "quotient example_X example_R"
value "quotient exampleX_mod_S exampleRS"

value "example_S``{3}"
value "exampleRS"
value "exampleRS``{{1, 2}}"

value "\<Union>x \<in> example_X. {(x, example_S``{x})}"
value "\<Union>x \<in> example_X. {(x, example_R``{x})}"

value "\<Union>x \<in> example_X. {example_S``{x}}"

value "\<Union>x \<in> example_X. {example_S``{x}}"



print_options
print_codeproc



  
  



definition fun_induced_on_quotient::" 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a set \<Rightarrow> 'b)" where
  "fun_induced_on_quotient X f R  \<equiv> (\<lambda>t. f (SOME x. x \<in> X \<and> R``{x} =t))" 

notation fun_induced_on_quotient ("'(_ _\<^bsub>_')")
print_syntax 

    
lemma is_eqr_compat3:
  assumes A0:"is_eqrel X R" and A1:"f`X \<subseteq> Y" and A2:"is_eqr_compat X R f"
  shows "(\<And>x. x \<in> X \<Longrightarrow> ((X f\<^bsub>R) (R``{x})) = f x)"
proof -
  fix x :: 'a
  assume "x \<in> X"
  then have "f x = f (SOME a. a \<in> X \<and> R `` {a} = R `` {x})"
    using A0 A2 is_eqr_compat_concrete by fastforce
  then show "(X f\<^bsub>R) (R `` {x}) = f x"
    by (simp add: fun_induced_on_quotient_def)
qed


locale equivalence_relation=
  fixes X::"'a set" and
        R::"'a rel"
  assumes eqr:"is_eqrel X R"
begin

definition \<pi> where
   "\<pi> \<equiv> (\<lambda>x. R``{x})"


end


locale quotient_induced_map=
  equivalence_relation+
  fixes f::"'a \<Rightarrow> 'b"
  assumes compat:"is_eqr_compat X R f"
begin


end

locale canonical_decomposition=
  fixes X::"'a set" and
        Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes fmap:"f`X \<subseteq> Y"
begin


definition Rf where "Rf \<equiv> kernel X f"

definition \<pi> where "\<pi> \<equiv> (\<lambda>x. Rf``{x})"

lemma Rf_is_eqr:
  "is_eqrel X Rf"
  by (simp add: Rf_def kernel_is_eqr)

lemma f_compat:
  "is_eqr_compat X Rf f"
  by (simp add: Rf_def kernel_compat)

lemma f_compat2:
  "(\<forall>x \<in> X. \<forall>y \<in> X. \<pi> x = \<pi> y \<longrightarrow> f x = f y)"
  by (simp add: Rf_is_eqr \<pi>_def f_compat is_eqr_compat_iff)

definition XR where 
  "XR \<equiv> quotient X Rf"


definition h where
    "h \<equiv> (\<lambda>t. f (SOME x. x \<in> X \<and> Rf``{x} =t))"



lemma f_factor:
  "\<And>x. x \<in> X \<Longrightarrow>  h (\<pi> x) = f x"
  using is_eqr_compat_concrete[of X Rf f Y]  Rf_is_eqr \<pi>_def f_compat fmap h_def by presburger 

lemma inj_on_quotient:
  "inj_on h XR"
proof(rule inj_onI)
  fix t s assume A0:"t \<in> XR" and A1:"s \<in> XR" and A2:"h t = h s" 
  then obtain x y where A3:"x \<in> X" and A4:"Rf``{x}=t" and A5:"y \<in> X" and A6:"Rf``{y}=s"
    by (metis XR_def quotientE1)
  obtain A7:"t \<in> quotient X Rf" and A8:"s \<in> quotient X Rf"
    using A0 A1 XR_def by auto
  have B0:"f x = (h t)"
    using A3 A4 \<pi>_def f_factor by auto
  also have "...  = h s"
    by (simp add: A2)
  also have "... = f y"
    using A5 A6 \<pi>_def f_factor by auto
  then obtain "f x = f y"
    using calculation by presburger
  then obtain "(x,y) \<in> Rf"
    unfolding Rf_def kernel_def using A3 A5 by blast
  then show "t = s"
    by (metis A4 A6 Rf_is_eqr eqrel_class2)
qed


end



locale magma=
  fixes X::"'a set" and
        f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
  assumes closed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> X"
      
locale equivalence_relation=
  fixes X::"'a set" and
        R::"'a rel"
  assumes ref1:"\<And>x. x \<in> X \<Longrightarrow> (x, x)\<in>R" and
          ref2:"R \<subseteq> X \<times> X" and
          sym[sym]:"(x, y) \<in> R \<Longrightarrow> (y, x) \<in> R" and
          trn[trans]:"(x, y)\<in>R \<Longrightarrow> (y, z)\<in> R \<Longrightarrow> (x, z)\<in>R"
begin

lemma reflexive_on1:
  "(x, y)\<in>R \<Longrightarrow> x \<in> X"
  using ref2  by auto

lemma reflexive_on2:
  "(x,y)\<in>R\<Longrightarrow>y \<in> X"
  using ref2  by auto

lemma reflexive_on3:
  "\<forall>x. (x, x)\<in>R \<longleftrightarrow> x \<in> X"
  using ref1 reflexive_on1 by blast
end


end
