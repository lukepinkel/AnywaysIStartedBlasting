theory q2
  imports Main FuncSet_mod
begin

declare [[show_results, show_abbrevs]]

hide_const map dom partition monoid group inverse Equiv_Relations.quotient


no_notation power (infixr "^" 80)
hide_const power
no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)
hide_fact Equiv_Relations.equiv_class_eq Equiv_Relations.equiv_class_subset
          Equiv_Relations.equiv_class_eq_iff Equiv_Relations.equiv_class_self
          Equiv_Relations.eq_equiv_class
          Equiv_Relations.equiv_class_nondisjoint
          Equiv_Relations.equiv_type
          Equiv_Relations.eq_equiv_class_iff
          Equiv_Relations.disjnt_equiv_class
          Equiv_Relations.quotientI
          Equiv_Relations.quotientE
          Equiv_Relations.Union_quotient
          Equiv_Relations.quotient_disj_strong
          Equiv_Relations.quotient_disj
          Equiv_Relations.quotient_eqI
          Equiv_Relations.quotient_eq_iff
          Equiv_Relations.eq_equiv_class_iff2
          Equiv_Relations.quotient_empty
          Equiv_Relations.proj_def
          quotient_is_empty
          quotient_is_empty2
          singleton_quotient  
          quotient_diff1
    

abbreviation set_mor where "set_mor A B \<equiv> extensional_funcset A B"

lemma compose_set_mor:"\<lbrakk>f \<in> set_mor X Y;g \<in> set_mor Y Z\<rbrakk>\<Longrightarrow>compose X g f \<in> set_mor X Z"
  by (simp add: PiE_iff compose_eq)
  

section \<open>Kernel Pairs\<close>
definition ker where "ker f X \<equiv> {(x, x') \<in> X \<times> X.  f x = f x'}"

lemma ker_equiv1:"ker f X = {u \<in> X \<times> X.  f (fst u) = f (snd u)}"
  by(auto simp add: ker_def)

lemma ker_memD1:"u\<in>ker f X \<Longrightarrow> u \<in> X \<times> X"
  by (simp add: ker_equiv1)

lemma ker_memI1:"\<lbrakk>x \<in> X; x' \<in> X; f x = f x'\<rbrakk> \<Longrightarrow> (x, x') \<in> ker f X" 
  by(simp add:ker_def)

lemma ker_memI2:"\<lbrakk>u \<in> X \<times> X; f (fst u) = f (snd u)\<rbrakk> \<Longrightarrow>u \<in> ker f X"
  by (simp add: ker_equiv1)

lemma ker_memI3:"\<lbrakk>(x,y) \<in> X \<times> X; f x = f y\<rbrakk> \<Longrightarrow>(x,y) \<in> ker f X"
  by (simp add: ker_equiv1)

lemma ker_mem_iff:"(x,y) \<in> X \<times> X \<and> f x = f y \<longleftrightarrow> (x,y) \<in> ker f X"
  by (simp add: ker_equiv1)

lemma ker_memD2:"(x, x') \<in> ker f X \<Longrightarrow> f x = f x'"
  by (simp add: ker_equiv1)

lemma ker_sym1:"(x,x') \<in> ker f X \<Longrightarrow> (x',x) \<in> ker f X"
  by (simp add: ker_equiv1)

lemma ker_sym2:"sym (ker f X)"
  by (simp add: ker_sym1 symI)

lemma ker_refl2:"refl_on X (ker f X)"
  by (simp add: ker_memI1 refl_on_def)

lemma ker_trans1[trans]:"\<lbrakk>(x,x')\<in> ker f X; (x',x'') \<in> ker f X\<rbrakk> \<Longrightarrow> (x,x'')\<in> ker f X"
  by (simp add: ker_def)

lemma ker_trans4:"trans (ker f X)"
  using ker_trans1[of _ _ f X ] transI[of "ker f X"] by blast

lemma ker_subseteq:"ker f X \<subseteq> X \<times> X"
  by (simp add: ker_equiv1)

lemma ker_is_equivalence:"equiv X (ker f X)"
  by (simp add: equivI ker_refl2 ker_subseteq ker_sym2 ker_trans4)

lemma compose_kernel_pair_mono: "ker g X \<subseteq> ker (compose X h g) X"
  by (auto simp add: ker_def compose_eq)

lemma ker_restrict: "ker (restrict f A) A = ker f A"
  by (auto simp add: ker_def)

section \<open>Quotient Set and Projections\<close>

(*there is no standard terminology for the unique factor mapping - it isn't a lifting,
 but may be referred to a descent; most often it is merely said to be induced
 so why not quotient domain factor and quotient domain codomain factor
*)
definition rel_im::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set"  (infixl \<open>'/\<close> 90)
  where "X/R = (\<Union>x \<in> X. {R``{x}})"  

definition proj :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "proj X R = (\<lambda>x \<in> X. R``{x})"

definition qdf :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a set \<Rightarrow> 'b)"
  where "qdf X Y R f = (THE h. h \<in> set_mor (X/R) Y \<and> f = compose X h (proj X R))"

definition qdcf::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'b set  \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "qdcf X R Y S f = qdf X (Y/S) R (compose X (proj Y S) f)"


definition is_compatible::"('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_compatible R P \<equiv> (\<forall>x. \<forall>y. (x, y) \<in> R \<and> P x \<longrightarrow> P y)"


lemma rel_im_memI1:"x \<in> X \<Longrightarrow> R``{x} \<in> X/R" 
  by(auto simp add:rel_im_def)

lemma rel_im_memI2:"(\<exists>x \<in> X. R``{x} = t) \<Longrightarrow> t \<in> X/R"
  using rel_im_memI1 by fastforce

lemma rel_im_memE1:"\<lbrakk>t\<in>X/R; (\<And>x. \<lbrakk>t = R``{x}; x \<in> X\<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by(auto simp add:rel_im_def)

lemma onto_rel_im:"t\<in>X/R \<Longrightarrow> (\<exists>x \<in> X. t = R``{x})"
  by (simp add: rel_im_def)

lemma proj_apply[simp]: "x \<in> X \<Longrightarrow> proj X R x = R``{x}"
  by (simp add: proj_def)


lemma proj_image: "proj X R ` X = X/R"
  by (simp add: UNION_singleton_eq_range rel_im_def)

lemma proj_set_mor: "proj X R \<in> set_mor X (X/R)"
  by (simp add: proj_def rel_im_memI1)


section \<open>Equivalence Relation Locale\<close>

locale equivalence_relation=
  fixes X::"'a set" and R::"('a \<times> 'a) set"
  assumes is_eqr:"equiv X R"
begin


abbreviation quotient_mapping (\<open>\<pi>\<close>) where "quotient_mapping \<equiv> proj X R"
abbreviation is_eqr_compat where "is_eqr_compat \<equiv> is_compatible R"


lemma closed:"R \<subseteq> X \<times> X"  
  using equiv_def is_eqr by blast 

lemma refl_on:"refl_on X R"
  using equiv_def is_eqr by auto

lemma sym:"sym R"
  using equiv_def is_eqr by blast

lemma trans:"trans R"
  using equiv_def is_eqr by auto

lemma reflexive:"x\<in>X \<Longrightarrow>(x, x)\<in>R"
  using refl_on refl_on_def by fastforce

lemma symmetric[sym]:"(a, b)\<in>R \<Longrightarrow> (b, a)\<in>R"
  using local.sym symE[of R a b] by blast

lemma transitive[trans]: "\<lbrakk>(a, b) \<in> R; (b, c) \<in> R \<rbrakk> \<Longrightarrow> (a, c) \<in> R"
  using local.trans transE[of R a b c] by blast

lemma class_member:"x\<in>X \<Longrightarrow>x\<in>R``{x}"
  using reflexive by auto

lemma class_member_map:"x \<in> X \<Longrightarrow> x \<in> \<pi> x"
  using reflexive by auto

lemma quotient_mapping_memI:"(a,x)\<in>R \<Longrightarrow> x \<in> \<pi> a"
  using closed by auto

lemma class_subset2:"(x,x') \<in> R \<Longrightarrow> R``{x'} \<subseteq> R``{x}"
  using local.transitive by auto

lemma class_eq:"(x,y) \<in> R\<Longrightarrow>R``{x} = R``{y}"
  by (simp add: class_subset2 local.symmetric subset_antisym)

lemma class_elem_in_set:"\<lbrakk>t \<in> X/R; x \<in> t\<rbrakk> \<Longrightarrow> x \<in> X"
proof-
  assume "t \<in> X/R" and A1:"x \<in> t"
  then obtain a where "a \<in> X" and "t = R``{a}"
    using onto_rel_im by blast
  then show "x \<in> X"
    using  A1 closed by auto
qed

lemma subset_equiv_class:"\<lbrakk>R``{y}\<subseteq>R``{x};y\<in>X\<rbrakk> \<Longrightarrow> (x, y) \<in> R"
  using class_member by auto

lemma class_nondisjoint1:"z \<in> (R``{x} \<inter> R``{y}) \<Longrightarrow> (x, y)\<in>R"
  using symmetric transitive by blast

lemma class_nondisjoint2:"R``{x} \<inter> R``{y} \<noteq> {}\<Longrightarrow>(x,y)\<in>R"
  using class_nondisjoint1 by blast


lemma class_eq_iff: "(x, y)\<in>R \<longleftrightarrow> R``{x} = R``{y} \<and> x \<in> X \<and> y \<in> X"
  using class_eq class_member closed by auto

lemma class_eq_iff_map: "(x, y)\<in>R \<longleftrightarrow>\<pi> x = \<pi> y \<and> x \<in> X \<and> y \<in> X"
  using class_eq_iff by auto

lemma is_compatibleI:"(\<And>x y. \<lbrakk>(x,y)\<in>R; P x\<rbrakk> \<Longrightarrow> P y) \<Longrightarrow> (is_eqr_compat P)"
  using is_compatible_def by blast

lemma is_compatibleD:"(is_eqr_compat P) \<Longrightarrow> \<lbrakk>(x,y)\<in>R; P x\<rbrakk> \<Longrightarrow> P y"
  unfolding is_compatible_def by blast


lemma rel_im_obtain2:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  obtains y where "y \<in> X" and "t=R``{y}" and "(y, x) \<in>R"
  using A1 A2 onto_rel_im by force

lemma rel_im_obtain3:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  shows "t = R``{x}"
proof
  show "t \<subseteq> R `` {x}"
  proof-
    obtain y where "y \<in> X" and "t = R``{y}" and "(y,x) \<in> R"
      using A1 A2 rel_im_obtain2 by blast
    then show ?thesis
      by (simp add: class_eq_iff)
  qed
  show "R``{x} \<subseteq> t"
  proof
    fix a assume A3:"a \<in> R``{x}"
    then obtain "(x, a) \<in>R" and "a \<in> X"
      by (simp add: class_eq_iff)
    then show "a \<in> t"
      using A1 A2 class_eq rel_im_obtain2 by force
  qed
qed


lemma rel_im_obtain3_map:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  shows "t =\<pi> x"
  using A1 A2 class_elem_in_set rel_im_obtain3 by auto

lemma class_subset_carrier:
  assumes A1:"t \<in> X/R" 
  shows "t \<subseteq> X"
  using assms class_elem_in_set by auto

lemma union_quotient:"\<Union>(X/R) = X"
proof 
  show "\<Union> (X / R) \<subseteq> X"
    by (simp add: Union_least class_subset_carrier)
  show "X\<subseteq> \<Union> (X / R)"
    using class_member[]  rel_im_memI1[of _ X R] by blast
qed

lemma equiv_nonempty:
  assumes A0:"t \<in> X/R" 
  shows "t \<noteq> {}"
proof-
  obtain x where "x \<in> X" and "t=R``{x}"
    using A0 onto_rel_im by blast
  then have "x \<in> t"
    using class_member by blast
  then show ?thesis
    by blast
qed

lemma relatedE1:"(x,y)\<in>R \<Longrightarrow> (\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t)"
proof-
  assume "(x,y)\<in>R" 
  then obtain "R``{x} \<in> X/R" and "x \<in> R``{x}" and "y \<in> R``{x}"
    by (simp add: class_eq_iff rel_im_memI1)
  then show "\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t"
    by blast
qed

lemma equiv_iff1:"(\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t) \<longleftrightarrow> (x,y) \<in> R" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using rel_im_obtain3 by auto
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: relatedE1)
qed

lemma is_compatibleE1:"\<lbrakk>is_eqr_compat P; t \<in> X/R; (\<exists>x \<in> t. P x)\<rbrakk> \<Longrightarrow> (\<forall>x \<in> t. P x)"
  using equiv_iff1 is_compatibleD by blast


lemma is_compatibleE2:"\<lbrakk>is_eqr_compat P; t \<in> X/R; (\<forall>x \<in> t. P x)\<rbrakk> \<Longrightarrow> (\<exists>x \<in> t. P x)"
  using equiv_nonempty by auto


lemma is_compatible_iff:"\<lbrakk>is_eqr_compat P; t \<in> X/R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> t. P x) \<longleftrightarrow> (\<exists>x \<in> t. P x)"
  using is_compatibleE1 is_compatibleE2 by auto 
  

lemma quotient_non_disjoint_equal:
  assumes A0:"t\<in>X/R" and A1:"s\<in>X/R" and A2:"s \<inter> t \<noteq> {}"
  shows "s=t"
proof-
  obtain z where "z \<in> s \<inter> t"
    using A2 by auto
  then obtain "s = R``{z}" and "t = R``{z}"
    by (simp add: A0 A1 rel_im_obtain3)
  then show ?thesis
    by simp
qed

lemma quotient_equal_or_disjoint:"\<lbrakk>t \<in> X/R; s \<in> X/R\<rbrakk> \<Longrightarrow> s=t \<or> s\<inter>t={}"
  using quotient_non_disjoint_equal by blast

lemma map_surj:"t \<in> X/R\<Longrightarrow>(\<exists>x \<in> X. \<pi> x = t)"
  using onto_rel_im by fastforce

lemma map_set_morphism:"\<pi> \<in> set_mor X (X/R)"
  by (simp add: proj_def rel_im_memI1)

lemma map_surj2:"\<pi>`X = X/R"
  using rel_im_def by fastforce

lemma effective:"ker \<pi> X = R"
  by(auto simp add:ker_def class_eq_iff_map)

lemma ahhh_im_choosing_shit:
  assumes "t \<in> X/R"
  obtains x where "x \<in> X" and "t = \<pi> x"
  using assms onto_rel_im[of t X R] by fastforce

lemma map_memI:"x \<in> X \<Longrightarrow> \<pi> x \<in> X/R"
  by (simp add: rel_im_memI1)

end


section \<open>Hugh\<close>



lemma deez_nuts:
  assumes A0:"f \<in> set_mor X Y" and
          A2:"g`X=Z" and
          A3:"ker g X\<subseteq> ker f X"
  defines "P \<equiv> \<lambda>z y. y \<in> Y \<and> (\<exists>x \<in> X. g x = z \<and> f x = y)"
  defines "h \<equiv> (\<lambda>z \<in> Z. THE y. P z y)"
  shows "h \<in> set_mor Z Y" and
        "f = compose X h g" and
        "\<And>h'. h' \<in> set_mor Z Y \<and> f  = compose X h' g \<Longrightarrow> h = h'" and
        "\<exists>!h \<in> set_mor Z Y. f = compose X h g"
proof-
  have B0:"\<And>z. z \<in> Z \<Longrightarrow> (\<exists>!y. P z y)"
  proof-
    fix z assume A4:"z \<in> Z" 
    obtain y where B0:"y \<in> Y" and B1:"\<exists>x \<in> X. g x = z \<and> f x = y"
      using A0 A2 A4 by blast
    obtain x where B2:"x \<in> X" and B3:"g x= z" and B4:"f x = y"
      using B1 by blast 
    have B5:"\<And>y'. P z y' \<Longrightarrow> y' = y"
    proof-
      fix y' assume "P z y'"
      then obtain A5:"y' \<in> Y" and A7:"(\<exists>x'\<in>X. g x' = z \<and> f x' = y')"
        using P_def by blast
      then obtain x' where B6:"x' \<in> X" and B7:"g x' = z" and B8:"f x' = y'"
        by blast
      then have "g x' = g x"
        by (simp add: B3)
      then have  "(x', x) \<in> ker g X"
        by (simp add: B2 B6 ker_memI1)
      then have "(x', x) \<in> ker f X"
        using A3 by blast
      then show "y' = y"
        by (simp add: B4 B8 ker_equiv1)
    qed
    show "\<exists>!y. P z y"
    proof
      show "P z y"
        using B0 B2 B3 B4 P_def by auto
      show "\<And>y'. P z y' \<Longrightarrow> y' = y"
        using B5 P_def by blast
    qed
  qed
  show P0:"h \<in> set_mor Z Y" 
  proof
    show " \<And>z. z \<in> Z \<Longrightarrow> h z \<in> Y"
    proof-
      fix z assume A6:"z \<in> Z" 
      have B9:"h z= (THE y. P z y)"
        by (simp add: A6 h_def)
      have B10:"(THE y. P z y) \<in> Y"
         using theI'[of "\<lambda>u. P z u"] A6 B0[of z] P_def by blast
      then show "h z \<in> Y"
        by (simp add: B9)
    qed
    show "\<And>z. z \<notin> Z \<Longrightarrow> h z = undefined"
      by (simp add: h_def)
  qed
  show P1:"f = compose X h g" 
  proof
    fix x show "f x = compose X h g x"
    proof(cases "x \<in> X")
      case True
      then have B9:"compose X h g x = h (g x)"
        by (simp add: compose_eq)
      obtain B10:"g x \<in> Z" and B11:"h (g x) = (THE y. P (g x) y)"
        using A2 True h_def by auto
      then have B12:"h (g x) \<in> Y \<and> (\<exists>a \<in> X. g a = (g x) \<and> f a = h (g x))"
        using B0[of "g x"] P_def theI'[of "\<lambda>u. P (g x) u" ] by force
      then obtain a where B13:"a \<in> X" and B14:"g a = g x" and B15:"f a = h (g x)"
        by blast
      then have "(a, x)\<in> ker g X"
        by (simp add: True ker_memI1)
      then have "(a,x)\<in> ker f X"
        using A3 by auto
      then have "f a = f x"
        by (simp add: ker_equiv1)
      then have "f x =h (g x)"
        using B15 by auto
      also have "... = compose X h g x"
        by (simp add: B9)
      finally show ?thesis
        by auto
    next
      case False
      then have "f x= undefined"
        using A0 by blast
      also have "... = compose X h g x"
        by (simp add: False compose_def)
      finally show ?thesis
        by simp 
    qed
  qed
  show P2:"\<And>h'. h' \<in> set_mor Z Y \<and> f  = compose X h' g \<Longrightarrow> h = h'"
  proof-
    fix h' assume A6:"h' \<in>  set_mor Z Y \<and> f = compose X h' g"
    show "h = h'"
    proof
      fix z show "h z = h' z"
      proof(cases "z \<in> Z")
        case True
        then obtain x where "x \<in> X" and "g x = z"
          using A2 by blast
        then show ?thesis 
          using A6 P1 compose_eq[of x X h g] compose_eq[of x X h' g] by auto
      next
        case False
        then obtain "h z = undefined" and "h' z = undefined"
          using A6 extensional_arb[of h' Z z] h_def by auto
        then show ?thesis
          by simp
      qed
    qed
  qed
  show "\<exists>!h \<in> set_mor Z Y. f = compose X h g"
    using P0 P1 P2 by blast
qed

lemma nuts_deez:
  assumes A0:"inj_on g Z" and 
          A1:"g \<in> set_mor Z Y" and
          A2:"f \<in> set_mor X Y" and 
          A3:"f`X \<subseteq> g`Z"
  defines "P \<equiv> (\<lambda>y z. z \<in> Z  \<and> g z = y)"
  defines "h \<equiv> (\<lambda>x \<in> X. THE z. P (f x) z)"
   shows "h \<in> set_mor X Z" and
         "f = compose X g h" and
         "\<And>h'. h' \<in> set_mor X Z \<and> f  = compose X g h' \<Longrightarrow> h = h'"
proof-
  have P0:"\<And>x. x \<in> X \<Longrightarrow> (\<exists>!z. P (f x) z)"
  proof-
    fix x assume A4:"x \<in> X"
    obtain z where B0:"z \<in> Z" and B1:"g z = f x"
      using A3 A4 by auto
    show "(\<exists>!z.  P (f x) z)"
    proof
      show "P (f x) z"
        by (simp add: B0 B1 P_def)
      show "\<And>z'. P (f x) z' \<Longrightarrow> z' = z"
        using A0 B0 B1 inj_onD P_def by fastforce
    qed
  qed
  have P1:"\<And>x. x \<in> X \<Longrightarrow>P (f x)  (h x)"
  proof-
    fix x assume A4:"x \<in> X"
    then have "(\<exists>!z.  P (f x) z)"
      by (simp add: P0)
    then show "P (f x) (h x)"
      using h_def theI'[of "\<lambda>u. P (f x) u"] A4 by auto
  qed
  show P2:"h \<in> set_mor X Z"
    using P1 P_def h_def by force 
  show P3:"f = compose X g h"
  proof
    fix x 
    show "f x = compose X g h x"
    proof(cases "x \<in> X")
      case True
      then show ?thesis 
        using P1[of x] compose_eq[of x X g h] P_def by auto
    next
      case False
      then have "f x= undefined"
        using A2 by blast
      also have "... = compose X g h x"
        by (simp add: False compose_def)
      finally show ?thesis 
        by blast
    qed
  qed
  show "\<And>h'. h' \<in> set_mor X Z \<and> f  = compose X g h' \<Longrightarrow> h = h'"
  proof-
    fix h' assume A6:"h' \<in>  set_mor X Z \<and> f = compose X g h'"
    show "h = h'"
    proof
      fix x 
      show "h x = h' x"
      proof(cases "x \<in> X")
        case True
        obtain B0:"h x \<in> Z" and B1:"h' x \<in> Z"
          using A6 P1 P_def True by blast
        have "g (h' x) = compose X g h' x"
          by (simp add: True compose_eq)
        also have "... = f x"
          by (simp add: A6)
        also have "... = compose X g h x"
          by (simp add: P3)
        also have "... = g (h x)"
          using P1 P3 P_def True by auto
        finally have B2:"g (h' x) = g (h x)"
          by simp
        show ?thesis
          using B2 A0 B0 B1 inj_onD[of g Z "h' x" "h x"] by auto
      next
        case False
        then show ?thesis
          using A6 h_def restrict_ext by auto 
      qed
    qed
  qed
qed

lemma sugma:
  assumes A0:"equivalence_relation X R" and
          A1:"f \<in> set_mor X Y" and
          A2:"ker (equivalence_relation.quotient_mapping X R) X \<subseteq> ker f X"
        shows "\<exists>!h \<in> (set_mor (X/R) Y). f = compose X h (equivalence_relation.quotient_mapping X R)"
proof-
  let ?\<pi>="equivalence_relation.quotient_mapping X R"
  have A3:"?\<pi> ` X = X / R"
    using A0 equivalence_relation.map_surj2 by blast
  show ?thesis
    using A1 A2 A3 deez_nuts(4)[of f X Y ?\<pi> "X/R"] by fastforce
qed

section \<open>Compatible function\<close>

context equivalence_relation
begin

lemma compatI: "(\<And>x y. (x, y) \<in> R \<Longrightarrow> f x = f y) \<Longrightarrow> R \<subseteq> ker f X"
  using closed by (auto intro: ker_memI1)

context
  fixes Y :: "'b set" and f :: "'a \<Rightarrow> 'b"
  assumes f_mor:    "f \<in> set_mor X Y"
      and f_compat: "R \<subseteq> ker f X"
begin

lemma qdf_ex1: "\<exists>!h. h \<in> set_mor (X/R) Y \<and> f = compose X h \<pi>"
  using deez_nuts(4)[OF f_mor map_surj2] f_compat effective by simp

lemma qdf_mor[simp]:"qdf X Y R f \<in> set_mor (X/R) Y"
  using theI'[OF qdf_ex1] by (simp add: qdf_def)

lemma qdf_comp:"f = compose X (qdf X Y R f) \<pi>"
  using theI'[OF qdf_ex1] by (auto simp add: qdf_def)

lemma qdf_proj[simp]:"x \<in> X \<Longrightarrow> qdf X Y R f (\<pi> x) = f x"
  using compose_eq[of x X "qdf X Y R f"  \<pi>] qdf_comp by simp

lemma qdf_uniqueI:"\<lbrakk> h \<in> set_mor (X/R) Y; f = compose X h \<pi>\<rbrakk> \<Longrightarrow> h = qdf X Y R f"
  using qdf_ex1 qdf_mor qdf_comp by blast

lemma qdf_im:"qdf X Y R f ` (X/R) = f ` X"
proof-
  have "qdf X Y R f ` (X/R) = qdf X Y R f ` (\<pi> ` X)"
    using map_surj2 by auto
  also have "... = (\<lambda>x. qdf X Y R f (\<pi> x)) ` X"
    by (simp add: image_image)
  also have "... = f ` X"
    using qdf_proj by auto
  finally show ?thesis .
qed
lemma qdf_ker_iff:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "(\<pi> x, \<pi> y) \<in> ker (qdf X Y R f) (X/R) \<longleftrightarrow> (x, y) \<in> ker f X"
proof-
  have B0:"(\<pi> x, \<pi> y) \<in> ker (qdf X Y R f) (X/R) \<longleftrightarrow> qdf X Y R f (\<pi> x) = qdf X Y R f (\<pi> y)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    show "?lhs \<Longrightarrow> ?rhs"
    proof-
      assume ?lhs then show ?rhs
        using ker_memD2[of "\<pi> x" "\<pi> y"] by blast
    qed
    show "?rhs \<Longrightarrow> ?lhs"
    proof-
      assume ?rhs then show ?lhs
        using A0 A1 ker_memI1[of "\<pi> x" "X/R" "\<pi> y" "qdf X Y R f"] map_memI by blast
    qed
  qed
  also have B1:"... \<longleftrightarrow> f x = f y"
    using A0 A1 qdf_proj by force
  also have B2:"... \<longleftrightarrow> (x, y) \<in> ker f X"
    using A0 A1 ker_mem_iff[of x y X f] by blast
  finally show ?thesis .
qed

end
end


lemma canonical_ligma:
  assumes A0:"f \<in> set_mor X Y"
  defines "R \<equiv> ker f X"
  shows "equiv X R" and
        "qdf X Y R f \<in> set_mor (X/R) Y" and
        "f = compose X (qdf X Y R f) (proj X R)" and
        "inj_on (qdf X Y R f) (X/R)" and
        "(qdf X Y R f)`(X/R) = f ` X" 
proof-
  interpret eqr:equivalence_relation X R
    by (simp add: R_def equivalence_relation.intro ker_is_equivalence)
  let ?h="qdf X Y R f" let ?\<pi>="proj X R"
  show P0:"equiv X R"
    by (simp add: eqr.is_eqr)
  show P1:"?h \<in> set_mor (X/R) Y"
    using A0 R_def eqr.qdf_mor by blast
  show P2:"f = compose X ?h ?\<pi>"
    using A0 R_def eqr.qdf_comp by blast 
  have allesniedergemacht:"R \<subseteq> ker f X"
    by (simp add: R_def)
  show P3:"inj_on ?h (X/R)"
  proof(rule inj_onI)
    fix t s assume t:"t \<in> X/R" and s:"s \<in> X/R" and eq:"?h t = ?h s"
    obtain x where x:"x \<in> X" "t = ?\<pi> x" 
      using t eqr.ahhh_im_choosing_shit by blast
    obtain y where y:"y \<in> X" "s = ?\<pi> y"
      using s eqr.ahhh_im_choosing_shit by blast
    have "f x = f y" 
      using eq x y eqr.qdf_proj[OF A0 allesniedergemacht] by simp
    then have "(x, y) \<in> R" 
      by (simp add: R_def ker_memI1 x(1) y(1))
    then show "t = s"
      by (simp add: eqr.class_eq_iff_map x(2) y(2)) 
  qed
  have "f`X = (compose X ?h ?\<pi>)`X"
    using P2 by fastforce
  also have "... = ?h`(X/R)"
    using eqr.map_surj2 surj_compose[of ?\<pi> X "X/R" ?h "?h`(X/R)"] by auto
  finally show "?h`(X/R) = f ` X"
    by blast 
qed

 
section \<open>Coarsening Relation\<close>
definition coarser_rel_im where
  "coarser_rel_im f R S \<equiv> (\<forall>x x'. (x, x') \<in> R \<longrightarrow> (f x, f x') \<in> S)"

lemma coarser_rel_imI:"(\<And>x y. (x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> S) \<Longrightarrow> coarser_rel_im f R S"
  by (simp add:coarser_rel_im_def)

lemma coarser_rel_imI2:"(map_prod f f)`R \<subseteq> S\<Longrightarrow> coarser_rel_im f R S"
  by (simp add: coarser_rel_im_def in_mono map_prod_imageI)

lemma coarser_rel_imD:"\<lbrakk>coarser_rel_im f R S; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (f x, f y) \<in> S"
  by (simp add: coarser_rel_im_def)

lemma coarser_rel_imE:"\<lbrakk>coarser_rel_im f R S; (\<And>x y. (x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> S) \<Longrightarrow> P\<rbrakk> \<Longrightarrow>P "
  by (simp add: coarser_rel_im_def)


section \<open>Preimage relation\<close>

definition vimage_rel::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('a \<times> 'a) set" where
  "vimage_rel f X S = {(x, x') \<in> X \<times> X. (f x, f x') \<in> S}"

lemma vimage_rel_eq:"(x, y) \<in> vimage_rel f X S \<longleftrightarrow> (x,y)\<in> X \<times> X \<and> (f x, f y) \<in> S"
  by (simp add: vimage_rel_def)

lemma coarser_sub_vimage:
  assumes A0:"R \<subseteq> X \<times> X"
  shows "coarser_rel_im f R S \<longleftrightarrow> R \<subseteq> vimage_rel f X S"
proof
  assume A1:"coarser_rel_im f R S"
  show "R \<subseteq> vimage_rel f X S"
  proof
    fix u assume A2:"u \<in> R"
    then obtain x y where A3:"u = (x, y)" 
      using A0 by blast
    then show "u \<in> vimage_rel f X S"
      using A0 A1 A2 coarser_rel_imD vimage_rel_eq by fastforce
  qed
next
  assume "R \<subseteq> vimage_rel f X S"
  then show "coarser_rel_im f R S"
    by (simp add: coarser_rel_im_def subset_iff vimage_rel_eq)
qed

lemma ein_grosse_gestangk:
  assumes A0:"equivalence_relation Y S" and 
          A1:"f \<in> set_mor X Y"
  shows "vimage_rel f X S = ker (compose X (proj Y S) f) X" (is "?lhs = ?rhs")
proof-  
  let ?h="(compose X (proj Y S) f) " 
  let ?\<pi>="(proj Y S)"
  have "\<And>x y. (x, y) \<in> ?lhs \<longleftrightarrow> (x, y) \<in> ?rhs"
  proof-
    fix x y
    have "(x,y) \<in> ?rhs \<longleftrightarrow> (x,y)\<in> X \<times> X \<and> ?h x =?h y"
      using ker_mem_iff[of x y X ?h] by simp
    also have "... \<longleftrightarrow> (x,y)\<in> X \<times> X \<and> ?\<pi> (f x) =?\<pi> (f y)"
      using compose_eq[of _ X ?\<pi> f] by blast
    also have "... \<longleftrightarrow> (x, y) \<in> X \<times> X \<and> (f x, f y) \<in> S"
      using A0 A1 equivalence_relation.class_eq_iff_map[of Y S "f x" "f y"] by blast
    also have "...\<longleftrightarrow> (x,y) \<in> ?lhs"
      by (simp add: vimage_rel_eq)
    finally show "(x, y) \<in> ?lhs \<longleftrightarrow> (x, y) \<in> ?rhs"
      by blast
  qed
  then show ?thesis
    by auto
qed


lemma coarser_sub_ker:
  assumes A0:"equivalence_relation X R" and 
          A1:"equivalence_relation Y S" and 
          A2:"f \<in> set_mor X Y"
        shows "coarser_rel_im f R S \<longleftrightarrow> R \<subseteq> ker (compose X (proj Y S) f) X"
  using A0 A1 A2 coarser_sub_vimage[of R X f S] ein_grosse_gestangk[of Y S f X] equivalence_relation.closed[of X R] by blast

lemma carl_wheezer:
  assumes A0:"equivalence_relation X R" and
          A1:"equivalence_relation Y S" and
          A2:"f \<in> set_mor X Y" and 
          A3:"coarser_rel_im f R S" 
  shows "qdcf X R Y S f \<in> set_mor (X/R) (Y/S)" 
        "\<And>x. x \<in> X \<Longrightarrow> qdcf X R Y S f (proj X R x) = proj Y S (f x)" and
        "compose X (proj Y S) f = compose X (qdcf X R Y S f) (proj X R)" and
        "\<And>h. \<lbrakk>h \<in> set_mor (X/R) (Y/S); compose X (proj Y S) f = compose X h (proj X R)\<rbrakk> \<Longrightarrow> h = qdcf X R Y S f"
proof-
  let ?p="(proj Y S) "
  let ?f'=" compose X ?p f"
  interpret dom: equivalence_relation X R
    by fact (* by (simp add:A0) lol?*)
  interpret cod: equivalence_relation Y S 
    by fact
  have B0:"?f' \<in> set_mor X (Y/S)"
    using A2 cod.map_set_morphism compose_set_mor[of f X Y ?p "Y/S"] by blast
  have B1:"R \<subseteq> ker ?f' X"
    using A3 coarser_sub_ker[OF A0 A1 A2] by simp
  show P0:"qdcf X R Y S f \<in> set_mor (X/R) (Y/S)"
     using B0 B1 dom.qdf_mor by (simp add: qdcf_def)
   show B2:"\<And>x. x \<in> X \<Longrightarrow> qdcf X R Y S f (proj X R x) = proj Y S (f x)"
    using dom.qdf_proj[OF B0 B1] by (simp add: qdcf_def compose_eq)
  show "?f' = compose X (qdcf X R Y S f) (proj X R)"
     using dom.qdf_comp[OF B0 B1] by (simp add: qdcf_def)
  show "\<And>h. \<lbrakk>h \<in> set_mor (X/R) (Y/S); compose X (proj Y S) f = compose X h (proj X R)\<rbrakk> \<Longrightarrow> h = qdcf X R Y S f"
    using dom.qdf_uniqueI[OF B0 B1] by (simp add: qdcf_def)
qed



lemma vimage_rel_equiv:
  assumes "equivalence_relation Y S" and 
          "f \<in> set_mor X Y"
  shows "equiv X (vimage_rel f X S)"
  by (simp add: ein_grosse_gestangk[OF assms] ker_is_equivalence)



lemma vimage_rel_class:
  assumes "x \<in> X"
  shows "(vimage_rel f X S)``{x} = {x' \<in> X. f x' \<in> S``{f x}}"
  by (auto simp add: assms vimage_rel_def)

lemma vimage_rel_proj:
  assumes A0:"f \<in> set_mor X Y" and 
          A1:"x \<in> X"
  shows "proj X (vimage_rel f X S) x = {x' \<in> X. f x' \<in> proj Y S (f x)}"
proof-
  have fx:"f x \<in> Y"
    using A0 A1 by blast
  have "proj X (vimage_rel f X S) x = (vimage_rel f X S)``{x}"
    by (simp add: A1)
  also have "... = {x' \<in> X. f x' \<in> S``{f x}}"
    by (simp add: A1 vimage_rel_class)
  also have "... = {x' \<in> X. f x' \<in> proj Y S (f x)}"
    by (simp add: fx)
  finally show ?thesis
    .
qed


lemma vimage_rel_quotient:
  assumes A0:"equivalence_relation Y S" and
          A1:"f \<in> set_mor X Y"
  shows "X / vimage_rel f X S = (\<lambda>s. {x \<in> X. f x \<in> s}) ` {s \<in> Y/S. s \<inter> f ` X \<noteq> {}}"
        (is "?lhs = ?rhs")
proof
  let ?R="vimage_rel f X S"
  let ?v="\<lambda>s. {x \<in> X. f x \<in> s}"
  interpret dom:equivalence_relation X ?R
    using A0 A1 equivalence_relation_def vimage_rel_equiv by blast
  interpret cod:equivalence_relation Y S
    by fact
  have key:"\<And>x. x \<in> X \<Longrightarrow> dom.quotient_mapping x = ?v (cod.quotient_mapping (f x))"
  proof-
    fix x assume x:"x \<in> X"
    show "dom.quotient_mapping x = ?v (cod.quotient_mapping (f x))"
      using vimage_rel_proj[OF A1 x] by simp
  qed
  show "?lhs \<subseteq> ?rhs"
  proof
    fix t assume "t \<in> ?lhs"
    then obtain x where x:"x \<in> X" and t:"t = dom.quotient_mapping x"
      using dom.ahhh_im_choosing_shit by blast
    have fx:"f x \<in> Y"
      using A1 x by blast
    have m1:"cod.quotient_mapping (f x) \<in> Y/S"
      using cod.map_memI fx by auto
    have m2:"cod.quotient_mapping (f x) \<inter> f`X \<noteq> {}"
      using fx x cod.class_member_map by blast
    show "t \<in> ?rhs"
      using t key[OF x] m1 m2 by blast
  qed
  show "?rhs \<subseteq> ?lhs"
  proof
    fix t assume "t \<in> ?rhs"
    then obtain s where s:"s \<in> Y/S" and meets:"s \<inter> f`X \<noteq> {}" and t:"t = ?v s"
      by blast
    obtain x where x:"x \<in> X" and fxs:"f x \<in> s"
      using meets by blast
    have "s = cod.quotient_mapping (f x)"
      using s fxs cod.rel_im_obtain3_map by blast
    then have "t = dom.quotient_mapping x"
      by (simp add: t key[OF x])
    then show "t \<in> ?lhs"
      using x dom.map_memI by blast
  qed
qed

section \<open>Quotient of Quotient\<close>

definition qproj::"'a set\<Rightarrow>('a\<times>'a) set \<Rightarrow>('a\<times>'a) set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "qproj X R S = qdf X (X/R) S (proj X R)"

definition rel_quot::"'a set \<Rightarrow> ('a\<times>'a) set\<Rightarrow>('a\<times>'a) set \<Rightarrow> ('a set \<times> 'a set) set " where 
  "rel_quot X R S = ker (qproj X R S) (X/S)"


lemma confirmed_weezy_boosts:
  assumes A0:"equivalence_relation X R" and 
          A1:"equivalence_relation X S" and
          A2:"S \<subseteq> R"
  shows "qproj X R S \<in> set_mor (X/S) (X/R)" and
        "\<And>x. x \<in> X \<Longrightarrow> qproj X R S (proj X S x) = proj X R x" and
        "qproj X R S ` (X/S) = X/R"
proof-
  interpret A3: equivalence_relation X R
    by fact
  interpret A4: equivalence_relation X S 
    by fact
  have B0:"proj X R \<in> set_mor X (X/R)" 
    by (rule A3.map_set_morphism)
  have B1:"S \<subseteq> ker (proj X R) X" 
    by (simp add: A3.effective A2)
  show "qproj X R S \<in> set_mor (X/S) (X/R)"
    using A4.qdf_mor[OF B0 B1] by (simp add: qproj_def)
  show "\<And>x. x \<in> X \<Longrightarrow> qproj X R S (proj X S x) = proj X R x"
    using A4.qdf_proj[OF B0 B1] by (simp add: qproj_def)
  show "qproj X R S ` (X/S) = X/R"
    using A4.qdf_im[OF B0 B1] A3.map_surj2 by (simp add: qproj_def)
qed


lemma second_iso_set:
  assumes A0:"equivalence_relation X R" and
          A1:"equivalence_relation X S" and 
          A2:"S \<subseteq> R"
  defines "h \<equiv> qdf (X/S) (X/R) (rel_quot X R S) (qproj X R S)"
  shows "h \<in> set_mor ((X/S) / rel_quot X R S) (X/R)" and
        "qproj X R S = compose (X/S) h (proj (X/S) (rel_quot X R S))" and
        "bij_betw h ((X/S) / rel_quot X R S) (X/R)"
proof-
  show "h \<in> set_mor ((X/S) / rel_quot X R S) (X/R)"
    by (simp add: A0 A1 A2 canonical_ligma(2) h_def confirmed_weezy_boosts(1) rel_quot_def)
  show "qproj X R S = compose (X/S) h (proj (X/S) (rel_quot X R S))"
    by (simp add: A0 A1 A2 canonical_ligma(3) h_def confirmed_weezy_boosts(1)  rel_quot_def)
  show "bij_betw h ((X/S) / rel_quot X R S) (X/R)"
  proof-
    have B0:"(qproj X R S) `(X / S) =( X /R)"
      by (simp add: A0 A1 A2 confirmed_weezy_boosts(3))
    have B1:"qproj X R S \<in> set_mor (X / S) (X / R)"
      by (simp add: A0 A1 A2 confirmed_weezy_boosts(1))
    have B2:"inj_on h ((X/S) / rel_quot X R S)"
      using B1 canonical_ligma(4)[of "qproj X R S" "(X / S)" "(X/R)"] h_def rel_quot_def[of X R S] by simp
    then show ?thesis
      by (simp add: B0 B1 bij_betw_def canonical_ligma(5) h_def rel_quot_def)
  qed
qed

lemma rel_quot_mem_iff:
  assumes A0:"equivalence_relation X R" and
          A1:"equivalence_relation X S" and
          A2:"S \<subseteq> R" and
          x:"x \<in> X" and y:"y \<in> X"
  shows "(proj X S x, proj X S y) \<in> rel_quot X R S \<longleftrightarrow> (x, y) \<in> R"
proof-
  interpret dom: equivalence_relation X R by fact
  interpret sub: equivalence_relation X S by fact
  have B0:"proj X R \<in> set_mor X (X/R)"
    by (rule dom.map_set_morphism)
  have B1:"S \<subseteq> ker (proj X R) X"
    by (simp add: dom.effective A2)
  show ?thesis
    using sub.qdf_ker_iff[OF B0 B1 x y]
    by (simp add: rel_quot_def qproj_def dom.effective)
qed

lemma rel_quot_eq:
  assumes A0:"equivalence_relation X R" and
          A1:"equivalence_relation X S" and
          A2:"S \<subseteq> R"
  shows "rel_quot X R S = map_prod (proj X S) (proj X S) ` R"
proof
  interpret dom: equivalence_relation X R by fact
  interpret sub: equivalence_relation X S by fact
  show "rel_quot X R S \<subseteq> map_prod (proj X S) (proj X S) ` R"
  proof
    fix u assume A3:"u \<in>  rel_quot X R S"
    then obtain s t where B0:"s \<in> X/S" and B1:"t \<in> X/S" and A4:"u = (s,t)" and B2:"qproj X R S s = qproj X R S t"
       unfolding rel_quot_def ker_def by auto
    obtain a where B3:"a \<in> X" and B4:"s = proj X S a"
      using B0 sub.ahhh_im_choosing_shit by blast
    obtain b where B5:"b \<in> X" and B6:"t = proj X S b"
      using B1 sub.ahhh_im_choosing_shit by blast
    then have B7:"(a, b) \<in> R"
      using A0 A1 A2 A3 A4 B3 B4 rel_quot_mem_iff[of X R S a b] by blast
    then show "u \<in> map_prod (proj X S) (proj X S) ` R"
      using A4 B4 B6 by blast
  qed
  show "map_prod (proj X S) (proj X S) ` R \<subseteq> rel_quot X R S"
  proof
    fix u assume A3:"u \<in> map_prod (proj X S) (proj X S) ` R"
    then obtain a b where B0:"(a, b) \<in> R" and B1:"u = (proj X S a, proj X S b)"
      by auto
    obtain B2:"a \<in> X" and B3:"b \<in> X"
      using B0 dom.class_eq_iff_map by blast
    show "u \<in> rel_quot X R S"
      using A0 A1 A2 B0 B1 B2 B3 rel_quot_mem_iff[of X R S a b] by blast
  qed
qed



section \<open>Product of Quotients\<close>
definition prod_rel::"'a set \<Rightarrow> ('a rel) \<Rightarrow> 'b set \<Rightarrow> 'b rel \<Rightarrow> (('a \<times> 'b) \<times>  ('a  \<times> 'b )) set" where
  "prod_rel X1 R1 X2 R2 \<equiv> ker (map_prod (proj X1 R1) (proj X2 R2)) (X1 \<times> X2)"


lemma prod_rel_is_equiv:"equiv (X1 \<times> X2) (prod_rel X1 R1 X2 R2)"
  by (simp add: ker_is_equivalence prod_rel_def)

lemma prod_rel_mem_iff:
  assumes A0:"equivalence_relation X1 R1" and
          A1:"equivalence_relation X2 R2"
  shows "((x1, x2), (y1, y2)) \<in> prod_rel X1 R1 X2 R2 \<longleftrightarrow> (x1, y1) \<in> R1 \<and> (x2, y2) \<in> R2" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  interpret eqr1:equivalence_relation X1 R1
    by fact
  interpret eqr2:equivalence_relation X2 R2
    by fact
  have "?lhs \<Longrightarrow> ?rhs"
  proof-
    assume ?lhs
    then obtain 
        B0:"x1 \<in> X1" and B1:"x2 \<in> X2" and B2:"y1 \<in> X1" and B3:"y2 \<in> X2" and
        B4:"map_prod (proj X1 R1) (proj X2 R2) (x1, x2) = map_prod (proj X1 R1) (proj X2 R2) (y1, y2)" 
      by(auto simp add:prod_rel_def ker_def)
    then obtain "(proj X1 R1) x1 =( proj X1 R1) y1" and  "(proj X2 R2) x2 =( proj X2 R2) y2"
      by auto
    then show ?rhs
      by (simp add: B0 B1 B2 B3 eqr1.class_eq_iff_map eqr2.class_eq_iff_map)
  qed
  also have "?rhs \<Longrightarrow> ?lhs" 
    by (simp add: eqr1.class_eq_iff_map eqr2.class_eq_iff_map ker_memI1 prod_rel_def)
  then show ?thesis
    using calculation by blast
qed

lemma prod_proj_set_mor:  
  "restrict (map_prod (proj X1 R1) (proj X2 R2)) (X1 \<times> X2)  \<in> set_mor (X1 \<times> X2) ((X1/R1) \<times> (X2/R2))"
  by (simp add: PiE_iff rel_im_memI1)

lemma prod_proj_image:
  "(restrict (map_prod (proj X1 R1) (proj X2 R2)) (X1 \<times> X2)) ` (X1 \<times> X2)  = (X1/R1) \<times> (X2/R2)"
  using map_prod_surj_on[of "proj X1 R1" X1 "X1/R1" "proj X2 R2" X2 "X2/R2"] 
        proj_image[of X1 R1] proj_image[of X2 R2] 
        image_restrict_eq[of "map_prod (proj X1 R1) (proj X2 R2)" "(X1 \<times> X2)"] by auto


definition is_compat_map where "is_compat_map R f \<equiv> (\<forall>x y. (x, y) \<in> R \<longrightarrow> f x = f y)"

lemma is_compat_mapI:"(\<And>x y. (x, y) \<in> R \<Longrightarrow> f x = f y) \<Longrightarrow> is_compat_map R f"
  by(simp add:is_compat_map_def)

lemma is_compat_mapD:"is_compat_map R f \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> f x = f y"
  by(simp add:is_compat_map_def)


lemma coarser_rel_im_restrict:
  "R \<subseteq> A \<times> A \<Longrightarrow> coarser_rel_im (restrict f A) R S \<longleftrightarrow> coarser_rel_im f R S"
  by (fastforce simp add: coarser_rel_im_def)

locale magma=
  fixes X::"'a set" and law::"'a \<times> 'a \<Rightarrow> 'a" 
  assumes op_closed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> law (x, y) \<in> X"
begin

end

locale magma_congruence=base_magma:magma X law+base_equivalence:equivalence_relation X R for X and law and R+
  assumes compatible:"coarser_rel_im law (prod_rel X R X R) R"
begin
abbreviation R2 where "R2 \<equiv> prod_rel X R X R"
abbreviation X2 where "X2 \<equiv> X \<times> X"
abbreviation XR2 where "XR2 \<equiv> (X/R) \<times> (X/R)"
abbreviation Q where "Q \<equiv> X/R"
abbreviation raw where "raw \<equiv> (restrict law X2)"
abbreviation \<pi>2 where "\<pi>2 \<equiv> map_prod \<pi> \<pi>"
abbreviation f where "f \<equiv>  compose X2 \<pi> raw"
abbreviation p2 where "p2 \<equiv> restrict \<pi>2 X2"

lemma equiv1:"equivalence_relation X R"
  by (simp add: base_equivalence.equivalence_relation_axioms)

lemma equiv2:"equivalence_relation X2 R2"
  by (simp add: equivalence_relation.intro prod_rel_is_equiv)

lemma restricted_law_mor:"raw \<in> set_mor X2 X"
  using base_magma.op_closed by auto

lemma proj_restricted_law_mor:"f \<in> set_mor X2 Q"
  using  proj_set_mor[of X R] restricted_law_mor compose_set_mor[of raw X2 X \<pi> "Q"] by blast


lemma compat_ker:"R2 \<subseteq> ker f X2"
proof-
  have "coarser_rel_im raw R2 R"
    by (simp add: coarser_rel_im_restrict compatible equiv2 equivalence_relation.closed)
  then show ?thesis
    using coarser_sub_ker[of X2 R2 X R "raw"] equiv1 equiv2 restricted_law_mor by blast
qed

definition quotient_law where 
  "quotient_law = (THE h. h \<in> set_mor (XR2) Q \<and> f = compose  X2  h p2)"

lemma qlaw_ex1:
  "\<exists>!h. h \<in> set_mor XR2 Q \<and> compose X2 \<pi> raw = compose  X2  h p2"
proof(rule deez_nuts(4)[of "f" X2 "Q" "p2" "XR2"])
  show "compose X2 \<pi> raw \<in> set_mor X2 Q"
    using proj_restricted_law_mor by blast
  show "p2 ` X2 = XR2"
    using prod_proj_image[of X R X R] by blast
  show "ker p2 X2 \<subseteq> ker (compose X2 \<pi> raw) X2"
    using compat_ker ker_restrict prod_rel_def by blast
qed
  

lemma qlaw_mor[simp]:"quotient_law \<in> set_mor XR2 Q"
  using theI'[OF qlaw_ex1] by (simp add: quotient_law_def)

lemma qlaw_comp:"f = compose  X2  quotient_law p2"
  using theI'[OF qlaw_ex1] by (simp add: quotient_law_def)

lemma qlaw_uniqueI:"\<lbrakk>h \<in> set_mor XR2 Q; f = compose X2 h p2\<rbrakk> \<Longrightarrow> h = quotient_law"
  using qlaw_ex1 qlaw_mor qlaw_comp by blast

lemma qlaw_proj[simp]:"u \<in> X2 \<Longrightarrow> quotient_law (p2 u) = f u"
  using compose_eq[of u X2 "quotient_law"  p2] qlaw_comp by simp

lemma qlaw_apply:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> quotient_law (\<pi> x, \<pi> y) = \<pi> (raw (x, y))"
proof-
  fix x y assume A0:"x \<in> X" and A1:"y \<in> X"
  then obtain B0:"(x,y) \<in> X2" and B1:"(\<pi> x, \<pi> y) \<in> XR2"
    using base_equivalence.map_memI by blast
  have B2:"quotient_law (\<pi> x, \<pi> y) = quotient_law (p2 (x, y))"
    using B0 by force
  also have B3:" ... =compose X2 quotient_law p2 (x, y)"
    using compose_eq[of "(x,y)" X2 quotient_law p2] B0 by blast
  also have B4:"... =  compose X2 \<pi> raw (x,y) "
    using qlaw_comp by presburger
  also have B5:"... = \<pi> (raw (x,y))"
    using B0 compose_eq[of "(x,y)" X2 \<pi> raw] by blast
  finally show "quotient_law (\<pi> x, \<pi> y) = \<pi> (raw (x, y))"
    by blast
qed


end




context magma_congruence
begin

lemma quotient_law_apply:
  assumes "x \<in> X" "y \<in> X" shows "quotient_law (\<pi> x, \<pi> y) = \<pi> (law (x, y))"
  using qlaw_apply[OF assms] assms by simp

lemma quotient_magma: "magma Q quotient_law"
proof (unfold_locales)
  fix t s assume "t \<in> Q" "s \<in> Q"
  then obtain x y where x: "x \<in> X" "t = \<pi> x" and y: "y \<in> X" "s = \<pi> y"
    by (elim base_equivalence.ahhh_im_choosing_shit)
  have lx: "law (x, y) \<in> X" by (rule base_magma.op_closed[OF x(1) y(1)])
  have eq: "quotient_law (t, s) = \<pi> (law (x, y))"
    unfolding x(2) y(2) by (rule quotient_law_apply[OF x(1) y(1)])
  show "quotient_law (t, s) \<in> Q" unfolding eq by (rule base_equivalence.map_memI[OF lx])
qed

sublocale quotient: magma Q quotient_law
  by (rule quotient_magma)

end


section \<open>Homomorphisms\<close>

locale magma_hom = dom: magma X lawX + cod: magma Y lawY
  for X :: "'a set" and lawX :: "'a \<times> 'a \<Rightarrow> 'a" and Y :: "'b set" and lawY :: "'b \<times> 'b \<Rightarrow> 'b" +
  fixes f :: "'a \<Rightarrow> 'b"
  assumes f_mor: "f \<in> set_mor X Y"
    and f_hom: "\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (lawX (x, y)) = lawY (f x, f y)"
begin

lemma f_maps: "x \<in> X \<Longrightarrow> f x \<in> Y"
  using f_mor by blast

lemma image_magma: "magma (f ` X) lawY"
proof (unfold_locales)
  fix a b assume "a \<in> f ` X" "b \<in> f ` X"
  then obtain x y where "x \<in> X" "y \<in> X" "a = f x" "b = f y" by blast
  then show "lawY (a, b) \<in> f ` X" by (simp add: f_hom[symmetric] dom.op_closed)
qed


lemma kernel_congruence: "magma_congruence X lawX (ker f X)"
proof (rule magma_congruence.intro)
  show "magma X lawX" by (rule dom.magma_axioms)
  show eqr: "equivalence_relation X (ker f X)"
    by (simp add: equivalence_relation.intro ker_is_equivalence)
  show "magma_congruence_axioms X lawX (ker f X)"
  proof (rule magma_congruence_axioms.intro, rule coarser_rel_imI)
    fix u v assume uv: "(u, v) \<in> prod_rel X (ker f X) X (ker f X)"
    obtain x1 x2 y1 y2 where u: "u = (x1, x2)" and v: "v = (y1, y2)" by (cases u, cases v)
    have "(x1, y1) \<in> ker f X \<and> (x2, y2) \<in> ker f X"
      using uv unfolding u v by (simp add: prod_rel_mem_iff[OF eqr eqr])
    then have X: "x1 \<in> X" "x2 \<in> X" "y1 \<in> X" "y2 \<in> X" and eq: "f x1 = f y1" "f x2 = f y2"
      by (auto simp: ker_def)
    show "(lawX u, lawX v) \<in> ker f X"
      unfolding u v by (rule ker_memI1[OF dom.op_closed dom.op_closed]) (simp_all add: X eq f_hom)
  qed
qed

end




context magma_hom
begin

interpretation ker: magma_congruence X lawX "ker f X"
  by (rule kernel_congruence)



abbreviation pr where "pr \<equiv> proj X (ker f X)"

abbreviation induced where "induced \<equiv> qdf X Y (ker f X) f"

lemma induced_proj: assumes "x \<in> X" shows "induced (pr x) = f x"
proof -
  have "f x = compose X induced pr x" by (rule fun_cong[OF canonical_ligma(3)[OF f_mor]])
  then show ?thesis using assms by (simp add: compose_eq)
qed

lemma induced_mor: "induced \<in> set_mor (X / ker f X) Y"
  and induced_inj: "inj_on induced (X / ker f X)"
  and induced_image: "induced ` (X / ker f X) = f ` X"
  by (rule canonical_ligma[OF f_mor])+

lemma induced_mor_image: "induced \<in> set_mor (X / ker f X) (f ` X)"
proof -
  have "induced \<in> extensional (X / ker f X)" using induced_mor by (simp add: PiE_iff)
  moreover have "induced \<in> Pi (X / ker f X) (\<lambda>_. f ` X)" using induced_image by blast
  ultimately show ?thesis by (simp add: PiE_def)
qed

theorem first_isomorphism_magmas:
  "magma_hom (X / ker f X) ker.quotient_law (f ` X) lawY induced"
  "bij_betw induced (X / ker f X) (f ` X)"
proof -
  show "bij_betw induced (X / ker f X) (f ` X)"
    using induced_inj induced_image by (simp add: bij_betw_def)
  show "magma_hom (X / ker f X) ker.quotient_law (f ` X) lawY induced"
  proof (rule magma_hom.intro[OF ker.quotient_magma image_magma], unfold_locales)
    show "induced \<in> set_mor (X / ker f X) (f ` X)" by (rule induced_mor_image)
    fix t s assume "t \<in> X / ker f X" "s \<in> X / ker f X"
    then obtain x y where x: "x \<in> X" "t = pr x" and y: "y \<in> X" "s = pr y"
      by (elim ker.base_equivalence.ahhh_im_choosing_shit)
    have "induced (ker.quotient_law (t, s)) = induced (pr (lawX (x, y)))"
      unfolding x(2) y(2) ker.quotient_law_apply[OF x(1) y(1)] ..
    also have "\<dots> = f (lawX (x, y))" by (rule induced_proj[OF dom.op_closed[OF x(1) y(1)]])
    also have "\<dots> = lawY (induced t, induced s)"
      unfolding x(2) y(2) by (simp only: f_hom[OF x(1) y(1)] induced_proj[OF x(1)] induced_proj[OF y(1)])
    finally show "induced (ker.quotient_law (t, s)) = lawY (induced t, induced s)" .
  qed
qed

end


end