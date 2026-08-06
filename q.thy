theory q
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

lemma reflexive:"x\<in>X \<Longrightarrow>(x, x)\<in>R"
  by (meson equivE is_eqr refl_onD)

lemma class_member:"x\<in>X \<Longrightarrow>x\<in>R``{x}"
  using reflexive by auto

lemma class_member_map:"x \<in> X \<Longrightarrow> x \<in> \<pi> x"
  using reflexive by auto

lemma quotient_mapping_memE:"\<lbrakk>a \<in> X; x \<in> \<pi> a\<rbrakk> \<Longrightarrow>(a, x) \<in> R"
  by (simp)

lemma quotient_mapping_memI:"(a,x)\<in>R \<Longrightarrow> x \<in> \<pi> a"
  using closed by auto


lemma symmetric[sym]:"(a, b)\<in>R \<Longrightarrow> (b, a)\<in>R"
  by (meson equiv_def is_eqr symE)

lemma sym:"sym R"
  using equiv_def is_eqr by auto

lemma transitive[trans]: "\<lbrakk>(a, b) \<in> R; (b, c) \<in> R \<rbrakk> \<Longrightarrow> (a, c) \<in> R"
  by (meson equivE is_eqr transE)


lemma transitive_mapping:
  assumes A0:"a \<in> X" and  A1:"b \<in> \<pi> a" and A2:"c \<in> \<pi> b" 
  shows "c \<in> \<pi> a"
proof-
  obtain "(a, b)\<in>R" and "b \<in> X"
    using A0 A1 closed by auto
  then show ?thesis
    using A2 local.transitive quotient_mapping_memE quotient_mapping_memI by blast
qed
  


lemma trans:"trans R"
  using equiv_def is_eqr by auto

lemma trans1:"\<lbrakk>(x,y)\<in>R;z \<in> R``{y}\<rbrakk> \<Longrightarrow> (x,z)\<in>R"
  using trans transitive[of x y z] by simp

lemma trans1_mapping:"\<lbrakk>(x,y)\<in>R;z \<in> \<pi> y\<rbrakk> \<Longrightarrow> (x,z)\<in>R"
proof-
  assume A0:"(x,y)\<in>R" and A1:"z \<in> \<pi> y"
  then obtain "y \<in> X" and "(y, z)\<in>R"
    using closed quotient_mapping_memE by auto
  then show "(x,z)\<in>R"
    using A0 local.transitive by blast
qed

lemma class_subset:"\<lbrakk>(x,y) \<in> R; z \<in> R``{y}\<rbrakk> \<Longrightarrow> z \<in> R``{x}"
  using trans trans1[of x y z] by simp

lemma mapping_subset:"\<lbrakk>(x,y)\<in>R; z \<in>\<pi> y\<rbrakk> \<Longrightarrow> z \<in> \<pi> x"
  using quotient_mapping_memI trans1_mapping by blast

lemma class_subset2:"(x,x') \<in> R \<Longrightarrow> R``{x'} \<subseteq> R``{x}"
  using class_subset by blast

lemma mapping_subset2:"(x,y)\<in>R \<Longrightarrow> \<pi> y \<subseteq> \<pi> x"
  by (simp add: mapping_subset subsetI)

lemma class_eq:"(x,y) \<in> R\<Longrightarrow>R``{x} = R``{y}"
  by (simp add: class_subset2 local.symmetric subset_antisym)

lemma class_eq_map:"(x,y)\<in>R \<Longrightarrow> \<pi> x = \<pi> y"
  using local.symmetric mapping_subset2 by blast

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

lemma mapping_equiv_class:"\<lbrakk>\<pi> y \<subseteq>\<pi> x ;y\<in>X; x \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R"
  using local.subset_equiv_class by auto


lemma eq_class: "\<lbrakk>R``{x} = R``{y};y\<in>X\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  using class_member by auto

lemma eq_class_mapping: "\<lbrakk>\<pi> x = \<pi> y;y\<in>X; x \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  using class_member_map by auto

lemma class_nondisjoint1:"z \<in> (R``{x} \<inter> R``{y}) \<Longrightarrow> (x, y)\<in>R"
  using symmetric transitive by blast

lemma class_nondisjoint2:"R``{x} \<inter> R``{y} \<noteq> {}\<Longrightarrow>(x,y)\<in>R"
  using class_nondisjoint1 by blast

lemma class_nondisjoint1_mapping:"\<lbrakk>x \<in> X; y \<in> X; z \<in> (\<pi> x \<inter> \<pi> y)\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  using class_nondisjoint2 by auto
 

lemma class_nondisjoint2_mapping:"\<lbrakk>x \<in> X; y \<in> X; \<pi> x \<inter> \<pi> y \<noteq> {}\<rbrakk>\<Longrightarrow>(x,y)\<in>R"
  by (simp add: class_nondisjoint2)


lemma class_eq_iff: "(x, y)\<in>R \<longleftrightarrow> R``{x} = R``{y} \<and> x \<in> X \<and> y \<in> X"
  using class_eq class_member closed by auto

lemma eq_class_iff: "\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> R``{x} = R``{y} \<longleftrightarrow> (x, y) \<in> R"
  using class_eq class_member by auto


lemma class_eq_iff_map: "(x, y)\<in>R \<longleftrightarrow>\<pi> x = \<pi> y \<and> x \<in> X \<and> y \<in> X"
  by (meson class_eq_iff class_eq_map eq_class_mapping)

lemma eq_class_iff_map: "\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> \<pi> x = \<pi> y \<longleftrightarrow> (x, y) \<in> R"
  using class_eq_iff_map by presburger


lemma is_compatibleI:"(\<And>x y. \<lbrakk>(x,y)\<in>R; P x\<rbrakk> \<Longrightarrow> P y) \<Longrightarrow> (is_eqr_compat P)"
  using is_compatible_def by blast

lemma is_compatibleD:"(is_eqr_compat P) \<Longrightarrow> \<lbrakk>(x,y)\<in>R; P x\<rbrakk> \<Longrightarrow> P y"
  unfolding is_compatible_def by blast

lemma class_image_subset:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t" and A3:"y \<in> t"
  shows "y \<in> R``{x}"
proof-
  obtain A4:"x \<in> X" and A5:"y \<in> X" 
    using A1 A2 A3 class_elem_in_set by blast
  obtain z where A6:"z \<in> X" and A7:"t = R``{z}"
    using A1 onto_rel_im by blast
  then obtain "(z,x)\<in>R" and "(z,y)\<in>R"
    using A2 A3 by auto
  then obtain "(x, y)\<in>R"
    using class_eq_iff by blast
  then show ?thesis
    by force
qed

lemma class_image_subset_map:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t" and A3:"y \<in> t"
  shows "y \<in> \<pi> x"
  using A1 A2 A3 class_elem_in_set class_image_subset by auto

lemma rel_im_obtain2:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  obtains y where "y \<in> X" and "t=R``{y}" and "(y, x) \<in>R"
  using A1 A2 onto_rel_im by force

lemma rel_im_obtain2_map:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  obtains y where "y \<in> X" and "t=\<pi> y" and "(y, x) \<in>R"
  using A1 A2 rel_im_obtain2 by auto

lemma class_member_subsetself:"\<lbrakk>t \<in> X/R; x \<in> t\<rbrakk> \<Longrightarrow> t \<subseteq> R``{x}"
  using class_image_subset by auto

lemma class_member_subsetself_map:"\<lbrakk>t \<in> X/R; x \<in> t\<rbrakk> \<Longrightarrow> t \<subseteq>\<pi> x"
  by (simp add: class_image_subset_map subset_iff)

lemma equiv_un:
  assumes A0:"t \<in> X/R"
  shows  "t = (\<Union>y \<in> t. R``{y})" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using A0 class_member_subsetself by auto
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume A1:"x \<in> ?rhs"
    then obtain y where B0:"y \<in> t" and B1:"x \<in> R``{y}"
      by blast
    obtain B2:"y \<in> X" and B3:"x \<in> X"
      using B1 class_eq_iff by auto
    obtain a where B4:"a \<in> X" and B5:"t = R``{a}"
      using assms onto_rel_im by blast
    have B4:"t = R``{y}"
      using B0 B5 class_eq_iff by auto
    then show "x \<in> ?lhs"
      using B1 by blast
  qed
qed


lemma equiv_un_map:
  assumes A0:"t \<in> X/R"
  shows  "t = (\<Union>y \<in> t. \<pi> y)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using assms class_elem_in_set class_member_map by auto
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume A1:"x \<in> ?rhs"
    then obtain y where B0:"y \<in> t" and B1:"x \<in> \<pi> y"
      by blast
    obtain B2:"y \<in> X" and B3:"x \<in> X"
      using B0 B1 assms class_elem_in_set class_eq_iff quotient_mapping_memE by blast
    obtain a where B4:"a \<in> X" and B5:"t =\<pi> a"
      by (meson B0 assms rel_im_obtain2_map)
    have B4:"t = \<pi> y"
      using B0 B4 B5 class_eq_map quotient_mapping_memE by blast
    then show "x \<in> ?lhs"
      using B1 by blast
  qed
qed

lemma rel_im_obtain3:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  shows "t = R``{x}"
proof
  show "t \<subseteq> R `` {x}"
    by (simp add: A1 A2 class_member_subsetself)
  show "R``{x} \<subseteq> t"
  proof
    fix a assume A3:"a \<in> R``{x}"
    then obtain "(x, a) \<in>R" and "a \<in> X"
      by (simp add: class_eq_iff)
    then show "a \<in> t"
      using A1 A2 equivalence_relation.equiv_un[of X R t] equivalence_relation_axioms by blast
  qed
qed


lemma rel_im_obtain3_map:
  assumes  A1:"t \<in> X/R" and A2:"x \<in> t"
  shows "t =\<pi> x"
  using A1 A2 class_elem_in_set rel_im_obtain3 by auto

lemma rel_im_memE1:
  assumes A1:"t \<in> X/R" and A2:"x \<in> t"
  shows "x \<in> X"
  using A1 A2 class_elem_in_set by auto

lemma rel_im_union:
  assumes A1:"t \<in> X/R" 
  shows "t \<subseteq> X"
  using A1 rel_im_memE1 by fastforce

lemma union_quotient:"\<Union>(X/R) = X"
  using is_eqr unfolding equiv_def refl_on_def rel_im_def by blast

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

lemma relatedI1:"(\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t) \<Longrightarrow> (x,y) \<in> R"
  using rel_im_obtain3 by blast

lemma relatedI2:"\<lbrakk>t \<in> X/R; x \<in> t; y \<in> t\<rbrakk> \<Longrightarrow> (x,y) \<in> R"
  using relatedI1 by blast

lemma relatedE1:"(x,y)\<in>R \<Longrightarrow> (\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t)"
proof-
  assume "(x,y)\<in>R" 
  then obtain "R``{x} \<in> X/R" and "x \<in> R``{x}" and "y \<in> R``{x}"
    by (simp add: class_eq_iff rel_im_memI1)
  then show "\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t"
    by blast
qed

lemma equiv_iff1:"(\<exists>t \<in> X/R. x \<in> t \<and> y \<in> t) \<longleftrightarrow> (x,y) \<in> R"
  using relatedE1 relatedI1 by blast


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
  obtain x y where B0:"x \<in> X" and B1:"t = R``{x}" and B2:"y \<in> X" and B3:"s = R``{y}"
    using A0 A1 onto_rel_im[of t X R] onto_rel_im[of s X R] by blast
  obtain z where "z \<in> R``{x} \<inter> R``{y}"
    using A2 B1 B3 by blast
  then show ?thesis
    by (simp add: B1 B3 class_eq_iff)
qed

lemma quotient_equal_or_disjoint:"\<lbrakk>t \<in> X/R; s \<in> X/R\<rbrakk> \<Longrightarrow> s=t \<or> s\<inter>t={}"
  using quotient_non_disjoint_equal by blast

lemma class_mem_rel_eqI:"\<lbrakk>t \<in>X/R; s \<in> X/R; x \<in> t; y \<in> s; (x,y)\<in>R\<rbrakk> \<Longrightarrow> s = t"
  using rel_im_obtain3 by auto

lemma class_mem_rel_eqE:"\<lbrakk>t \<in>X/R; s \<in> X/R; x \<in> t; y \<in> s; s=t\<rbrakk> \<Longrightarrow> (x,y)\<in>R"
  using rel_im_obtain3 by auto


lemma map_surj:"t \<in> X/R\<Longrightarrow>(\<exists>x \<in> X. \<pi> x = t)"
  using onto_rel_im by fastforce

lemma map_set_morphism:"\<pi> \<in> set_mor X (X/R)"
  by (simp add: q.proj_def rel_im_memI1)

lemma map_surj2:"\<pi>`X = X/R"
  using rel_im_def by fastforce

lemma effective:"ker \<pi> X = R"
  by (auto simp add: ker_def class_eq_iff_map)

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

definition vimage_rel::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('a \<times> 'a) set" where
  "vimage_rel f X S = {(x, x') \<in> X \<times> X. (f x, f x') \<in> S}"

lemma vimage_rel_eq:"(x, y) \<in> vimage_rel f X S \<longleftrightarrow> (x,y)\<in> X \<times> X \<and> (f x, f y) \<in> S"
  by (simp add: vimage_rel_def)

lemma vimage_relationI:"\<lbrakk>(x, y) \<in> X \<times> X; (f x, f y) \<in> S\<rbrakk> \<Longrightarrow> (x, y) \<in> vimage_rel f X S"
  by (simp add: vimage_rel_def)

lemma vimage_relationD1:"(x, y) \<in> vimage_rel f X S \<Longrightarrow> (x, y) \<in> X \<times> X"
  by (simp add: vimage_rel_def)

lemma vimage_relationD2:"(x, y) \<in> vimage_rel f X S \<Longrightarrow>(f x, f y) \<in> S "
  by (simp add: vimage_rel_def)

lemma vimage_relE:"(a,b)\<in>vimage_rel f X S \<Longrightarrow> (\<lbrakk>(a,b)\<in> X \<times> X; (f a, f b) \<in> S\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
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

print_options

lemma vimage_rel_class:
  assumes A0:"equivalence_relation Y S" and A1:"f \<in> set_mor X Y" and A2:"x \<in> X"
  shows "(vimage_rel f X S)``{x} = {x' \<in> X. f x' \<in> S``{f x}}"
  by(auto simp add:A2 vimage_rel_def)

lemma vimage_rel_class2:
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
    by (simp add: A1 vimage_rel_class2)
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

end