theory Algebrah4
  imports Main
begin

declare [[show_consts, show_results, show_types]]
declare [[show_abbrevs=true]]

hide_const map
hide_const partition
hide_const monoid
hide_const group
hide_const inverse
no_notation power (infixr "^" 80)
hide_const power
no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)


definition Pi :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set" where "Pi A B = {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B x}"
definition maps_to::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  where "maps_to A B \<equiv> {f. (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)}"
definition maps_on::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) set" where "maps_on A \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined)}"
definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b" where "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"
syntax "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
translations "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"
definition compose::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where "compose A g f = (\<lambda>x\<in>A. g (f x))"

lemma Pi_I[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> f \<in> Pi A B"  by (simp add: Pi_def)
lemma Pi_I'[simp]: "(\<And>x. x \<in> A \<longrightarrow> f x \<in> B x) \<Longrightarrow> f \<in> Pi A B"  by (simp add:Pi_def)
lemma Pi_mem: "f \<in> Pi A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B x" by (simp add: Pi_def)
lemma Pi_iff: "f \<in> Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i)"  unfolding Pi_def by auto
lemma PiE[elim]: "f \<in> Pi A B \<Longrightarrow> (f x \<in> B x \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"  by (auto simp: Pi_def)
lemma Pi_cong: "(\<And>w. w \<in> A \<Longrightarrow> f w = g w) \<Longrightarrow> f \<in> Pi A B \<longleftrightarrow> g \<in> Pi A B"  by (auto simp: Pi_def)
lemma Pi_empty [simp]: "Pi {} B = UNIV"  by (simp add: Pi_def)
lemma Pi_Int: "Pi I E \<inter> Pi I F = (Pi I (\<lambda>i. E i \<inter> F i))"  by auto
lemma Pi_split_domain[simp]: "f \<in> Pi (A \<union> B) X \<longleftrightarrow> f \<in> Pi A X \<and> f \<in> Pi B X" by (auto simp: Pi_def)
lemma Pi_split_insert_domain[simp]: "f \<in> Pi (insert a A) B \<longleftrightarrow>f \<in> Pi A B \<and> f a \<in> B a"  by (auto simp: Pi_def)

lemma maps_to_eq:"maps_to A B = Pi A (\<lambda>_. B)" by (simp add: Pi_def maps_to_def)
lemma maps_to_memI[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> maps_to A B"  by (simp add: maps_to_def)
lemma id_maps_to[simp]: "(\<lambda>x. x) \<in> maps_to A A" by auto
lemma maps_to_memD: "f \<in> maps_to A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B" by (simp add: maps_to_def)
lemma maps_toE[elim]: "f \<in> maps_to A B \<Longrightarrow> (f x \<in> B \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q" by (auto simp: maps_to_def)
lemma maps_to_cong: "(\<And>w. w \<in> A \<Longrightarrow> f w = g w) \<Longrightarrow> f \<in>  maps_to A B \<longleftrightarrow> g \<in>  maps_to A B"  by (auto simp: maps_to_def)
lemma maps_to_empty[simp]: "maps_to {} B = UNIV"  by (simp add: maps_to_def)
lemma maps_to_int: "maps_to I E \<inter> maps_to I F = (maps_to I (E \<inter> F))" by auto
lemma maps_splits_dom[simp]: "f \<in> maps_to (A \<union> B) X \<longleftrightarrow> f \<in> maps_to A X \<and> f \<in> maps_to B X" by (auto simp: maps_to_def)
lemma maps_splits_insert_dom[simp]: "f \<in> maps_to (insert a A) B \<longleftrightarrow>f \<in> maps_to A B \<and> f a \<in> B"  by (auto simp: Pi_def)
lemma maps_to_im:"f \<in> maps_to A B \<Longrightarrow> f ` A \<subseteq> B"  by auto
definition hom::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where "hom A B \<equiv> {f. ((\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B))}"
lemma maps_to_comp: "f \<in> maps_to A B \<Longrightarrow> g \<in> maps_to B C \<Longrightarrow> compose A g f \<in> maps_to A C"  by (simp add: maps_to_def compose_def restrict_def)
lemma compose_assoc:"f \<in> maps_to A B \<Longrightarrow>compose A h (compose A g f) = compose A (compose B h g) f "by (simp add: fun_eq_iff maps_to_def compose_def restrict_def)
lemma compose_eq: "x \<in> A \<Longrightarrow> compose A g f x = g (f x)" by (simp add: compose_def restrict_def)
lemma surj_compose: "f ` A = B \<Longrightarrow> g ` B = C \<Longrightarrow> compose A g f ` A = C"  by (auto simp add: image_def compose_eq)
lemma restrict_cong: "I = J \<Longrightarrow> (\<And>i. i \<in> J =simp=> f i = g i) \<Longrightarrow> restrict f I = restrict g J"  by (auto simp: restrict_def fun_eq_iff simp_implies_def)
lemma restrictI1[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> Pi A B"  by (simp add: Pi_def restrict_def)
lemma restrictI2[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> maps_to A B"  by (simp add: maps_to_def restrict_def)
lemma restrict_apply[simp]: "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"  by (simp add: restrict_def)
lemma restrict_apply': "x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x" by simp
lemma restrict_ext: "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)" by (simp add: fun_eq_iff maps_to_def restrict_def)
lemma restrict_UNIV: "restrict f UNIV = f" by (simp add: restrict_def)
lemma inj_on_restrict_eq [simp]: "inj_on (restrict f A) A \<longleftrightarrow> inj_on f A"  by (simp add: inj_on_def restrict_def)
lemma inj_on_restrict_iff: "A \<subseteq> B \<Longrightarrow> inj_on (restrict f B) A \<longleftrightarrow> inj_on f A"  by (metis inj_on_cong restrict_def subset_iff)
lemma id_compose1: "f \<in> maps_to A B \<Longrightarrow> f \<in> maps_on A \<Longrightarrow> compose A (\<lambda>y\<in>B. y) f = f" by (auto simp add: fun_eq_iff compose_def maps_on_def maps_to_def)
lemma id_compose2: "f \<in> maps_to A B \<Longrightarrow> f \<in> maps_on A \<Longrightarrow> compose A f (\<lambda>x\<in>A. x) = f" by (auto simp add: fun_eq_iff compose_def maps_on_def maps_to_def)
lemma image_restrict_eq [simp]: "(restrict f A) ` A = f ` A"  by (auto simp add: restrict_def)
lemma restrict_restrict[simp]: "restrict (restrict f A) B = restrict f (A \<inter> B)"  unfolding restrict_def by (simp add: fun_eq_iff)
lemma bijI:"f \<in> maps_to A B \<Longrightarrow> g \<in> maps_to B A \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> g (f x) = x) \<Longrightarrow> (\<And>y. y\<in>B \<Longrightarrow> f (g y) = y) \<Longrightarrow> bij_betw f A B"  by (metis bij_betw_byWitness maps_to_im)
lemma bijD1: "bij_betw f A B \<Longrightarrow> f \<in> maps_to A B"  by (auto simp add: bij_betw_def)
lemma inj_compose:"bij_betw f A B \<Longrightarrow> inj_on g B \<Longrightarrow> inj_on (compose A g f) A"   by (auto simp add: bij_betw_def inj_on_def compose_eq)
lemma bij_compose:"bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (compose A g f) A C"  by (simp add: inj_compose bij_betw_def surj_compose)
lemma bij_restrict_eq [simp]: "bij_betw (restrict f A) A B = bij_betw f A B" by (simp add: bij_betw_def)


subsection \<open>Extensionality\<close>
lemma maps_on_memI[intro]:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> maps_on A" by (simp add: maps_on_def)
lemma maps_on_memD:"f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" by (simp add: maps_on_def)
lemma maps_on_empty[simp]: "maps_on {} = {\<lambda>x. undefined}"  unfolding maps_on_def by auto
lemma maps_on_arb: "f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined"  by (simp add: maps_on_def)
lemma restrict_maps_on [simp]: "restrict f A \<in> maps_on A" by (simp add: restrict_def maps_on_def)
lemma compose_maps_on [simp]: "compose A f g \<in> maps_on A"  by (simp add: compose_def)
lemma maps_on_equalityI:"f \<in> maps_on A \<Longrightarrow> g \<in> maps_on A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g" by (force simp add: fun_eq_iff maps_on_def)
lemma maps_on_restrict:  "f \<in> maps_on A \<Longrightarrow> restrict f A = f"  by (rule maps_on_equalityI[OF restrict_maps_on]) auto
lemma maps_on_subset: "f \<in> maps_on A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f \<in> maps_on B" unfolding maps_on_def by auto
lemma inv_map_to: "f ` A = B \<Longrightarrow> (\<lambda>x\<in>B. inv_into A f x) \<in> maps_to B A"  by (unfold inv_into_def) (fast intro: someI2)
lemma compose_inv_into_id: "bij_betw f A B \<Longrightarrow> compose A (\<lambda>y\<in>B. inv_into A f y) f = (\<lambda>x\<in>A. x)"  by (simp add: bij_betw_def compose_def,rule restrict_ext, auto)
lemma compose_id_inv_into: "f ` A = B \<Longrightarrow> compose B f (\<lambda>y\<in>B. inv_into A f y) = (\<lambda>x\<in>B. x)"  by (simp add: compose_def,rule restrict_ext,simp add: f_inv_into_f)
lemma maps_on_Int[simp]: "maps_on I \<inter> maps_on I' = maps_on (I \<inter> I')"  unfolding maps_on_def by auto
lemma maps_on_UNIV[simp]: "maps_on UNIV = UNIV"  by (auto simp: maps_on_def)
lemma restrict_maps_on_sub[intro]: "A \<subseteq> B \<Longrightarrow> restrict f A \<in> maps_on B"  unfolding restrict_def maps_on_def by auto
lemma maps_on_insert_cancel[intro, simp]:  "a \<in> maps_on I \<Longrightarrow> a \<in> maps_on (insert i I)"  unfolding maps_on_def by auto


definition Id where "Id X \<equiv> (\<lambda>x \<in> X. x)"
lemma hom_memI1:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> hom A B" unfolding hom_def by fast
lemma hom_memI2:"f \<in> maps_on A \<Longrightarrow> f \<in>maps_to A B \<Longrightarrow> f \<in> hom A B"   by(rule hom_memI1,auto elim: maps_on_memD)
lemma hom_memD1:"f \<in> hom A B \<Longrightarrow> f \<in> maps_on A" unfolding hom_def maps_on_def by(auto)
lemma hom_memD2:"f \<in> hom A B \<Longrightarrow> f \<in> maps_to A B" unfolding hom_def maps_to_def by(auto)
lemma id1[simp]:"Id X x = (if x \<in> X then x else undefined)" by (simp add:Id_def)
lemma hom1:"hom {} Y = {\<lambda>x. undefined}"  by(auto simp add:hom_def) 
lemma hom2:"f \<in> hom A B \<Longrightarrow> g \<in> hom B C \<Longrightarrow> compose A g f \<in> hom A C" by(auto simp add:hom_def compose_def)
lemma hom3:"f \<in> hom A B \<Longrightarrow> compose A h (compose A g f) = compose A (compose B h g) f" by(auto simp add:hom_def fun_eq_iff compose_def)

lemma f_eqI:
  assumes A0:"f \<in> hom A Y" and A1:"g \<in> hom A Z" and A2:"(\<And>x. x \<in> A \<Longrightarrow> f x = g x)"
  shows "f = g"
proof(auto simp add: fun_eq_iff)
  fix x show "f x = g x"
  proof(cases "x \<in> A")
    case True then show ?thesis using A2 by auto
  next
    case False then obtain "f x = undefined" and "g x = undefined" using A0 A1 by (meson hom_memD1 maps_on_memD)
    then show ?thesis by simp
  qed
qed
lemma fun_eqI:"f \<in> hom A Y \<Longrightarrow> g \<in> hom A Z \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g"  using f_eqI by blast 
lemma hom5:"f \<in> hom A B \<Longrightarrow> compose A (Id B) f = f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom6:"f \<in> hom A B  \<Longrightarrow> compose A f (Id A) = f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom7:"(Id A) \<in> hom A A" unfolding hom_def by(auto)
lemma hom8:"A \<subseteq> B \<Longrightarrow> (Id A) \<in> hom A B"  using hom_def by fastforce 
lemma hom9:"f \<in> hom A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B" unfolding hom_def by simp
lemma hom10:"f \<in> hom A B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" unfolding hom_def by simp
lemma hom11:"f \<in> hom A B \<Longrightarrow> g \<in> hom A C \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = g x" unfolding hom_def by(auto)

definition surj::"('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where"surj f Y \<equiv> (\<forall>y \<in> Y. \<exists>x. f x = y)"
lemma surjI1:"(\<And>y. y \<in> Y \<Longrightarrow> (\<exists>x. f x = y)) \<Longrightarrow> surj f Y"by (simp add: surj_def)
lemma surjI2:"(\<And>y. y \<in> Y \<Longrightarrow> (\<exists>x. y = f x )) \<Longrightarrow> surj f Y"by(auto simp add:surj_def)
lemma surj_fiber_nonempty:  "surj f Y \<Longrightarrow> y \<in> Y \<Longrightarrow> vimage f {y} \<noteq> {}"  unfolding surj_def by auto
lemma surjE1:"surj f Y \<Longrightarrow> y \<in> Y \<Longrightarrow> (\<exists>x. f x = y)" by (simp add: surj_def)
lemma surjE2:"surj f Y \<Longrightarrow> y \<in> Y \<Longrightarrow> (\<exists>x. y= f x)"  using surjE1 by fastforce
lemma surjE3:"surj f Y \<Longrightarrow> (\<And>y. \<exists>x. y = f x \<Longrightarrow> P) \<Longrightarrow> P" by auto
lemma surj_obtains:  assumes "surj f Y" and "y \<in> Y"  obtains x where "f x = y" using assms unfolding surj_def by blast

section RightInverse
definition is_right_inv::"'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where"is_right_inv Y f s \<equiv> (\<forall>y \<in> Y.  f (s y) = y)"
lemma is_right_invI1: "(\<And>y. y \<in> Y \<Longrightarrow> f (s y) = y) \<Longrightarrow> is_right_inv Y f s" unfolding  is_right_inv_def by blast
lemma is_right_invI2:  "(\<And>y. y \<in> Y \<Longrightarrow> y = f (s y)) \<Longrightarrow> is_right_inv Y f s"by (simp add: is_right_invI1)
lemma is_right_invE1:"is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> f (s y) = y" by (simp add: is_right_inv_def)
lemma is_right_invE2:"is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> y = f (s y) "  by (simp add: is_right_inv_def)
lemma ex_rinv_imp_surj: "\<exists>s. is_right_inv Y f s \<Longrightarrow> surj f Y" unfolding surj_def is_right_inv_def by(auto)
lemma is_rinv_imp_surj: "is_right_inv Y f s \<Longrightarrow> surj f Y" using ex_rinv_imp_surj by blast

lemma surj_implies_ex_rinv:
  "surj f Y \<Longrightarrow> \<exists>s. is_right_inv Y f s"
proof-
  assume onto:"surj f Y"
  have "\<exists>s. \<forall>y \<in> Y. y = f (s y)"
  proof(rule bchoice[of Y "\<lambda>a b. a = f b"])
    show "\<forall>y::'b\<in>Y. \<exists>ya::'a. y = f ya"
    using onto unfolding surj_def by fastforce
  qed
  then show "\<exists>s. is_right_inv Y f s"
    by (metis is_right_inv_def) 
qed


section LeftInverse


definition is_left_inv::"'a set \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where "is_left_inv X f r \<equiv> (\<forall>x \<in> X.  r (f x) = x)"
lemma is_left_invI1[intro]: "(\<And>x. x \<in> X \<Longrightarrow> r (f x) = x) \<Longrightarrow> is_left_inv X f r" unfolding  is_left_inv_def by blast
lemma is_left_invI2[intro]: "(\<And>x. x \<in> X \<Longrightarrow> x = r (f x)) \<Longrightarrow> is_left_inv X f r" by (simp add: is_left_inv_def)
lemma is_left_invE1:"is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> r (f x) = x"by (simp add: is_left_inv_def)
lemma is_left_invE2:"is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> x = r (f x)"by (simp add: is_left_inv_def)
lemma is_left_inv_id:"is_left_inv X f r \<Longrightarrow> compose X r f = Id X"  using maps_on_equalityI[of "compose X r f" X "Id X"]  by (simp add: Id_def compose_eq is_left_invE1)
lemma linv_cancel:"is_left_inv X f r \<Longrightarrow> x1 \<in>X \<Longrightarrow>  x2 \<in> X \<Longrightarrow> f x1 = f x2 \<Longrightarrow> x1 =x2"  by (metis (no_types) is_left_invE1)
lemma ex_linv_implies_inj:"\<exists>s. is_left_inv X f r \<Longrightarrow> inj_on f X" by (simp add: inj_on_def linv_cancel)
lemma is_linv_implies_inj:"is_left_inv X f r \<Longrightarrow> inj_on f X"by (simp add: inj_on_def linv_cancel)
lemma inj_implies_ex_linv:"inj_on f X \<Longrightarrow> \<exists>r. is_left_inv X f r" unfolding is_left_inv_def using inv_into_f_f[of f X] by blast


section LeftRightInverses
lemma left_inv_target: "is_left_inv X f r \<Longrightarrow> r`(f`X) = X "  unfolding is_left_inv_def  by (simp add: image_comp)
lemma right_inv_target: "is_right_inv Y f s \<Longrightarrow> f`(s`Y) = Y"  unfolding is_right_inv_def  by (simp add: image_comp)
lemma rinv_l: "is_left_inv X f r \<Longrightarrow> is_right_inv X r f" by (simp add: is_left_invE1 is_right_inv_def)
lemma linv_r:"is_right_inv (Y::'b set) f s \<Longrightarrow> is_left_inv Y s f" by (simp add: is_left_inv_def is_right_invE1)
lemma rinv_surj: "is_left_inv X f r \<Longrightarrow> surj r X" using ex_rinv_imp_surj rinv_l by blast
lemma linv_inj: "is_right_inv (Y::'b set) f s \<Longrightarrow> inj_on s Y"  using is_linv_implies_inj linv_r by blast

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

definition fun_section :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'a" where "fun_section f X Y \<equiv> (\<lambda>y \<in> Y. SOME x.  x \<in> X \<and> f x = y)"

lemma fun_section_simp:"y \<in> Y \<Longrightarrow> fun_section f X Y y = (\<lambda>y. SOME x. x \<in> X \<and> f x = y) y" by (simp add: fun_section_def)

lemma section_is_rinv:
  assumes A0:"surj f Y" and A1:"image f X = Y"
  shows "is_right_inv Y f (fun_section f X Y)"
proof-
  let ?A="vimage f Y"
  let ?s=" (fun_section f X Y)"
  show ?thesis
  proof(rule is_right_invI2)
    fix y assume A2:"y \<in> Y" 
    show "y = f (?s y)"
    proof(simp add:A2 fun_section_simp, rule someI2_ex)
      show "\<exists>a::'a. a \<in> X \<and> f a = y"  using A1 A2 by blast
      show "\<And>x::'a. x \<in> X \<and> f x = y \<Longrightarrow> y = f x"  by simp
   qed
  qed
qed


lemma section_is_into[intro,simp]:
  assumes A0:"surj f Y" and A1:"image f X = Y" and A2:"y \<in> Y"
  shows "(fun_section f X Y) y \<in> X"
  proof(simp add:A2 fun_section_simp, rule someI2_ex)
    show  "\<exists>a::'a. a \<in> X \<and> f a = y"
      using A1 A2 by blast
    show "\<And>x::'a. x \<in> X \<and> f x = y \<Longrightarrow> x \<in> X"
      by simp
qed

locale set_morphism=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes dom[intro]:"x \<notin> A \<longrightarrow> f x = undefined" and   cod[intro,simp]:"x \<in> A \<Longrightarrow> f x \<in> B"
begin
lemma mem_maps_to:"f \<in> maps_to A B" by (simp add: maps_to_memI)
lemma mem_maps_on:"f \<in> maps_on A" by (simp add: dom maps_on_memI) 
lemma mem_hom:"f \<in> hom A B" by (simp add: hom_memI2 mem_maps_on mem_maps_to)
end
locale sur_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"   assumes sur[intro]:"f `A = B"
locale inj_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"   assumes inj[intro, simp]:"inj_on f A"
locale iso_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"   assumes iso[intro, simp]:"bij_betw f A B"
locale set_epimorphism =set_morphism + sur_locale
locale set_monomorphism=set_morphism + inj_locale
locale set_isomorphism =set_morphism + iso_locale
begin
sublocale set_epimorphism by unfold_locales (simp add:bij_betw_imp_surj_on)
sublocale set_monomorphism using bij_betw_def by unfold_locales fast
sublocale inverse:set_morphism "restrict (inv_into A f) B" B A by(unfold_locales;simp add: restrict_def;simp add: inv_into_into restrict_def sur)
sublocale inverse:iso_locale "restrict (inv_into A f) B" B A by(unfold_locales, simp add: bij_betw_inv_into)
end
context set_morphism
begin


theorem bij_betw_iff_has_inverse: "bij_betw f A B \<longleftrightarrow> (\<exists>g \<in> hom B A. compose A g f = Id A \<and> compose B f g = Id B)"  (is "_ \<longleftrightarrow> (\<exists>g \<in> hom B A. ?INV g)")
proof
  let ?inv = "restrict (inv_into A f) B"
  assume A0:"bij_betw f A B"
  then have "?INV ?inv" 
    by (simp add: bij_betw_inv_into_left bij_betw_inv_into_right is_left_invI2 is_left_inv_id)
  also have "?inv \<in> hom B A"  by (rule hom_memI2, simp,simp add: A0 bijD1 bij_betw_inv_into)
  then show "\<exists>g \<in> hom B A. ?INV g"  using calculation by auto
next
  assume "\<exists>g \<in> hom B A. ?INV g"
  then obtain g where "f \<in> maps_to A B" "g \<in> maps_to B A" and "\<And>x. x\<in>A\<Longrightarrow>g(f x) = x" and "\<And>y. y\<in>B \<Longrightarrow> f(g y) = y"  by (metis mem_maps_to compose_eq hom_memD2 id1)
  then show "bij_betw f A B" by (rule bijI) 
qed
end


definition is_disjoint::"'a set set \<Rightarrow> bool" where "is_disjoint P \<equiv> (\<forall>p \<in> P. \<forall>q \<in> P. p \<inter> q \<noteq> {} \<longrightarrow> p =q)"

lemma is_disjointI1: "(\<And>p q. \<lbrakk>p \<in> P; q \<in> P; p \<inter> q \<noteq> {}\<rbrakk> \<Longrightarrow> p=q) \<Longrightarrow> is_disjoint P" by (simp add: is_disjoint_def)
lemma is_disjointE1:  "is_disjoint P \<Longrightarrow> \<lbrakk>p \<in> P; q \<in> P; x \<in>p; x \<in> q\<rbrakk> \<Longrightarrow> p=q" unfolding is_disjoint_def by blast
lemma is_disjointE2:  "\<lbrakk>is_disjoint P; p \<in> P; q \<in> P\<rbrakk> \<Longrightarrow> p=q \<or> p \<inter> q = {} "  unfolding is_disjoint_def by blast
definition is_part::"'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where  "is_part X P \<equiv> is_disjoint P \<and> \<Union>P=X \<and> {} \<notin> P"
lemma is_partI1:  "\<Union>P=X \<Longrightarrow> is_disjoint P \<Longrightarrow> {} \<notin> P \<Longrightarrow> is_part X P" by (simp add: is_part_def)
lemma is_partE1:  assumes A0:"is_part X P" and A1:"x \<in> X" obtains p where "p \<in> P" and "x \<in> p"  by (metis A0 A1 UnionE is_part_def)
lemma is_partE2: "\<lbrakk>is_part X P; p \<in> P\<rbrakk> \<Longrightarrow> p \<subseteq> X"  unfolding is_part_def by auto
lemma is_part_ex1:  "\<lbrakk>is_part X P; x \<in>X\<rbrakk> \<Longrightarrow> (\<exists>p \<in> P. x \<in> p)" by (meson is_partE1)
lemma is_part_ex2: "\<lbrakk>is_part X P; x \<in>X; p \<in> P; x \<in> p; q \<in> P; x \<in> q \<rbrakk> \<Longrightarrow> p=q"  unfolding is_part_def is_disjoint_def by auto

lemma is_part_unique: "\<lbrakk>is_part X P; x \<in>X\<rbrakk> \<Longrightarrow> (\<exists>!p \<in> P. x \<in> p)"
proof(rule ex_ex1I)
  show "is_part X P \<Longrightarrow> x \<in> X \<Longrightarrow> \<exists>p. p \<in> P \<and> x \<in> p"
    using is_part_ex1[of X P x] by auto
  show "\<And>p y. is_part X P \<Longrightarrow> x \<in> X \<Longrightarrow> p \<in> P \<and> x \<in> p \<Longrightarrow> y \<in> P \<and> x \<in> y \<Longrightarrow> p = y"
    using is_part_ex2[of X P x ] by presburger
qed


section EquivalenceRelation
subsection EquivalenceClasses
definition is_eqrel::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where "is_eqrel X R \<equiv> refl_on X R \<and> sym R \<and> trans R"

lemma converse_fst_snd:  "fst`R=snd`(converse R)" by (simp add: fst_eq_Domain snd_eq_Range)

lemma is_eqrelI1:  "\<lbrakk>refl_on X R; sym R; trans R\<rbrakk> \<Longrightarrow> is_eqrel X R" using is_eqrel_def by blast

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

lemma eqrelE4c:"is_eqrel X R \<Longrightarrow> x \<in> R``{y} \<Longrightarrow> x \<in> X"  by (simp add: eqrelE4)
lemma eqrelE4d:"is_eqrel X R \<Longrightarrow> x \<in> R``{y} \<Longrightarrow> y \<in> X"  by (simp add: eqrelE4)

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
  obtain z where "z \<in> X" and "R``{z} = t"  by (metis A1 quotientE4)
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
  show " \<Union> (quotient X R) = X"
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

lemma is_eqr_compat_p:
  assumes eqr:"is_eqrel X R"
  shows" is_eqr_compat X R f \<longleftrightarrow> (\<forall>z. eqr_compat_prop X R (\<lambda>x. z = f x))"  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L:?lhs
  show ?rhs
  proof
    fix z let ?P="(\<lambda>x. z = f x)"
    show  "eqr_compat_prop X R ?P"
    using L unfolding eqr_compat_prop_def is_eqr_compat_def by(auto)
  qed
  next
  assume R:?rhs
  show ?lhs
  proof(rule is_eqr_compatI1)
    fix x y assume a0:"x \<in> X" and a1:"y \<in> X" and a2:"(x,y)\<in> R"
    obtain  z where a3:"z = f x"
      by simp
    then show "f x = f y"
    using R  by (simp add: a0 a1 a2 eqr_compat_prop_def)
  qed
qed

   
    
lemma is_eqr_compatI2:
  "is_eqrel X R \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; R``{x}=R``{y}\<rbrakk> \<Longrightarrow> f x = f y) \<Longrightarrow> is_eqr_compat X R f"
  by (meson eqrel_class3e is_eqr_compatI1)

lemma is_eqr_compatE1:
  "is_eqrel X R \<Longrightarrow> is_eqr_compat X R f \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> f x = f y"
  by (simp add: eqrelE4 is_eqr_compat_def)
                                                      
lemma is_eqr_compatE2:
  "is_eqrel X R \<Longrightarrow> is_eqr_compat X R f \<Longrightarrow> t \<in> (X/R) \<Longrightarrow> x \<in> t \<Longrightarrow> y \<in> t \<Longrightarrow> f x = f y"
  using quotient_mem_elem[of X R t x y] is_eqr_compatE1[of X R f x y] by blast

lemma is_eqr_compatE3: "is_eqrel X R \<Longrightarrow> is_eqr_compat X R f \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> R``{x} \<Longrightarrow> f y = f x" using is_eqr_compatE1 by fastforce

lemma is_eqr_compatE4:
  assumes "is_eqrel X R" "is_eqr_compat X R f" "x \<in> X"
  shows "(\<Union>y \<in> R``{x}. f y) = f x"
proof-
  have Q1: "\<forall>y\<in>R `` {x}. f x = f y"
    using assms is_eqr_compatE3[of X R f x _] by blast
  have Q2:"x \<in> R``{x}"
    using eqrel_class3[of X R x] assms(1,3) by auto
  show ?thesis
    using Q1 Q2 by blast
qed

lemma is_eqr_compatE5:
  "is_eqrel X R \<Longrightarrow> is_eqr_compat X R f \<Longrightarrow> t \<in> X/R \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<Union>x \<in> t. f x) \<in> B"
  unfolding quotient_def using is_eqr_compatE4 by fastforce


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
  where "canonical_proj X R \<equiv> (\<lambda>x \<in> X. THE t. t \<in> (X/R) \<and>  x \<in> t)"


lemma canonical_proj_eq:
  assumes A0:"is_eqrel X R" and A1:"x \<in> X"
  shows "canonical_proj X R x = R``{x}"
  unfolding canonical_proj_def
  apply(simp add:A1)
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
        canonical_proj_props4:"surj  (canonical_proj X R) (X/R)" and
        canonical_proj_props5:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R \<longleftrightarrow> (canonical_proj X R) x = (canonical_proj X R) y" and
        canonical_proj_props6:"(canonical_proj X R)`(X) =(X/R)" and
        canonical_proj_props7:"\<And>x. x \<in> X \<Longrightarrow> y \<in> canonical_proj X R x\<Longrightarrow> (x,y)\<in>R" 
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
      by (metis B0 B1 UnionI assms canonical_proj_eq quotient_un unique_class1)
   qed
   show P3:"surj (canonical_proj X R) (X/R)" by (meson surj_def P1) 
   show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y)\<in>R \<longleftrightarrow> (canonical_proj X R) x = (canonical_proj X R) y"
     using A0 canonical_proj_eq[of X R] eqrel_class3e[of X R] by auto
   show P4:"(canonical_proj X R)`(X) =(X/R)"
     by (simp add: quotient_def UNION_singleton_eq_range assms canonical_proj_eq)
  show P5:"\<And>x. x \<in> X \<Longrightarrow> y \<in> canonical_proj X R x\<Longrightarrow> (x,y)\<in>R"
    by (simp add: assms canonical_proj_eq) 
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
  assumes gsurj:"surj g Y" and vim:"(image g X) = Y" and compat:"(\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
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
      then obtain B0:"g x \<in> Y"  and B1:"?s (g x) \<in> X"  by (simp add: gsurj vim)
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
  by (simp add: canonical_proj_props4 canonical_proj_props6 eqr proj_section_def)


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
  by (metis canonical_proj_props3 eqr proj_section2 proj_section3 unique_class) 

lemma factor_mapping_eqrel1:
  fixes X::"'a set" and R::"'a rel"
  defines "\<pi> \<equiv> canonical_proj X R"
  assumes eqr:"is_eqrel X R" and  compat:"(\<forall>x \<in> X. \<forall>y \<in> X. \<pi> x = \<pi> y \<longrightarrow> f x = f y)"
  shows "\<exists>h. \<forall>x \<in> X. f x = h (\<pi> x)"
proof(rule factor_mapping[where ?Y="X/R"])
  show  "surj \<pi> (X / R)"
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
    by (metis R0 \<pi>_def eqr is_eqr_compatI3) 
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
  assumes fmap:"f`X \<subseteq> Z" and gsurj:"surj f Y" and compat:"(\<forall>x \<in> X. \<forall>y \<in> X. g x = g y \<longrightarrow> f x = f y)"
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
        quotient_of_quotient7:"surj  h2 (X/R)"
proof-
  obtain B0:"is_eqr_compat X R f" and B1:"is_eqr_compat X S g"
    by (simp add: A0 A1 f_def g_def prj_compat)
  then obtain B2:"is_eqr_compat X S f"   by (meson A0 A1 A2 is_eqr_compat_finer)
  have B3:"\<And>x y. (x,y)\<in>R  \<longleftrightarrow> f x = f y \<and>  x \<in> X \<and> y \<in> X"  by (metis A0 canonical_proj_props5 eqrelE4 f_def)
  have B4:"\<And>x y. (x,y)\<in>S  \<longleftrightarrow> g x = g y \<and>  x \<in> X \<and> y \<in> X" by (metis A1 canonical_proj_props5 eqrel_class3e g_def)
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
    show "(\<exists>x \<in> X. t = g x)"  using A1 C0 g_def proj_section2 proj_section3 by blast
  qed
  show P4:"\<And>t. t \<in> (X/S) \<Longrightarrow> (h2(h1 t))=h t"
    by (simp add: T_def eqr_associated_compat eqr_associated_is_eqr h1_def h2_def is_eqr_compat_concrete) 
  show P5:"inj_on h2 ((X/S)/T)"
    by (simp add: T_def eqr_inj2 h2_def)
  show P6:"surj  h2 (X/R)" by (metis surj_def P2 P4)  
qed


definition product_eqrel::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> (('a \<times> 'b) \<times> 'a \<times> 'b) set" where
  "product_eqrel X R Y S \<equiv> {((x1, y1), (x2, y2)) \<in>(X \<times> Y) \<times> (X \<times> Y). (x1, x2) \<in> R \<and> (y1, y2) \<in> S}"


lemma product_eqrel_sym:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S"
  shows "sym (product_eqrel X R Y S)"
  using assms unfolding sym_def product_eqrel_def is_eqrel_def by(blast)

lemma product_eqrel_trans:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S"
  shows "trans (product_eqrel X R Y S)"
  using assms unfolding trans_def product_eqrel_def is_eqrel_def by(blast)

lemma product_eqrel_refl:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S"
  shows "refl_on (X \<times> Y) (product_eqrel X R Y S)"
  using assms unfolding refl_on_def product_eqrel_def is_eqrel_def by(auto)

lemma product_eqrel_reql:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> is_eqrel (X \<times> Y)  (product_eqrel X R Y S)"
  by (simp add: is_eqrelI1 product_eqrel_refl product_eqrel_sym product_eqrel_trans)

lemma product_eqrel_subset:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow>  (product_eqrel X R Y S) \<subseteq> ( (X \<times> Y)  \<times>  (X \<times> Y) )"
  by (simp add: eqrelE4b product_eqrel_reql)

lemma product_eqrel_mem1:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (u, v) \<in>  (product_eqrel X R Y S) \<longleftrightarrow> (\<exists>x1 \<in> X. \<exists>x2 \<in> X. \<exists>y1 \<in> Y. \<exists>y2 \<in> Y. u=(x1, y1) \<and> v = (x2, y2) \<and> (x1, x2)\<in>R \<and> (y1, y2)\<in>S)"
  unfolding product_eqrel_def by(auto)

lemma product_eqrel_mem2:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (u, v) \<in>  (product_eqrel X R Y S) \<longleftrightarrow>  (fst u, fst v) \<in> R \<and> (snd u, snd v) \<in> S"
  unfolding product_eqrel_def by(auto simp add:eqrelE4)
  

lemma product_eqrel_memE1:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (u, v) \<in>  (product_eqrel X R Y S) \<Longrightarrow>  (fst u, fst v) \<in> R \<and> (snd u, snd v) \<in> S \<and> fst u \<in> X \<and> fst v \<in> X \<and> snd u \<in> Y \<and> snd v \<in> Y"
  by (metis eqrelE4 product_eqrel_mem2)

lemma product_eqrel_memE2:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> ((x1, y1), (x2, y2)) \<in>  (product_eqrel X R Y S) \<Longrightarrow>x1 \<in> X \<and> x2 \<in> X \<and> y1\<in> Y \<and> y2 \<in> Y"
  by (simp add: product_eqrel_mem1)
  
  
lemma product_eqrel_memI1:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (fst u, fst v) \<in> R \<and> (snd u, snd v) \<in> S \<Longrightarrow> (u, v) \<in>  (product_eqrel X R Y S) "
  by (simp add: product_eqrel_mem2)

lemma product_eqrel_memI2:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (x1, x2) \<in> R \<and> (y1, y2) \<in> S \<Longrightarrow> ((x1, y1), (x2, y2)) \<in>  (product_eqrel X R Y S) "
  by (simp add: product_eqrel_mem2)
  

lemma product_eqrel_mem3:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S; ((x1, y1), v) \<in> (product_eqrel X R Y S)\<rbrakk> \<Longrightarrow> (\<exists>x2 \<in> X. \<exists>y2 \<in> Y. v=(x2, y2) \<and> (x1, x2)\<in>R \<and> (y1, y2)\<in>S)"
  by (simp add: product_eqrel_mem1)


lemma product_eqrel_mem4:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S; (\<exists>x2 \<in> X. \<exists>y2 \<in> Y. v=(x2, y2) \<and> (x1, x2)\<in>R \<and> (y1, y2)\<in>S)\<rbrakk> \<Longrightarrow> ((x1, y1), v) \<in> (product_eqrel X R Y S) "
  using product_eqrel_mem2[of X R Y S] by force


lemma product_eqrel_mem_iff1:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow>(u, u) \<in> ( product_eqrel X R Y S) \<longleftrightarrow>  (\<exists>x \<in> X. \<exists>y \<in> Y. u=(x, y) \<and> (x, x) \<in>R \<and> (y, y) \<in> S) "
  unfolding product_eqrel_def by(auto)
 

lemma product_eqrel_mem_iff2:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow>(u, u) \<in> ( product_eqrel X R Y S) \<longleftrightarrow> (\<exists>x \<in> X. \<exists>y \<in> Y. u=(x,y))"
  by (simp add: eqrel_class3e product_eqrel_mem_iff1)


lemma product_eqrel_mem_iff3:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow>(u, u) \<in> ( product_eqrel X R Y S) \<longleftrightarrow> u \<in> (X \<times> Y)"
  using product_eqrel_mem_iff2[of X R Y S u] by blast



lemma product_eqrel_mem_iff4:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> ((x1, y1), v)\<in>(product_eqrel X R Y S) \<longleftrightarrow> (\<exists>x2 \<in> X. \<exists>y2 \<in> Y. v=(x2, y2) \<and> (x1, x2)\<in>R \<and>(y1, y2)\<in> S)"
  using eqrelE4[of X R]  eqrelE4[of Y S] by (metis fst_conv prod.exhaust_sel product_eqrel_mem2 snd_conv)



lemma product_eqrel_mem_obtain1:
  assumes "is_eqrel X R" and "is_eqrel Y S" and "(u, v) \<in> (product_eqrel X R Y S)"
  obtains x1 x2 y1 y2 where "x1 \<in> X" and "x2\<in>X" and "y1 \<in> Y" and "y2 \<in> Y" and  "u=(x1, y1)" and  "v = (x2, y2)" and "(x1, x2)\<in>R" and "(y1, y2)\<in>S"
  using assms  product_eqrel_mem1 by blast
 

lemma product_eqrel_mem_obtain2:
  assumes "is_eqrel X R" and "is_eqrel Y S" and "((x1, y1), v) \<in> (product_eqrel X R Y S)"
  obtains x2 y2 where  "x2\<in>X" and "y2 \<in> Y" and  "v = (x2, y2)" and "(x1, x2)\<in>R" and "(y1, y2)\<in>S"
  using assms product_eqrel_mem1 by blast

lemma product_eqrel_mem_obtain3:
  assumes "is_eqrel X R" and "is_eqrel Y S" and "(u, (x2, y2)) \<in> (product_eqrel X R Y S)"
  obtains x1 y1 where "x1 \<in> X" and  "y1 \<in> Y" and  "u=(x1, y1)" and "(x1, x2)\<in>R" and "(y1, y2)\<in>S"
  using assms product_eqrel_mem1 by blast


lemma product_eqrel_mem_iff5:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S"
  shows "((x1, y1), v) \<in> (product_eqrel X R Y S) \<longleftrightarrow> x1 \<in> X \<and> y1 \<in> Y \<and> v \<in> ((canonical_proj X R x1) \<times> (canonical_proj Y S y1))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L:?lhs
  show ?rhs 
  proof-
    obtain x1mem:"x1 \<in> X" and y1mem:"y1 \<in> Y"  
      using eqr eqs L product_eqrel_mem_obtain1[of X R Y S] by blast
    obtain x2 y2 where "x2 \<in> X" and "y2 \<in> Y" and "v=(x2, y2)"
      using L eqr eqs product_eqrel_memE1[of X R Y S "(x1, y1)" v]  prod.exhaust_sel by blast
    then obtain "(x1, x2)\<in>R" and "(y1, y2)\<in>S"
      using L eqr eqs product_eqrel_mem2 by fastforce
    then obtain "x2 \<in> (canonical_proj X R x1)" and "y2 \<in> (canonical_proj Y S y1)"
      by (simp add: canonical_proj_eq eqr eqs x1mem y1mem)
    then show " x1 \<in> X \<and> y1 \<in> Y \<and>  v \<in> ((canonical_proj X R x1) \<times> (canonical_proj Y S y1))"
      using \<open>(v::'a \<times> 'b) = (x2::'a, y2::'b)\<close> x1mem y1mem by blast
  qed
  next
  assume R:?rhs
  show ?lhs
  proof-
    obtain x2 y2 where "x2 \<in> (canonical_proj X R x1)" and "y2 \<in> (canonical_proj Y S y1)"  and "v=(x2, y2)"
      using R by blast 
    then obtain "(x1, x2)\<in>R" and "(y1, y2)\<in>S"
      by (meson R canonical_proj_props7 eqr eqs) 
    then show "((x1, y1), v) \<in> (product_eqrel X R Y S)"
      by (simp add: \<open>(v::'a \<times> 'b) = (x2::'a, y2::'b)\<close> eqr eqs product_eqrel_memI2)
  qed
qed

lemma product_eqrel_mem_iff6:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (u, v)\<in>(product_eqrel X R Y S) \<longleftrightarrow> fst u \<in> X \<and> snd u \<in> Y \<and> v \<in> ((canonical_proj X R (fst u)) \<times> (canonical_proj Y S (snd u)))"
  by (metis prod.exhaust_sel product_eqrel_mem_iff5)


lemma product_eqrel_memE3:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (u, v)\<in>(product_eqrel X R Y S) \<Longrightarrow> fst u \<in> X \<and> snd u \<in> Y \<and> v \<in> ((canonical_proj X R (fst u)) \<times> (canonical_proj Y S (snd u)))"
  using product_eqrel_mem_iff6 by blast


lemma product_eqrel_memE4:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> (u, v)\<in>(product_eqrel X R Y S) \<Longrightarrow> fst v \<in> X \<and> snd v \<in> Y \<and> u \<in> ((canonical_proj X R (fst v)) \<times> (canonical_proj Y S (snd v)))"
  by (metis canonical_proj_props5 product_eqrel_mem2 product_eqrel_memE1 product_eqrel_mem_iff6)

lemma product_eqrel_memE5:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S" and umem:"u \<in> X \<times> Y"and vin:"v \<in> (canonical_proj (X \<times> Y) (product_eqrel X R Y S) u) "
  shows "fst v \<in> X \<and> snd v \<in> Y \<and> u \<in> ((canonical_proj X R (fst v)) \<times> (canonical_proj Y S (snd v)))"
  by (metis canonical_proj_props7 eqr eqs product_eqrel_memE4 product_eqrel_reql umem vin)


lemma product_eqrel_memE6:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S" and tmem:"t \<in> (X \<times> Y)/(product_eqrel X R Y S)"
  shows " (\<exists>t1 \<in> (X/R). \<exists>t2\<in>(Y/S). t= t1\<times>t2)"
proof-
  let ?RxS="(product_eqrel X R Y S)"
  obtain eqrs:"is_eqrel (X\<times>Y) ?RxS"
    by (simp add: eqr eqs product_eqrel_reql)
  obtain u where umem:"u \<in> X \<times> Y" and ueq:"t=(canonical_proj (X \<times> Y) ?RxS) u"
    using canonical_proj_props2 eqrs tmem by blast
  then obtain x1 y1 where x1mem:"x1 \<in> X" and y1mem:"y1 \<in> Y" and ueq2: "u=(x1, y1)"
    by blast
  define t1 where "t1 = (canonical_proj X R x1)"
  define t2 where "t2 = (canonical_proj Y S y1)"
  have "\<And>v. v \<in> t \<Longrightarrow> v \<in> t1 \<times> t2"
    by (metis ueq2 canonical_proj_props7 eqr eqrs eqs product_eqrel_mem_iff5 t1_def t2_def ueq umem)
  also have "\<And>v. v \<in> t1 \<times>t2 \<Longrightarrow> v \<in> t"
    unfolding t1_def t2_def using product_eqrel_mem_iff5[of X R Y S x1 y1 ] x1mem y1mem  by (simp add: canonical_proj_eq eqr eqrs eqs ueq ueq2) 
  then have "t=t1 \<times> t2"
    using calculation by blast 
  then show ?thesis
    by (metis canonical_proj_props1 eqr eqs t1_def t2_def x1mem y1mem)
qed


lemma product_eqrel_memE7:
  assumes eqr:"is_eqrel X R" and eqs:"is_eqrel Y S" and t12ex:"(\<exists>t1 \<in> (X/R). \<exists>t2\<in>(Y/S). t= t1\<times>t2)"
  shows "t \<in> (X \<times> Y)/(product_eqrel X R Y S)"
proof-
  obtain t1 t2 where t1mem:"t1 \<in> (X/R)" and t2mem:"t2\<in>(Y/S)" and teq:"t= t1\<times>t2"
    using t12ex by auto
  then obtain x1 y1 where x1mem:"x1 \<in> X" and t1eq:"t1=(canonical_proj X R x1)" and y1mem:"y1 \<in> Y" and t2eq:"t2=(canonical_proj Y S y1)"
    by (metis eqr eqs proj_section2 proj_section3)
  define u where "u=(x1, y1)"
  have "\<And>v. v \<in>  (canonical_proj (X \<times> Y) (product_eqrel X R Y S) u) \<Longrightarrow> v \<in> t"
    by (metis canonical_proj_props7 eqr eqs mem_Sigma_iff product_eqrel_mem_iff5 product_eqrel_reql t1eq t2eq teq u_def x1mem y1mem)
  also have "\<And>v. v \<in> t \<Longrightarrow> v \<in>  (canonical_proj (X \<times> Y) (product_eqrel X R Y S) u)"
  proof-
    fix v assume vin:"v \<in> t"
    then obtain x2 y2 where x2mem2:"x2 \<in> t1" and y2mem2:"y2 \<in> t2" and veq:"v=(x2, y2)"
      using teq by blast
    then obtain "(u, v)  \<in>(product_eqrel X R Y S) "
      by (simp add: eqr eqs product_eqrel_mem_iff5 t1eq t2eq u_def x1mem y1mem)
    then show "v \<in> canonical_proj (X \<times> Y) (product_eqrel X R Y S) u"
      by (metis Image_singleton_iff canonical_proj_eq eqr eqs product_eqrel_refl product_eqrel_reql refl_onD1)
  qed
  then obtain "t=(canonical_proj (X \<times> Y) (product_eqrel X R Y S) u)"
    using calculation by blast
  then show ?thesis
    by (metis SigmaI canonical_proj_props1 eqr eqs product_eqrel_reql u_def x1mem y1mem)
qed

lemma product_eqrel_memE8:
  "\<lbrakk>is_eqrel X R; is_eqrel Y S\<rbrakk> \<Longrightarrow> t \<in> (X \<times> Y)/(product_eqrel X R Y S) \<longleftrightarrow> (\<exists>t1 \<in> (X/R). \<exists>t2\<in>(Y/S). t= t1\<times>t2)"
  by (metis product_eqrel_memE6 product_eqrel_memE7)

lemma product_compatible:
  fixes f::"'a \<times> 'b \<Rightarrow> 'c" and X::"'a set" and Y::"'b set" and R::"'a rel" and S::"'b rel"
  defines "RS \<equiv> (product_eqrel X R Y S)" and "XY \<equiv> X \<times> Y"
  assumes "\<And>x1 x2 y1 y2. ((x1, y1), (x2, y2)) \<in> RS \<Longrightarrow> f (x1, y1) = f (x2, y2)"
  shows "is_eqr_compat XY RS f"
  using is_eqr_compatI1[of XY RS f] assms by blast


locale equivalence_relation=
  fixes X :: "'a set"
    and R :: "('a \<times> 'a) set"
  assumes is_eqrel:"is_eqrel X R"
begin
lemma relsub[intro,simp]:"R \<subseteq> X \<times> X"  by (simp add: eqrelE4b is_eqrel)
lemma refl[intro,simp]:"a \<in> X \<Longrightarrow> (a,a) \<in> R"  using eqrel_class3e is_eqrel by fastforce 
lemma symm[sym]:"(a,b) \<in> R  \<Longrightarrow> (b,a) \<in> R"  using is_eqrel is_eqrelE22 by auto  
lemma tran[trans]:"(a, b) \<in> R \<Longrightarrow> (b, c) \<in> R \<Longrightarrow> (a, c) \<in> R"  using eqrel_class3e is_eqrel by fastforce
lemma l_closed[intro]:  "(a, b) \<in> R \<Longrightarrow> a \<in> X"using relsub by blast
lemma r_closed[intro]:  "(a, b) \<in> R \<Longrightarrow> b \<in> X"using relsub by blast


definition proj where "proj \<equiv> canonical_proj X R"
definition psec where "psec \<equiv> proj_section X R"
lemma projE1:"x \<in> proj y \<Longrightarrow> y \<in> X \<Longrightarrow> x \<in> X" by (metis (no_types) canonical_proj_props7 is_eqrel local.proj_def r_closed)  
lemma projE2:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> proj x = proj y \<longleftrightarrow> (x, y) \<in> R" unfolding proj_def using is_eqrel canonical_proj_props5[of X R x y] by(simp)
lemma projE3:"x \<in> X \<Longrightarrow> proj x \<in> X/R"  by (simp add: canonical_proj_props1 is_eqrel local.proj_def)
lemma projE4:"x \<in> X \<Longrightarrow> y \<in> proj x \<Longrightarrow> (x, y) \<in> R" using canonical_proj_props7 is_eqrel local.proj_def by fastforce
lemma projE5:"(x, y) \<in> R \<Longrightarrow> y \<in> proj x" using canonical_proj_eq eqrelE4 is_eqrel local.proj_def by fastforce 
lemma psecE1:"t \<in> X/R \<Longrightarrow> proj (psec t) = t" by (simp add: is_eqrel local.proj_def proj_section3 psec_def)
lemma psecE2:"t \<in> X/R \<Longrightarrow> psec t \<in> X" by (simp add: is_eqrel proj_section2 psec_def)

end

locale set_partition=
  fixes X and P
  assumes subset: "P \<subseteq> Pow X"
    and nenm:"{} \<notin> P"
    and uneq:"\<Union>P = X"
    and disj:"\<lbrakk>A \<in> P; B \<in> P; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"


context equivalence_relation
begin
lemma partition:
  "set_partition X (X/R)"
  apply(unfold_locales)
  using is_eqrel quotient_un apply blast
  using is_eqrel proj_section4 apply auto[1]
  apply (simp add: is_eqrel quotient_un)
  using is_eqrel quotient_disj3 by blast

end

context set_partition begin

text \<open>p 12, ll 9--10\<close>
lemma eqc_exists:"a \<in> X \<Longrightarrow> \<exists>A. a \<in> A \<and> A \<in> P"  using uneq by blast
lemma eqc_unique: "\<lbrakk>a \<in> A; A \<in> P; a \<in> B; B \<in> P \<rbrakk> \<Longrightarrow> A = B" using disj by blast
lemma eqc_closed [intro]: "\<lbrakk> a \<in> A; A \<in> P \<rbrakk> \<Longrightarrow> a \<in> X" using uneq by blast
lemma element_exists:  "t \<in> P \<Longrightarrow> \<exists>x \<in> X. x \<in> t" by (metis eqc_closed ex_in_conv nenm)
definition proj where  "proj \<equiv> (\<lambda>a \<in> X. THE A. a \<in> A \<and> A \<in> P)"
lemma proj_closed [intro, simp]: assumes [intro]: "a \<in> X" shows "proj a \<in> P"
proof-
  obtain A where "a \<in> A" "A \<in> P" using eqc_exists by blast
  then show ?thesis   apply (auto simp: proj_def)  by (rule theI2,auto dest: eqc_unique)
qed
lemma eqc_undefined [intro, simp]:  "a \<notin> X \<Longrightarrow> proj a = undefined" unfolding proj_def by simp
lemma elem_in_eqc: "\<lbrakk>a \<in> A; A \<in> P\<rbrakk> \<Longrightarrow> proj a = A"
  apply (simp add: proj_def eqc_closed)
  apply (rule the_equality)
  by (auto dest: eqc_unique)

definition induced_eqr where "induced_eqr \<equiv> {(a, b) . \<exists>A \<in> P. a \<in> A \<and> b \<in> A}"

lemma induced_eqr_sub:"induced_eqr \<subseteq> X \<times> X" unfolding induced_eqr_def using eqc_closed by(auto)
lemma induced_eqr_is_eqr: "equivalence_relation  X induced_eqr"
  apply(unfold_locales)
  apply(auto simp add: is_eqrel_def)
  unfolding refl_on_def using induced_eqr_sub
  using eqc_exists induced_eqr_def apply force
  unfolding sym_def  using induced_eqr_def apply auto[1]
  unfolding trans_def induced_eqr_def using disj by(auto)
 
interpretation eq:equivalence_relation X induced_eqr by (rule induced_eqr_is_eqr)
theorem Class_is_Block:
  assumes "a \<in> X" shows "proj a = eq.proj a"
proof -
  from \<open>a \<in> X\<close> and eqc_exists obtain A where block: "a \<in> A \<and> A \<in> P" by blast
  show ?thesis
    apply (simp add: proj_def eq.proj_def)
    apply (rule theI2)
    apply (rule block)
    apply (metis block eqc_unique)
    apply (auto)
    using eq.projE5 eq.proj_def induced_eqr_def apply fastforce
    by (smt (verit) case_prodD elem_in_eqc eq.projE4 eq.proj_def induced_eqr_def mem_Collect_eq)  
qed

end


section MagmaLocale

definition magma_stable :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where  "magma_stable X f A \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A. f x y \<in> A) \<and> (A \<subseteq> X)"

locale magma=
  fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) 
  assumes closed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> X" 
begin
definition stable where  "stable A \<equiv> magma_stable X f A"
definition commutes where  "commutes A B \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B. a \<cdot> b = b \<cdot> a)"
definition centralizer where "centralizer E \<equiv> {x \<in> X. \<forall>y \<in> E. commutes {x} {y}}"
definition l_identity where "l_identity e \<equiv> (\<forall>x \<in>X. e \<cdot> x = x)"
definition r_identity where "r_identity e \<equiv> (\<forall>x \<in>X. x \<cdot> e = x)"
definition id_elem where "id_elem e \<equiv>(\<forall>x \<in>X. e \<cdot> x = x \<and> x \<cdot> e = x)"
definition l_trans where "l_trans \<equiv> (\<lambda>a \<in> X. \<lambda>x \<in> X. a \<cdot> x)"
definition r_trans where "r_trans \<equiv> (\<lambda>a \<in> X. \<lambda>x \<in> X. x \<cdot> a)"
lemma stableI:  "A \<subseteq> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> A) \<Longrightarrow> stable A" by (simp add: local.stable_def magma_stable_def)
lemma stableE1: "stable A \<Longrightarrow> A \<subseteq> X" by (simp add: local.stable_def magma_stable_def)
lemma stableE2:  "stable A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x\<cdot>y \<in> A" by (simp add: local.stable_def magma_stable_def)
lemma centralizer_antitone:  "A \<subseteq> B \<Longrightarrow> centralizer B \<subseteq> centralizer A" unfolding centralizer_def by blast
lemma id_elem_unique:"\<And>e1 e2. id_elem e1 \<Longrightarrow> id_elem e2 \<Longrightarrow>e1 \<in> X \<Longrightarrow> e2 \<in> X \<Longrightarrow>  e1 = e2" unfolding id_elem_def by auto
lemma id_commutes:"id_elem e \<Longrightarrow> e \<in> X \<Longrightarrow> commutes {e} X" unfolding id_elem_def commutes_def by(auto)
lemma l_trans_app:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> l_trans x y = r_trans y x" unfolding l_trans_def r_trans_def by(auto)
lemma l_trans_hom:"\<And>a. a \<in> X \<Longrightarrow> l_trans a \<in> hom X X" by (simp add: closed hom_memI1 l_trans_def)
lemma r_trans_hom:"\<And>a. a \<in> X \<Longrightarrow> r_trans a \<in> hom X X" by (simp add: closed hom_memI1 r_trans_def)
lemma id_elem_linj:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> inj_on (l_trans e) X " unfolding inj_on_def l_trans_def id_elem_def by(auto)
lemma id_elem_rinj:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> inj_on (r_trans e) X " unfolding inj_on_def r_trans_def id_elem_def by(auto)
end

section Submagma
locale submagma=magma X "(\<cdot>)" for A and X and magma_law (infixl "\<cdot>" 70)+  assumes submem:"A \<subseteq> X" and  subfun:"\<lbrakk>x \<in>A; y \<in> A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> A" 
begin
lemma sub[intro,simp]:"x \<in> A \<Longrightarrow> x \<in> X" using submem by auto
sublocale sub:magma A "(\<cdot>)" by (simp add: magma.intro subfun) 
end
lemma submamga_trans: assumes "submagma A B f" and "submagma B C f"  shows "submagma A C f" proof- interpret A: submagma A B f by fact  interpret C: submagma B C f by fact  show ?thesis  by (simp add: A.subfun C.magma_axioms submagma.intro submagma_axioms_def subset_iff)  qed
lemma submagmaI:"magma X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (f x y) \<in> A) \<Longrightarrow> submagma A X f"  by (simp add: submagma.intro submagma_axioms.intro subsetD)
locale unital_magma=magma+ fixes e assumes idin:"e \<in> X" and lid:"x \<in> X \<Longrightarrow> e \<cdot> x = x" and rid:"x \<in> X \<Longrightarrow> x \<cdot> e = x"
begin
lemma islid:"l_identity e" by (simp add: l_identity_def lid)
lemma isrid:"r_identity e" by (simp add: r_identity_def rid)
lemma isid:"id_elem e"  by (simp add: id_elem_def lid rid)
end

section HomomorphismLocale
locale magma_homomorphism=set_morphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) +
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin

lemma imag_comp:"submagma A X (\<cdot>) \<Longrightarrow> x \<in> f ` A \<Longrightarrow> y \<in> f ` A \<Longrightarrow> x \<star> y \<in> f ` A"
proof-
  fix x y assume A0:"submagma A X (\<cdot>)" "x \<in> f ` A" "y \<in> f `A" then obtain a b where A1:"a \<in> A" "b \<in> A" "x = f a" "y = f b"  by blast
  then obtain "a\<cdot>b \<in> A" by (meson A0 submagma.subfun) 
  then obtain "f (a \<cdot>b) \<in> f `A" and  "f (a \<cdot> b) = (f a)\<star>(f b)" by (meson A0(1) A1(1) A1(2) cmp imageI submagma.sub) 
  then show "x \<star> y \<in> f ` A"  by (simp add: A1(3) A1(4)) 
qed

lemma submagma1:"submagma A X (\<cdot>) \<Longrightarrow> submagma (f`A) Y (\<star>)" 
  apply(unfold_locales)
  apply (simp add: image_subsetI submagma.sub)
  using imag_comp by blast

lemma submagma12:"submagma B Y (\<star>) \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow>submagma (vimage f B) X (\<cdot>)" 
proof-
  assume A0:"submagma B Y (\<star>)" and A1:"(vimage f B) \<subseteq> X"
  then show "submagma (vimage f B) X (\<cdot>)"
  apply(unfold_locales)
  using A1 apply blast
  by (simp add: cmp submagma.subfun subset_eq)
qed
end

locale magma_epimorphism=set_epimorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
end
locale magma_monomorphism=set_monomorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
end

locale magma_isomorphism=set_isomorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
sublocale magma_epimorphism by(unfold_locales,simp add: cmp)
sublocale magma_monomorphism by(unfold_locales,simp add: cmp)
end

     
section QuotientMagma

definition l_cong::"'a set\<Rightarrow>('a\<Rightarrow>'b\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where "l_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f a x, f a y) \<in> R)"
definition r_cong::"'a set\<Rightarrow>('b\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where "r_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f x a, f y a) \<in> R)"
definition cong::"'a set\<Rightarrow>('a\<Rightarrow>'a\<Rightarrow>'a)\<Rightarrow>('a\<times>'a) set \<Rightarrow> bool" where "cong X f R \<equiv> (\<forall>(x1, x2) \<in> R. \<forall>(y1, y2) \<in> R.  (f x1 y1, f x2 y2) \<in> R)"

lemma l_congI1:"(\<And>a x y. a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R) \<Longrightarrow> l_cong X f R" using l_cong_def by fastforce
lemma r_congI1:"(\<And>a x y. a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R) \<Longrightarrow> r_cong X f R" using r_cong_def by fastforce
lemma congI1:"(\<And>x1 x2 y1 y2. (x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (f x1 y1 , f x2 y2) \<in> R) \<Longrightarrow> cong X f R" using cong_def by fastforce

lemma l_congD1:"l_cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R" using l_cong_def by fastforce
lemma r_congD1:"r_cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R" using r_cong_def by fastforce
lemma congDR:"refl_on X R \<Longrightarrow> cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R"  proof-  assume A0:"refl_on X R" "cong X f R" "a \<in> X" "(x,y)\<in>R"  then have B0:"(a,a)\<in>R"   by (simp add: refl_onD)  then show "(f x a, f y a) \<in> R"  using A0 cong_def by fastforce qed
lemma congDL:"refl_on X R \<Longrightarrow> cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R"  proof-  assume A0:"refl_on X R" "cong X f R" "a \<in> X" "(x,y)\<in>R"  then have B0:"(a,a)\<in>R"   by (simp add: refl_onD)  then show "(f a x, f a y) \<in> R"  using A0 cong_def by fastforce qed
lemma l_congI2:"equivalence_relation X R \<Longrightarrow> cong X f R \<Longrightarrow>l_cong X f R"  by (metis congDL equivalence_relation.is_eqrel is_eqrel_def l_congI1)  
lemma r_congI2:"equivalence_relation X R \<Longrightarrow> cong X f R \<Longrightarrow>r_cong X f R"  by (metis congDR equivalence_relation.is_eqrel is_eqrel_def r_congI1)  
lemma congI2:"equivalence_relation X R \<Longrightarrow> l_cong X f R \<Longrightarrow> r_cong X f R \<Longrightarrow> cong X f R"
proof- 
  assume A0:"equivalence_relation X R" "l_cong X f R" "r_cong X f R"
  show "cong X f R"
  proof(rule congI1)
    fix x1 x2 y1 y2 assume A1:"(x1, x2) \<in> R" "(y1, y2) \<in> R" 
    then obtain B0:"x1 \<in> X" "x2 \<in> X""y1 \<in> X" "y1 \<in> X"  by (meson A0(1) eqrelE4 equivalence_relation_def)
    then obtain "(f x1 y1, f x1 y2) \<in> R" and "(f x1 y2, f x2 y2) \<in> R"  by (meson A0 A1 eqrelE4 equivalence_relation_def l_congD1 r_congD1)
    then show "(f x1 y1, f x2 y2) \<in> R" using A0 eqrel_class3e equivalence_relation.is_eqrel by fastforce
  qed
qed

locale quotient_magma=
  magma X "(\<cdot>)" + 
  equivalence_relation X R
  for X::"'a set" and 
      f:: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70) and 
      R::"'a rel"+
  assumes compatible:"(x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (x1\<cdot>y1 , x2\<cdot>y2) \<in> R"
begin
definition quotient_law  (infixl "\<bullet>" 70) where "quotient_law \<equiv> (\<lambda>t \<in> X/R. \<lambda>s \<in> X/R.  proj (f (psec t) (psec s)))"
lemma op_compat1:"proj x1 = proj x2 \<Longrightarrow>proj y1 = proj y2 \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> y1 \<in> X \<Longrightarrow> y2 \<in> X \<Longrightarrow> proj (x1 \<cdot>y1) = proj (x2 \<cdot> y2)"  by (simp add: closed compatible projE2)
lemma left_compatible:"a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (a\<cdot>x, a\<cdot>y) \<in> R" using compatible projE2 by blast
lemma right_compatible:"a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (x\<cdot>a, y\<cdot>a) \<in> R" using compatible projE2 by blast
lemma left_trans_compat:"\<And>a. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (l_trans a x, l_trans a y)\<in>R"  by (simp add: compatible l_closed l_trans_def r_closed)
lemma right_trans_compat:"\<And>a. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (r_trans a x, r_trans a y)\<in>R" by (simp add: compatible r_closed r_trans_def l_closed)
lemma psecE3:"t \<in> X/R \<Longrightarrow> s \<in> X/R \<Longrightarrow> f (psec t) (psec s) \<in> X" using closed psecE2 by blast
lemma qlaw1:"t \<in> X/R \<Longrightarrow> s \<in> X/R  \<Longrightarrow> t\<bullet>s \<in> X/R"  by (simp add: closed projE3 psecE2 quotient_law_def restrict_def)
lemma qlaw2: assumes mem:"x1 \<in> X" "x2 \<in> X"  and rel:"y1 \<in> proj x1" "y2 \<in> proj x2" shows "y1\<cdot>y2 \<in> proj (x1 \<cdot> x2)"  by (simp add: compatible mem projE4 projE5 rel)
lemma qlaw3:  assumes mem:"x \<in> X" "y \<in> X" shows "(proj x)\<bullet>proj(y) = proj(x \<cdot> y)"
proof- 
  let ?t="(proj x)" and ?s="(proj y)"  
  obtain a b where A0:"a \<in> X" and A1:"b \<in> X" and "a = psec ?t" and "b = psec ?s" and "proj a = ?t" and "proj b = ?s" by (simp add: mem projE3 psecE1 psecE2)
  then obtain B0:"psec (proj a) = a"  "psec  (proj b) = b"  "proj x = proj a"  "proj y = proj b"  by force
  have "(proj x)\<bullet>proj(y) =  proj (f (psec (proj x)) (psec (proj y)))"   by (simp add: mem projE3 quotient_law_def restrict_def)
  also have "... = proj (a\<cdot>b)"    by(simp add:B0)
  also have "... = proj (x \<cdot> y)"   using B0(3,4)  A0 A1 mem op_compat1 by blast
  finally show ?thesis  by blast
qed

sublocale quotient: magma "X/R" quotient_law  by (simp add: magma.intro qlaw1)
lemma proj_homomorphism:"magma_homomorphism proj X f (X/R) quotient_law" apply(unfold_locales)
  apply (simp add: canonical_proj_def local.proj_def)
  apply (simp add: projE3)
  by (simp add: qlaw3) 
lemma proj_hom:"proj \<in> hom X (X/R)"  by (metis (no_types, lifting) canonical_proj_def hom_memI1 local.proj_def projE3 restrict_apply)
sublocale proj:magma_homomorphism proj X f "(X/R)" quotient_law  by (simp add: proj_homomorphism) 
end

lemma quotient_magmaI:
  fixes X::"'a set" and R::"'a rel" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70)
  assumes A0:"magma X (\<cdot>)" and A1:"equivalence_relation X R" and
         lc:"\<And>a x y. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (a\<cdot>x, a\<cdot>y)\<in>R" and
         rc:"\<And>a x y. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (x\<cdot>a, y\<cdot>a)\<in>R"
  shows compatible:"\<And>x1 x2 y1 y2. (x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (x1\<cdot>y1 , x2\<cdot>y2) \<in> R"
proof -
  fix x1 x2 y1 y2 assume x1Rx2: "(x1, x2) \<in> R" assume y1Ry2: "(y1, y2) \<in> R"
  obtain B0:"x1 \<in> X" and B1:"y2 \<in> X"  by (metis A1 eqrelE4 equivalence_relation.is_eqrel x1Rx2 y1Ry2)
  have B2: "R `` {x1 \<cdot> y1} = R `` {x1 \<cdot> y2} \<and> x1 \<cdot> y1 \<in> X \<and> x1 \<cdot> y2 \<in> X"  by (meson A1 B0 eqrel_class3e equivalence_relation_def lc y1Ry2)
  have B3:"R `` {x1 \<cdot> y2} = R `` {x2 \<cdot> y2} \<and> x1 \<cdot> y2 \<in> X \<and> x2 \<cdot> y2 \<in> X"  by (meson A1 B1 eqrel_class3e equivalence_relation.is_eqrel rc x1Rx2)
  then show "(x1 \<cdot> y1, x2 \<cdot> y2) \<in> R"  using A1 eqrel_class3e equivalence_relation.is_eqrel B2 by fastforce
qed

lemma quotient_magmaI12:
  fixes X::"'a set" and R::"'a rel" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70)
  assumes A0:"magma X (\<cdot>)" and A1:"equivalence_relation X R" and A2:"cong X f R"
  shows "quotient_magma X f R"
  using A0 A1 A2 cong_def quotient_magma.intro quotient_magma_axioms_def by fastforce

lemma quotient_magmaI13:
  fixes X::"'a set" and R::"'a rel" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70)
  assumes A0:"magma X (\<cdot>)" and A1:"equivalence_relation X R" and A2:"l_cong X f R"  and  A3:"r_cong X f R"
  shows "quotient_magma X f R"
  by (simp add: assms congI2 quotient_magmaI12)

lemma quotiet_magma_magma:"quotient_magma X f R \<Longrightarrow> magma (X/R) (quotient_magma.quotient_law X f R)" by (simp add: magma.intro quotient_magma.qlaw1)
lemma quotiet_magma_hom:"quotient_magma X f R \<Longrightarrow> magma_homomorphism (equivalence_relation.proj X R) X f (X/R) (quotient_magma.quotient_law X f R)"  by (simp add: quotient_magma.proj_homomorphism) 

section Semigroup
locale semigroup=magma+
  assumes associative[ac_simps]:"\<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
begin
definition l_cancel where "l_cancel a \<equiv> inj_on (l_trans a) X"
definition r_cancel where "r_cancel a \<equiv> inj_on (r_trans a) X"
definition b_cancel where "b_cancel a \<equiv> inj_on (l_trans a) X \<and> inj_on (r_trans a) X"

lemma associate2: "\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (x\<cdot>y)\<cdot>z = x \<cdot> y \<cdot> z" by simp
lemma associate3:  assumes mem:"x \<in> X" "y \<in> X""z \<in> X" and xy:"x \<cdot> y = y \<cdot> x"  shows "x\<cdot>(y\<cdot>z) = (y\<cdot>x)\<cdot>z" 
proof- have " x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z " by (simp add: mem associative)  also have "... = (y \<cdot> x) \<cdot> z"  by (simp add: xy)  finally show ?thesis by simp qed
lemma commutes_assoc:
  assumes mem:"x \<in> X" "y \<in> X""z \<in> X" and xy:"x \<cdot> y = y \<cdot> x" and xz:"x \<cdot> z = z \<cdot> x" 
  shows " x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x"
proof-
  have " x\<cdot>(y\<cdot>z) = (y\<cdot>x)\<cdot>z" by (simp add: associate3 mem xy)
  also have "... = (y \<cdot> z) \<cdot> x" by (simp add: associative mem xz)
  finally show ?thesis by simp
qed
lemma assoc4:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X;d\<in>X\<rbrakk> \<Longrightarrow> (a\<cdot>b)\<cdot>(c\<cdot>d) = a\<cdot>(b\<cdot>c)\<cdot>d" using associative closed by auto

lemma ltranslation_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>  \<Longrightarrow> compose X (l_trans x) (l_trans y) z = l_trans (x \<cdot> y) z"  by (simp add: associative closed compose_def l_trans_def)
lemma rtranslation_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>  \<Longrightarrow> compose X (r_trans y) (r_trans x) z = r_trans (x \<cdot> y) z"  by (simp add: associative closed compose_def r_trans_def) 
lemma ltranslation_comp:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans x) (l_trans y) = l_trans (x \<cdot> y)"
  using fun_eqI[of "compose X (l_trans x) (l_trans y)" X X "l_trans (x \<cdot> y)" X]
  by (metis closed hom2 l_trans_hom ltranslation_comp1)
lemma rtranslation_comp:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans y) (r_trans x) = r_trans (x \<cdot> y)"
  using fun_eqI[of "compose X (r_trans y) (r_trans x)" X X "r_trans (x \<cdot> y)" X]
  by (metis closed hom2 r_trans_hom rtranslation_comp1)


lemma l_cancelI: "(\<And>x y. \<lbrakk>x \<in> X; y \<in> X;  (l_trans a) x =  (l_trans a) y\<rbrakk> \<Longrightarrow> x =y) \<Longrightarrow> l_cancel a "  unfolding l_cancel_def inj_on_def by auto 
lemma r_cancelI: "(\<And>x y. \<lbrakk>x \<in> X; y \<in> X;  (r_trans a) x =  (r_trans a) y\<rbrakk> \<Longrightarrow> x =y) \<Longrightarrow> r_cancel a "  unfolding r_cancel_def inj_on_def by auto 
lemma b_cancelI: "r_cancel a \<Longrightarrow> l_cancel a  \<Longrightarrow> b_cancel a " by (simp add: b_cancel_def l_cancel_def r_cancel_def) 
lemma id_cancel:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> b_cancel e"by (simp add: b_cancel_def id_elem_linj id_elem_rinj)
lemma id_elem_id_map:
  assumes is_mem:"e \<in> X" and is_id:"id_elem e"
  shows "l_trans e = Id X" and "r_trans e = Id X" 
proof-
  obtain idhom:"Id X \<in> hom X X" and lhom:"l_trans e \<in> hom X X" and rhom:"r_trans e \<in> hom X X"  using hom7[of X] l_trans_hom[of e] r_trans_hom[of e] is_mem by auto
  show " l_trans e = Id X" using lhom idhom  proof(rule fun_eqI)  show "\<And>x. x \<in> X \<Longrightarrow> l_trans e x = Id X x" using id_elem_def is_id is_mem l_trans_def by auto qed
  show " r_trans e = Id X" using rhom idhom  proof(rule fun_eqI) show "\<And>x. x \<in> X \<Longrightarrow> r_trans e x = Id X x" using id_elem_def is_id is_mem r_trans_def by auto qed
qed

lemma all_invertibleRI:
  assumes emem:"e \<in> X" and rid:"r_identity e" and rinvs:"\<And>x. x \<in> X \<Longrightarrow> (\<exists>y. y \<in> X \<and> x \<cdot>y = e)"
  shows "\<And>x. x \<in> X \<Longrightarrow> (\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)" and  "id_elem e" 
proof-
  show  "\<And>x. x \<in> X \<Longrightarrow> (\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)"
  proof-
    fix x assume xmem:"x \<in> X"
    then obtain y where ymem:"y \<in> X" and rinvy:"x \<cdot> y = e" using emem rinvs[of x] by blast
    then obtain z where zmem:"z \<in> X" and rinvz:"y \<cdot> z = e" using emem rinvs[of y] by blast
    have "y \<cdot> x = (y \<cdot> x) \<cdot> e" using closed rid xmem ymem unfolding r_identity_def by auto
    also have "... = (y \<cdot> x) \<cdot> (y \<cdot> z)"  by (simp add: rinvz)
    also have "... = y \<cdot> (x \<cdot> y \<cdot> z)"   using associative calculation r_identity_def rid rinvz xmem ymem zmem by auto
    also have "... = y \<cdot> (e \<cdot> z)" by (simp add: rinvy)
    also have "... = (y \<cdot>e ) \<cdot> z"    by (simp add: associative emem ymem zmem) 
    also have "... = e"  using r_identity_def rid rinvz ymem by force
    finally have "x \<cdot> y = e \<and> y \<cdot> x = e"
      by (simp add: rinvy)
    then show "(\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)"
      using ymem by auto
  qed
  then show "id_elem e"   using associative id_elem_def r_identity_def rid by fastforce
qed
  

lemma all_invertibleLI:
  assumes emem:"e \<in> X" and lid:"l_identity e" and linvs:"\<And>x. x \<in> X \<Longrightarrow> (\<exists>y. y \<in> X \<and> y \<cdot>x = e)"
  shows "\<And>x. x \<in> X \<Longrightarrow> (\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)" and  "id_elem e" 
proof-
  show  "\<And>x. x \<in> X \<Longrightarrow> (\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)"
  proof-
    fix x assume xmem:"x \<in> X"
    then obtain y where ymem:"y \<in> X" and linvy:"y \<cdot> x = e" using emem linvs[of x] by blast
    then obtain z where zmem:"z \<in> X" and linvz:"z \<cdot> y = e" using emem linvs[of y] by blast
    have "x\<cdot>y = e\<cdot>(x\<cdot>y)" using closed lid xmem ymem unfolding l_identity_def by auto
    also have "... = (z\<cdot>y)\<cdot>(x\<cdot>y)"  by (simp add: linvz)
    also have "... = z\<cdot>(y\<cdot>x\<cdot>y)"  by (simp add: associative closed xmem ymem zmem)  
    also have "... = z\<cdot>(e\<cdot>y)" by (simp add: linvy)
    also have "... = z\<cdot>y"   using l_identity_def lid ymem by auto  
    also have "... = e"  using l_identity_def lid linvz ymem by force
    finally have "x \<cdot> y = e \<and> y \<cdot> x = e"    by (simp add: linvy)
    then show "(\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)"
      using ymem by auto
  qed
  then show "id_elem e"   using associative id_elem_def l_identity_def lid by fastforce
qed
  

end


section QuotientSemigroup
locale quotient_semigroup=semigroup X "(\<cdot>)"  + quotient_magma X "(\<cdot>)" R for X::"'a set" and f (infixl "\<cdot>" 70) and R
begin
print_facts
lemma qassociative1: assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"z \<in> X" shows "((proj x)\<bullet>(proj y))\<bullet>(proj z) = (proj x)\<bullet>((proj y)\<bullet>(proj z))" by (simp add: A0 A1 A2 associative closed qlaw3)
lemma qassociate2: assumes A0:"t \<in> X / R"  and A1:"s \<in> X / R" and A2 :"r \<in> X / R"  shows  "(t\<bullet>s)\<bullet>r = t\<bullet>(s\<bullet>r)"  by (metis (full_types) A0 A1 A2 psecE1 psecE2 qassociative1)
sublocale quotient:semigroup "X/R" "(\<bullet>)" using semigroup.intro qassociate2 quotient.magma_axioms semigroup_axioms_def by blast

end

locale comm_locale=fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "(\<cdot>)" 70)  assumes commutative:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow>x\<cdot>y = y\<cdot>x"


locale comm_semigroup=semigroup X "(\<cdot>)"+comm_locale X "(\<cdot>)" for X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
begin
lemma lcom:"\<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow> y\<cdot>(x\<cdot>z) = x \<cdot> (y \<cdot> z) "  by (metis associative commutative)
end


section Monoid
locale monoid=semigroup+fixes unit ("e")   assumes idmem:"e\<in>X" and  leftid:"x \<in> X \<Longrightarrow> e \<cdot> x = x" and  rightid:"x \<in> X \<Longrightarrow> x \<cdot> e = x"
begin
lemma monoidI2:"semigroup X f \<Longrightarrow> e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x \<and> x \<cdot> e = x) \<Longrightarrow> monoid X f e" using monoid_axioms by blast
lemma ltranslation_id:"l_trans e = Id X "  by (simp add: id_elem_def id_elem_id_map(1) idmem leftid rightid)
lemma rtranslation_id:"r_trans e = Id X "  by (simp add: id_elem_def id_elem_id_map(2) idmem leftid rightid)
end
section Submonoid
locale submonoid=monoid X "(\<cdot>)" e   for A and X and f (infixl "\<cdot>" 70) and unit ("e") + assumes setsub:"A \<subseteq> X" and   opsub:"\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A" and   idsub:"e \<in> A"
begin
lemma subD[intro,simp]:"a \<in> A \<Longrightarrow> a \<in> X" using setsub by auto  
sublocale sub:monoid A "(\<cdot>)" e by (simp add: monoid_axioms_def monoid_def semigroup.intro associative idsub leftid magma_def opsub rightid semigroup_axioms_def)
end
lemma submonoid_submagma:"submonoid A X f e \<Longrightarrow> submagma A X f"  by (simp add: monoid_def semigroup.axioms(1) submagmaI submonoid.opsub submonoid.setsub submonoid_def)
lemma submonoidI:"monoid X f e \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (f x y) \<in> A) \<Longrightarrow> e \<in> A \<Longrightarrow> submonoid A X f e" by (simp add: submonoid.intro submonoid_axioms.intro) 
lemma submonoid_transitive:  assumes "submonoid A B f e" and "submonoid B C f e" shows "submonoid A C f e" proof-  interpret A: submonoid A B f e by fact  interpret B: submonoid B C f e by fact show ?thesis   by (simp add: A.opsub A.sub.idmem B.monoid_axioms submonoidI subset_eq) qed


locale hom_monoid=
  magma_homomorphism f X "(\<cdot>)" Y "(\<star>)"+
  dom:monoid X "(\<cdot>)" e +
  cod:monoid Y "(\<star>)" i for
  X::"'a set"and  domain_law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and domain_identity ("e") and
  Y::"'b set" and codomain_law::"'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<star>" 70) and codomain_identity ("i") and 
  f::"'a \<Rightarrow> 'b"+assumes
  unital:"f e = i"




lemma composition_monoid:"monoid (hom X X) (compose X) (Id X)"by(unfold_locales, auto simp add:hom2 hom3 hom5 hom6 hom7)

section CompositionMonoid
locale compositional_monoid =submonoid M "hom E E" "compose E" "Id E" for M and E
begin
lemma hom_mem:"f \<in> M \<Longrightarrow> f \<in> hom E E" using subD by blast
lemma eval_simp[intro, simp]:"f \<in> M  \<Longrightarrow> x \<in> E \<Longrightarrow> f x \<in> E" by(auto intro:  hom9)
lemma eval_ndef[intro,simp]:"f \<in> M \<Longrightarrow> x \<notin> E \<Longrightarrow> f x = undefined" using hom10 by fastforce
end

section InversionInMonoids
context monoid begin
definition invertible where "u \<in> X \<Longrightarrow> invertible u \<longleftrightarrow> (\<exists>v \<in> X. u \<cdot> v = e \<and> v \<cdot> u = e)"
definition inv_elem where "inv_elem = (\<lambda>u \<in> X. THE v. v \<in>X \<and> u \<cdot> v = e \<and> v \<cdot> u = e)"

lemma invertibleI [intro]:  "\<lbrakk> u \<cdot> v = e; v \<cdot> u = e; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> invertible u" unfolding invertible_def by fast
lemma invertibleE [elim]: "\<lbrakk>invertible u; \<And>v. \<lbrakk> u \<cdot> v = e; v \<cdot> u = e; v \<in> X \<rbrakk> \<Longrightarrow> P; u \<in> X\<rbrakk> \<Longrightarrow> P"  unfolding invertible_def by fast
lemma inverse_unique:  "\<lbrakk>u \<cdot> v' =e; v \<cdot> u = e; u \<in> X;  v \<in> X; v' \<in> X \<rbrakk> \<Longrightarrow> v = v'" by (metis associative leftid rightid)
lemma inverse_equality:  "\<lbrakk>u \<cdot> v = e; v \<cdot> u = e; u \<in> X; v \<in> X \<rbrakk> \<Longrightarrow> inv_elem u = v" unfolding inv_elem_def using inverse_unique by simp blast

lemma invertible_inverse_closed [intro, simp]: "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv_elem u \<in> X" using inverse_equality by auto
lemma inverse_undefined [intro, simp]:  "u \<notin> X \<Longrightarrow> inv_elem u = undefined"  by (simp add: inv_elem_def)
lemma invertible_left_inverse [simp]: "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv_elem u \<cdot> u = e" using inverse_equality by auto

lemma invertible_right_inverse [simp]:  "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> u \<cdot> inv_elem u = e"  using inverse_equality by auto
lemma invertible_left_cancel [simp]:  "\<lbrakk> invertible x; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow> x \<cdot> y = x \<cdot> z \<longleftrightarrow> y = z" by (metis associative invertible_def leftid)
lemma invertible_right_cancel [simp]:  "\<lbrakk> invertible x; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow> y \<cdot> x = z \<cdot> x \<longleftrightarrow> y = z"  by (metis associative invertible_def rightid)
lemma inv_ident [simp]: "inv_elem e = e"  using inverse_equality idmem leftid by blast
lemma invertible_inverse_invertible [intro, simp]:  "\<lbrakk> invertible u; u \<in> X\<rbrakk> \<Longrightarrow> invertible (inv_elem u)"  using invertible_left_inverse invertible_right_inverse by blast
lemma invertible_inverse_inverse [simp]:  "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv_elem (inv_elem u) = u" by (simp add: inverse_equality)

lemma invprod:assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"invertible x" and A3:"invertible y" 
  shows "invertible (x \<cdot> y)" and "inv_elem (x \<cdot> y) = (inv_elem y) \<cdot> (inv_elem x )"
proof-
  let ?a="inv_elem x" let  ?b="inv_elem y" let ?u="x \<cdot> y" let ?v="?b \<cdot> ?a"
  have "?u \<cdot> ?v = e"  by (simp add: associate3 associative closed leftid A0 A1 A2 A3)
  also have  "?v \<cdot> ?u = e"  by (metis A0 A1 A2 A3 associative closed invertible_inverse_closed invertible_left_inverse rightid)
  then show "inv_elem (x \<cdot> y) = (inv_elem y) \<cdot> (inv_elem x) "  by (simp add: A0 A1 A2 A3 calculation closed inverse_equality)
  then show "invertible (x \<cdot> y)"
    using A0 A1 A2 A3 \<open>inv_elem (y::'a) \<cdot> inv_elem (x::'a) \<cdot> (x \<cdot> y) = e\<close> calculation closed invertibleI invertible_inverse_closed by presburger
qed

lemma invid:"invertible e" using idmem rightid by auto
lemma inv_right_cancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> (inv_elem x \<cdot> y) = y" by (simp add: associate3 leftid)
lemma inv_left_cancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv_elem x \<cdot> (x \<cdot> y) = y" by (metis associative invertible_inverse_closed invertible_left_inverse leftid) 

lemma l_trans_inv1:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans x) (l_trans (inv_elem x)) = Id X"  by (simp add: ltranslation_comp ltranslation_id)
lemma l_trans_inv2:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans (inv_elem x)) (l_trans x) = Id X"  by (simp add: ltranslation_comp ltranslation_id) 

lemma r_trans_inv1:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans x) (r_trans (inv_elem x)) = Id X"  by (simp add: rtranslation_comp rtranslation_id) 
lemma r_trans_inv2:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans (inv_elem x)) (r_trans x) = Id X"  using rtranslation_comp rtranslation_id by auto 

end

section InversionInSubmonoids
context submonoid begin
lemma submonoid_invertible [intro, simp]:  "\<lbrakk> sub.invertible u; u \<in> A \<rbrakk> \<Longrightarrow> invertible u"  using invertibleI by blast
lemma submonoid_inverse_closed [intro, simp]:  "\<lbrakk> sub.invertible u; u \<in> A \<rbrakk> \<Longrightarrow> inv_elem u \<in> A"using inverse_equality by auto
end

locale quotient_monoid=
  monoid X "(\<cdot>)" e + 
  quotient_semigroup X "(\<cdot>)" R for
  X::"'a set" and
  f::"'a \<Rightarrow> 'a \<Rightarrow>'a" (infixl "\<cdot>" 70) and
  R::"('a \<times> 'a) set" and
  e::"'a"
begin

lemma quotient_lid:"\<And>t. t \<in> X / R \<Longrightarrow> (proj e) \<bullet> t = t" by (metis idmem leftid proj.cmp psecE1 psecE2)
lemma quotient_rid:"\<And>t. t \<in> X / R \<Longrightarrow> t \<bullet> (proj e) = t" by (metis idmem rightid proj.cmp psecE1 psecE2)
sublocale quotient: monoid "X/R" "(\<bullet>)" "proj e" by(unfold_locales, simp add: idmem, simp add: quotient_lid,simp add: quotient_rid)
end

section Group
locale group = 
  monoid X "(\<cdot>)" e for X and f (infixl "\<cdot>" 70) and unit ("e") + 
  assumes invertible [simp, intro]: "u \<in> X \<Longrightarrow> invertible u"
begin
lemma groupI:"(\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow>  (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)) \<Longrightarrow> e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x \<and> x \<cdot> e = x) \<Longrightarrow>(\<And>x. x \<in> X \<Longrightarrow> invertible x) \<Longrightarrow>  group X f e" using group_axioms by blast 
lemma left_cancellation:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X; a\<cdot>x=a\<cdot>y\<rbrakk> \<Longrightarrow> x = y " by simp
lemma right_cancellation:"\<lbrakk>b \<in> X; x \<in> X; y \<in> X;x\<cdot>b=y\<cdot>b\<rbrakk> \<Longrightarrow> x = y " by simp
lemma double_inv_prod:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> inv_elem (a \<cdot> inv_elem b) \<in> X" using closed by fastforce
lemma insert_id1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (c \<cdot> inv_elem c) \<cdot>b " using rightid by fastforce 
lemma insert_id2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (inv_elem c \<cdot> c) \<cdot>b " using rightid by fastforce 
lemma remove_id1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> (a \<cdot> inv_elem c) \<cdot> (c \<cdot> b) = a \<cdot>b " by (simp add: assoc4 rightid)
lemma remove_id2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> (a \<cdot> c) \<cdot> (inv_elem c \<cdot> b) = a \<cdot>b " by (simp add: assoc4 rightid)
end

section Monoid_subgroup
locale monoid_subgroup= submonoid A X "(\<cdot>)" e + sub: group A "(\<cdot>)" e for A and X and f (infixl "\<cdot>" 70) and unit ("e")
begin
lemma monoid_subgroup_inverse_equality [simp]:  "u \<in> A \<Longrightarrow> inv_elem u = sub.inv_elem u" by (simp add: inverse_equality)
lemma monoid_subgroup_inverse_iff [simp]: "\<lbrakk>invertible x; x \<in> X \<rbrakk> \<Longrightarrow> inv_elem x \<in> A\<longleftrightarrow> x \<in> A"using invertible_inverse_inverse sub.invertible_inverse_closed by fastforce
end 

lemma monoid_subgroup_transitive [trans]:  assumes "monoid_subgroup K H f e" and "monoid_subgroup H G f e" shows "monoid_subgroup K G f e" proof- interpret K: monoid_subgroup K H f e by fact  interpret H: monoid_subgroup H G f e by fact show ?thesis  by (meson H.submonoid_axioms K.sub.group_axioms K.submonoid_axioms monoid_subgroup.intro submonoid_transitive)  qed
lemma monoid_subgroup_submonoid:"monoid_subgroup H G f e \<Longrightarrow> submonoid H G f e" by (simp add: monoid_subgroup.axioms(1))  

context monoid begin
lemma monoid_subgroupI:" submonoid H X f e \<Longrightarrow> e \<in> H \<Longrightarrow> (\<And>x. x \<in> H \<Longrightarrow>  monoid.invertible H (\<cdot>) e x)  \<Longrightarrow> (\<And>x. x \<in> H \<Longrightarrow> inv_elem  x \<in> H) \<Longrightarrow> monoid_subgroup H X f e" 
  apply(unfold_locales)
  apply (simp add: submonoid.setsub)
  apply (simp add: submonoid.opsub)
  apply blast
  apply (meson associative submonoid.subD)
  apply (metis leftid submonoid.subD)
  apply (simp add: rightid submonoid.subD)
  by blast

definition "Units = {u \<in> X. invertible u}"
lemma mem_UnitsI: "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> u \<in> Units"  unfolding Units_def by clarify
lemma mem_UnitsD:  "\<lbrakk> u \<in> Units \<rbrakk> \<Longrightarrow> invertible u \<and> u \<in> X"  unfolding Units_def by clarify

lemma monoid_subgroupI2:
  fixes A
  assumes subset [THEN subsetD, intro]: "A \<subseteq> X"
    and [intro]: "e \<in> A"
    and [intro]: "\<And>g h. \<lbrakk> g \<in> A; h \<in> A\<rbrakk> \<Longrightarrow> g \<cdot> h \<in> A"
    and [intro]: "\<And>g. g \<in> A \<Longrightarrow> invertible g"
    and [intro]: "\<And>g. g \<in> A \<Longrightarrow> inv_elem g \<in> A"
  shows "monoid_subgroup A X (\<cdot>) e"
proof -
interpret sub: monoid A "(\<cdot>)" e  by (simp add: monoid_axioms_def monoid_def semigroup.intro assms(2) assms(3) associative leftid magma_def rightid semigroup_axioms_def subset)
  show ?thesis
  apply(unfold_locales)
  apply (simp add: assms(1))
  apply (simp add: assms(3))
  apply (simp add: sub.idmem)
  using invertible_left_inverse invertible_right_inverse by blast
qed

interpretation units: monoid_subgroup Units X f e
  apply(rule monoid_subgroupI2)
  using mem_UnitsD apply blast
  using idmem leftid mem_UnitsI apply blast
  apply (metis closed invprod(1) mem_UnitsD mem_UnitsI)
  using mem_UnitsD apply auto[1]
  using mem_UnitsD mem_UnitsI by blast

lemma group_of_units:"group Units f e" by (simp add: units.sub.group_axioms)

lemma composition_invertible [simp, intro]:  "\<lbrakk> invertible x; invertible y; x \<in> X; y \<in>X \<rbrakk> \<Longrightarrow> invertible (x \<cdot> y)" using invprod(1) by presburger 
lemma invertible_right_inverse2:  "\<lbrakk> invertible u; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> u \<cdot> ((inv_elem u) \<cdot> v) = v"  using inv_right_cancel by blast
lemma invertible_left_inverse2: "\<lbrakk> invertible u; u \<in> X; v\<in>X\<rbrakk> \<Longrightarrow> (inv_elem u) \<cdot> (u \<cdot> v) = v" by (simp add: monoid.inv_left_cancel monoid_axioms)
lemma inverse_composition_commute: assumes [simp]: "invertible x" "invertible y" "x \<in> X" "y \<in> X"  shows "inv_elem (x \<cdot> y) = inv_elem y \<cdot> inv_elem x"  by (simp add: monoid.invprod(2) monoid_axioms)
end

context compositional_monoid
begin
lemma invertible_is_bijective:assumes dom: "u \<in> hom E E" shows "invertible u \<longleftrightarrow> bij_betw u E E" 
proof-  
  from dom interpret set_morphism u E E  by (metis (full_types) hom10 hom9 set_morphism_def)
  show "invertible u \<longleftrightarrow> bij_betw u E E"  using bij_betw_iff_has_inverse mem_hom by blast
qed
lemma Units_bijective: "Units = {u \<in>  hom E E. bij_betw u E E}"  unfolding Units_def by (auto simp add: invertible_is_bijective)
lemma Units_bij_betwI [intro, simp]: "u \<in> Units \<Longrightarrow> bij_betw u E E" by (simp add: Units_bijective)
lemma Units_bij_betwD [dest, simp]: "\<lbrakk>u \<in> hom E E; bij_betw u E E \<rbrakk> \<Longrightarrow> u \<in> Units" unfolding Units_bijective by simp
sublocale symmetric: group "Units" "compose E" "Id E" by (fact group_of_units)
end



locale compositional_group = compositional_monoid M E+monoid_subgroup M Units "compose E" "Id E" for M and E
begin
lemma compositional_group_closed [intro, simp]: "\<lbrakk>u \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> u x \<in> E" using bij_betwE by blast
lemma compositional_group_undef [intro, simp]:  "\<lbrakk>u \<in> M; x \<notin> E\<rbrakk> \<Longrightarrow> u x = undefined"  by simp
end


section QuotientGroup
locale quotient_group=
  group X "(\<cdot>)" e + 
  quotient_monoid X "(\<cdot>)" R e for
  X::"'a set" and
  f::"'a \<Rightarrow> 'a \<Rightarrow>'a" (infixl "\<cdot>" 70) and
  R::"('a \<times> 'a) set" and
  e::"'a"
begin
definition "H \<equiv> proj e"
lemma equivalent_iff:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> (inv_elem x) \<cdot> y \<in> H"
proof-
  fix x y assume xmem:"x \<in> X" and ymem:"y \<in> X"
  show "(x, y) \<in> R \<longleftrightarrow> (inv_elem x) \<cdot> y \<in> H" (is "?LHS \<longleftrightarrow> ?RHS")
  proof
    assume L:?LHS
    then obtain "(inv_elem x \<cdot> x, inv_elem x \<cdot> y) \<in> R"
      using invertible invertible_inverse_closed left_compatible xmem by presburger
    then obtain "(e, inv_elem x \<cdot> y) \<in> R"
      by (simp add: xmem)
    then show ?RHS
      using H_def projE5 by blast
    next
    assume R:?RHS
    then obtain "(e, inv_elem x \<cdot> y) \<in> R"
      using H_def idmem projE4 by blast
    then obtain "(x \<cdot> e, x \<cdot> inv_elem x \<cdot> y) \<in> R"
      by (metis associative compatible invertible invertible_inverse_closed projE2 xmem ymem)
    then obtain "(x, y) \<in> R"
      by (simp add: leftid rightid xmem ymem)
    then show ?LHS
      by blast
  qed
qed

lemma h_inv_closed:"\<And>x. x \<in> H \<Longrightarrow> inv_elem x \<in> H"
proof-
  fix x assume xmem:"x \<in> H"
  then obtain "(e, x) \<in> R"
    using H_def idmem projE4 by blast
  then obtain "(inv_elem x \<cdot> e, inv_elem x \<cdot> x) \<in> R"
    using H_def xmem equivalent_iff idmem invertible invertible_inverse_closed invertible_inverse_inverse invertible_left_inverse projE1 rightid by presburger
  then obtain "(e, inv_elem x) \<in> R"
    by (metis H_def idmem invertible invertible_inverse_closed invertible_left_inverse projE1 projE2 rightid xmem)
  then show "inv_elem x \<in> H"
    by (simp add: H_def projE5)
qed

lemma id_image_monoid_subgroup:"monoid_subgroup H X f e"
proof(rule monoid_subgroupI)
  show "submonoid H X (\<cdot>) e"
  proof(rule submonoidI)
    show "monoid X (\<cdot>) e"
      by (simp add: monoid_axioms)
    show "H \<subseteq> X"
      using H_def idmem projE1 by auto
    show "\<And>(x::'a) y::'a. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> x \<cdot> y \<in> H"
      by (metis H_def idmem leftid qlaw2)
    show " e \<in> H"
      using H_def idmem projE2 projE5 by blast
  qed
  interpret sub:monoid H "(\<cdot>)" e apply(unfold_locales)
    apply (meson \<open>submonoid H (X::'a set) (\<cdot>) (e::'a)\<close> submonoid.opsub)
    apply (simp add: H_def associative idmem projE1)
    apply (meson \<open>submonoid H (X::'a set) (\<cdot>) (e::'a)\<close> submonoid.idsub)
    using H_def idmem leftid projE1 apply blast
    by (simp add: H_def idmem projE1 rightid)
  show "e \<in> H"
    by (meson \<open>submonoid H (X::'a set) (\<cdot>) (e::'a)\<close> submonoid.idsub)
  show "\<And>x::'a. x \<in> H \<Longrightarrow> monoid.invertible H (\<cdot>) e x"
    using H_def h_inv_closed idmem invertible_left_inverse invertible_right_inverse projE1 by blast
  show "\<And>x::'a. x \<in> H \<Longrightarrow> inv_elem x \<in> H"
    by (simp add: h_inv_closed)
qed

lemma quotient_rinv:"x \<in> X \<Longrightarrow> (proj x)\<bullet>(proj (inv_elem x)) = proj e" by (simp add: qlaw3)
lemma quotient_linv:"x \<in> X \<Longrightarrow> (proj (inv_elem x))\<bullet>(proj x ) = proj e"  by (metis invertible invertible_inverse_closed invertible_left_inverse proj.cmp) 
lemma quotient_elem_inv:"x \<in> X \<Longrightarrow>  quotient.invertible (proj x) " by (meson invertible invertible_inverse_closed projE3 quotient.invertibleI quotient_linv quotient_rinv)  
lemma quotient_eqcl_inv:"t \<in> (X/R) \<Longrightarrow>  quotient.invertible t " by (metis psecE1 psecE2 quotient_elem_inv)
lemma quotient_inv_comp:"x \<in> X \<Longrightarrow>  quotient.inv_elem (proj x) = proj (inv_elem x)"  by (simp add: quotient.inverse_equality quotient_linv quotient_rinv) 

sublocale quotient:group "X/R" "(\<bullet>)" "proj e" by(unfold_locales,simp add: quotient_eqcl_inv)
end

section LiftingLawToSets

definition set_prod ::"('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  where "set_prod f H K = (\<Union>h\<in>H. \<Union>k\<in>K. {f h k})"
lemma set_prod_memI:"\<exists>h \<in> H. \<exists>k \<in> K. y = f h k \<Longrightarrow> y \<in> set_prod f H K" by(auto simp add:set_prod_def)
lemma set_prod_memD:" y \<in> set_prod f H K \<Longrightarrow> (\<exists>h \<in> H. \<exists>k \<in> K. y = f h k)" by(auto simp add:set_prod_def)
lemma set_prod_singletonD1:" y \<in> set_prod f {x} K \<Longrightarrow> (\<exists>k \<in> K. y= f x k)" by(auto simp add:set_prod_def)
lemma set_prod_singletonD2:" y \<in> set_prod f H {x} \<Longrightarrow> (\<exists>h \<in> H. y= f h x)" by(auto simp add:set_prod_def)
lemma set_prod_singleton_memI1:"(\<exists>k \<in> K. y= f x k) \<Longrightarrow>  y \<in> set_prod f {x} K" by(auto simp add:set_prod_def)
lemma set_prod_singleton_memI2:"(\<exists>h \<in> H. y= f h x) \<Longrightarrow>  y \<in> set_prod f H {x}" by(auto simp add:set_prod_def)
lemma set_prod_singleton_mem_iff:" y \<in> set_prod f {x} K \<longleftrightarrow> (\<exists>k \<in> K. y= f x k)" by(auto simp add:set_prod_def)
lemma set_prod_singleton_mem1:" set_prod f {x} K = {f x k|k. k \<in> K}" by(auto simp add:set_prod_def)
lemma set_prod_singleton_mem2:" set_prod f H {x} = {f h x|h. h \<in> H}" by(auto simp add:set_prod_def)


context magma 
begin
lemma set_prod_closed:"A \<subseteq> X \<Longrightarrow> B \<subseteq> X \<Longrightarrow> set_prod f A B \<subseteq> X" by(auto simp add:closed set_prod_def subsetD)
definition l_coset (infixl "\<cdot>|" 70) where "x \<cdot>| H \<equiv> {x \<cdot>h |h. h \<in> H}"
definition r_coset (infixl "|\<cdot>" 70) where "H |\<cdot> x \<equiv> {h \<cdot>x |h. h \<in> H}"
lemma l_coset_memI[intro]:"h \<in> H \<Longrightarrow> x \<cdot> h \<in> x \<cdot>| H" unfolding l_coset_def  by blast
lemma r_coset_memI[intro]:"h \<in> H \<Longrightarrow> h \<cdot> x \<in> H |\<cdot> x" unfolding r_coset_def by blast
lemma l_coset_memE[elim]:"a \<in> x\<cdot>|H \<Longrightarrow> (\<And>h. \<lbrakk>h\<in>H;a=x\<cdot>h\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" unfolding l_coset_def  by blast
lemma r_coset_memE[elim]:"a \<in> H|\<cdot>x \<Longrightarrow> (\<And>h. \<lbrakk>h\<in>H;a=h\<cdot>x\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" unfolding r_coset_def  by blast
lemma l_coset_prod:"x\<cdot>|H = set_prod f {x} H"  using set_prod_singleton_mem1 by fastforce
lemma r_coset_prod:"H|\<cdot>x = set_prod f H {x}"  using set_prod_singleton_mem2 by fastforce
end

context semigroup begin
lemma set_prod_assoc:"A \<subseteq> X \<Longrightarrow> B \<subseteq> X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> set_prod f(set_prod f A B) C= set_prod f A (set_prod f B C) " 
proof-
  assume A0:"A \<subseteq> X" "B \<subseteq> X" "C \<subseteq> X "
  let ?AB="set_prod f A B" let ?BC="set_prod f B C" 
  let ?L="set_prod f ?AB C" let ?R="set_prod f A ?BC"
  show "?L= ?R"
  proof
    show "?L \<subseteq> ?R"
    proof
      fix x assume A1:"x \<in> ?L"
      then obtain a b c where B0: "a\<in>A" "b\<in>B" "c\<in>C" "x = (a\<cdot>b)\<cdot>c" unfolding set_prod_def by blast
      then obtain "x = a\<cdot>(b\<cdot>c)" using A0 associative by blast
      then show "x \<in> ?R"  unfolding set_prod_def using B0 by blast
    qed
    next show "?R \<subseteq> ?L"
    proof
      fix x assume A1:"x \<in>?R"
      then obtain a b c where B0: "a\<in>A" "b\<in>B" "c\<in>C" "x = a\<cdot>(b\<cdot>c)" unfolding set_prod_def by blast
      then obtain "x = (a\<cdot>b)\<cdot>c" using A0 by (simp add: associative in_mono) 
      then show "x \<in>?L"  unfolding set_prod_def using B0 by blast
    qed
  qed
qed
end



context monoid begin

lemma set_prod_lid:"A \<subseteq> X \<Longrightarrow> set_prod f {e} A = A" 
  apply(auto simp add:set_prod_singleton_mem1)
  apply (simp add: leftid subset_eq)
  using leftid by force

lemma set_prod_rid:"A \<subseteq> X \<Longrightarrow> set_prod f A {e} = A" 
  apply(auto simp add:set_prod_singleton_mem2)
  apply (simp add: rightid subset_eq)
  using rightid by force
end

  

lemma quotient_by_monoid_subgroup_eqr:
  fixes G::"'a set" and  H::"'a set" 
  fixes f (infixl "\<cdot>" 70) 
  assumes A0:"group G f e" and A1:"monoid_subgroup H G f e"
  defines "RL \<equiv> {(x, y) \<in> G \<times> G. (monoid.inv_elem G f e x) \<cdot> y \<in> H}"
  defines "RR \<equiv> {(x, y) \<in> G \<times> G. y \<cdot> (monoid.inv_elem G f e x) \<in> H}"
  shows "is_eqrel G RL" and "is_eqrel G RR"  
proof-
  let ?inv="monoid.inv_elem G (\<cdot>) e"
  show "is_eqrel G RL"
  apply(auto simp add:is_eqrel_def RL_def refl_on_def sym_def trans_def)
  apply (metis A0 A1 group.axioms(1) group.invertible monoid.invertible_left_inverse monoid_subgroup_submonoid submonoid.idsub)
  proof-
     show "\<And>(x::'a) y::'a. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow>(?inv x) \<cdot> y \<in> H \<Longrightarrow> (?inv y) \<cdot> x \<in> H"
     proof-
      fix x y assume A3:"x \<in> G" "y \<in> G" "(?inv x) \<cdot> y \<in> H"
      have "(?inv y) \<cdot> x = ?inv ((?inv x) \<cdot> y)"   by (simp add: A0 A3(1) A3(2) group.axioms(1) group.invertible monoid.invertible_inverse_closed monoid.invertible_inverse_inverse monoid.invprod(2))
      also have "... \<in> H"  by (meson A1 A3(3) group.invertible monoid_subgroup.axioms(1) monoid_subgroup.axioms(2) submonoid.submonoid_inverse_closed)
      finally show "?inv y \<cdot> x \<in> H" by simp
     qed
    show "\<And>x y z.  \<lbrakk>x \<in> G; y \<in> G; z \<in> G;?inv x \<cdot> y \<in> H;  ?inv y \<cdot> z \<in> H\<rbrakk> \<Longrightarrow> ?inv x \<cdot> z \<in> H"
    proof-
      fix x y z assume A2:"x \<in> G" "y \<in> G"  "(?inv x) \<cdot> y \<in> H"  "z \<in> G" "(?inv y) \<cdot> z \<in> H "  
       have B0:"(?inv x) \<cdot> z = ((?inv x) \<cdot> y) \<cdot> ((?inv y) \<cdot> z)" using A0 A1 A2 group.axioms(1) monoid_def group.invertible monoid.inv_right_cancel monoid.invertible_inverse_closed semigroup.associative monoid_subgroup.axioms(1) submonoid.subD by fastforce
      show "(?inv x) \<cdot> z \<in> H" by (metis A1 A2(3) A2(5) B0 monoid_subgroup_submonoid submonoid.opsub)
    qed
  qed
  show "is_eqrel G RR"
  apply(auto simp add:is_eqrel_def RR_def refl_on_def sym_def trans_def)
  apply (metis A0 A1 group.axioms(1) group.invertible monoid.invertible_right_inverse monoid_subgroup_submonoid submonoid.idsub)
  proof-
     show "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow>y \<cdot> (?inv x) \<in> H \<Longrightarrow> x \<cdot> (?inv y)  \<in> H"
     proof-
      fix x y assume A3:"x \<in> G" "y \<in> G" "y \<cdot>(?inv x) \<in> H"
      have "x \<cdot> (?inv y) = ?inv (y \<cdot>(?inv x))" by (simp add: A0 A3(1) A3(2) group.axioms(1) group.invertible monoid.invertible_inverse_closed monoid.invertible_inverse_inverse monoid.invprod(2))  
      also have "... \<in> H"  by (meson A1 A3(3) group.invertible monoid_subgroup.axioms(1) monoid_subgroup.axioms(2) submonoid.submonoid_inverse_closed)
      finally show "x \<cdot> (?inv y) \<in> H" by simp
    qed
    show "\<And>x y z.  \<lbrakk>x \<in> G; y \<in> G; z \<in> G; y \<cdot> ?inv x \<in> H;  z \<cdot> ?inv y \<in> H\<rbrakk> \<Longrightarrow>z \<cdot> ?inv x  \<in> H"
    proof-
      fix x y z assume A2:"x \<in> G" "y \<in> G"  "z \<in> G" "y \<cdot> (?inv x) \<in> H"  "z \<cdot> (?inv y) \<in> H "  
      have B0:"z \<cdot> (?inv x) = (z \<cdot> (?inv y)) \<cdot> ((y \<cdot> ?inv x))"  using A0 A1 A2 group.axioms(1,2) group_axioms_def monoid_def monoid.inv_left_cancel monoid.invertible_inverse_closed semigroup.associative monoid_subgroup_submonoid submonoid.subD by fastforce
      show "z \<cdot> (?inv x)\<in> H"  by (metis A1 A2(4) A2(5) B0 monoid_subgroup.axioms(1) submonoid.opsub) 
    qed
  qed
qed

lemma quotient_by_monoid_subgroup:
  fixes G::"'a set" and  H::"'a set" 
  fixes f (infixl "\<cdot>" 70) 
  assumes A0:"group G f e" and A1:"monoid_subgroup H G f e"
  defines "RL \<equiv> {(x, y) \<in> G \<times> G. (monoid.inv_elem G f e x) \<cdot> y \<in> H}"
  defines "RR \<equiv> {(x, y) \<in> G \<times> G. y \<cdot>(monoid.inv_elem G f e x) \<in> H}"
  shows "\<And>a x y. a \<in> G \<Longrightarrow> (x, y) \<in> RL \<Longrightarrow>  (a\<cdot>x , a\<cdot>y) \<in> RL"  and "\<And>a x y. a \<in> G \<Longrightarrow> (x, y) \<in> RR \<Longrightarrow>  (x\<cdot>a , y\<cdot>a) \<in> RR"
proof-
  let ?inv="monoid.inv_elem G (\<cdot>) e"
  show "\<And>a x y. a \<in> G \<Longrightarrow> (x, y) \<in> RL\<Longrightarrow> (a\<cdot> x , a\<cdot> y) \<in> RL"
  proof-
    fix a x y assume A2:"a \<in> G" "(x, y) \<in> RL"
    obtain B0:"(?inv x) \<cdot> y \<in> H" and B1:"x \<in> G" and B2:"y \<in> G"    using A2 RL_def by blast  
    obtain B3:"(?inv x) \<in> G" and B4:"(?inv a) \<in> G"  by (simp add: A0 A2(1) group.axioms(1) B1 group.invertible monoid.invertible_inverse_closed)
    then obtain B5:"(a \<cdot> x) \<in> G" "a \<cdot>y \<in> G" by (meson A0 A2(1) group.axioms(1) monoid_def semigroup_def B1 B2 magma.closed)
    have B6:"((?inv x)\<cdot>(?inv a)) = ?inv (a \<cdot> x)" by (simp add: A0 A2(1) group.axioms(1) B1 group.invertible monoid.invprod(2))
    have B7:"(?inv x) \<cdot> y = (?inv x) \<cdot> ((?inv a) \<cdot> a) \<cdot> y"  by (metis A0 A2(1) group.axioms(1) B1 group.invertible monoid.invertible_inverse_closed monoid.invertible_left_inverse monoid.rightid) 
    also have "... = (((?inv x)\<cdot>(?inv a)) \<cdot> a) \<cdot> y"  using A0 A2(1) group.axioms(1) monoid_def B3 B4 semigroup.associative by fastforce  
    also have "... = ((?inv x)\<cdot>(?inv a)) \<cdot> (a \<cdot> y) " by (metis A0 A2(1) group.axioms(1) monoid_def semigroup_def B2 B3 B4 magma.closed semigroup.associative)
    also have "... = monoid.inv_elem G (\<cdot>) e (a \<cdot> x) \<cdot> (a \<cdot> y)"   by (simp add: B6)
    also have "... \<in> H"  using B0 calculation by auto
    then have "?inv (a \<cdot> x) \<cdot> (a \<cdot> y) \<in> H" by blast
    then show " (a\<cdot> x , a\<cdot> y) \<in> RL"   using B5 unfolding RL_def by blast
  qed
  show "\<And>a x y. a \<in> G \<Longrightarrow> (x, y) \<in> RR\<Longrightarrow> (x\<cdot>a , y\<cdot>a) \<in> RR"
  proof-
    fix a x y assume A2:"a \<in> G" "(x, y) \<in> RR"
    obtain B0:"y\<cdot>(?inv x)\<in> H" and B1:"x \<in> G" and B2:"y \<in> G"  using A2 RR_def by blast  
    obtain B3:"(?inv x) \<in> G" and B4:"(?inv a) \<in> G"  by (simp add: A0 A2(1) group.axioms(1) B1 group.invertible monoid.invertible_inverse_closed)
    then obtain B5:"(x\<cdot>a) \<in> G" "y\<cdot>a \<in> G" by (meson A0 A2(1) group.axioms(1) monoid_def semigroup_def B1 B2 magma.closed)
    have B6:"((?inv a)\<cdot>(?inv x)) = ?inv (x\<cdot>a)" by (simp add: A0 A2(1) group.axioms(1) B1 group.invertible monoid.invprod(2))
    have B7:"y\<cdot>(?inv x) =y\<cdot>(a\<cdot>(?inv a))\<cdot>(?inv x)" by (metis A0 A2(1) group.axioms(1) B2 group.invertible monoid.invertible_right_inverse monoid.rightid) 
    also have "... = ((y\<cdot>a) \<cdot>(?inv a)) \<cdot> (?inv x)"  using A0 A2(1) group.axioms(1) monoid_def B2 B4 semigroup.associative by fastforce
    also have "... = (y\<cdot>a) \<cdot> ((?inv a)\<cdot>(?inv x)) " using A0 group.axioms(1) monoid_def B3 B4 B5(2) semigroup.associative by fastforce
    also have "... = (y\<cdot>a) \<cdot> (?inv (x\<cdot>a))"   by (simp add: B6)
    also have "... \<in> H"  using B0 calculation by auto
    then have "(y\<cdot>a) \<cdot> (?inv (x\<cdot>a)) \<in> H" by blast
    then show " (x\<cdot>a ,y\<cdot>a) \<in> RR"  using B5 unfolding RR_def by blast
  qed
qed
 
locale commutative_semigroup=semigroup X "(\<cdot>)" for X and f (infixl "\<cdot>" 70)+
  assumes commutes:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y = y \<cdot> x"
begin
lemma lcomm:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)" using associate3 commutes by force
end


section ExponentsAndOrder
context monoid begin

primrec pow_nat  (infixr "^" 80)where
   pow_0:"x ^ 0 = e " 
 | pow_Suc:"x ^ Suc n = x \<cdot> (x ^ n)"

lemma power_one[simp]:"e ^ n = e" proof(induct n)  case 0 then show ?case  by simp  next   case (Suc n) then show ?case by (simp add: idmem rightid) qed
lemma power_on_right[simp]:"x \<in> X \<Longrightarrow> x ^ 1 = x"  by (simp add: rightid)
lemma power_Suc0_right [simp]: "x \<in> X \<Longrightarrow> x ^ Suc 0 = x" using power_on_right by auto
lemma pow_closed[simp]:"x \<in> X \<Longrightarrow> x ^ n \<in> X"  proof(induct n)  case 0  then show ?case  by (simp add: idmem)  next   case (Suc n)  then obtain "x ^ Suc n = x \<cdot> x ^ n" and "x ^ n \<in> X"  by simp  then show ?case  by (simp add: Suc.prems closed)  qed
lemma power_commutes: "x \<in> X \<Longrightarrow> (x ^ n) \<cdot> x = x \<cdot> (x ^ n)"proof( induct n)case 0 then show ?case  by (simp add: leftid rightid)  next case (Suc n)  then show ?case   by (metis associate3 pow_Suc pow_closed)  qed
lemma power_Suc2: "x \<in> X \<Longrightarrow> x ^ Suc n = x ^ n \<cdot> x"   by (simp add: power_commutes)
lemma power_add: "x \<in> X \<Longrightarrow> x ^ (m + n) = x ^ m \<cdot> x ^ n" proof(induct m) case 0  then show ?case   by (simp add: leftid)  next  case (Suc m)  then show ?case   by (simp add: associate3 local.power_commutes)  qed
lemma power_mult: "x \<in> X \<Longrightarrow> x ^ (m * n) = (x ^ m) ^ n"  by (induct n) (simp_all add: power_add)
definition elem_exponents :: "'a \<Rightarrow> nat set" where "elem_exponents x \<equiv> {n::nat. 0<n \<and> x^n = e}"
definition elem_ord::"'a \<Rightarrow> nat" where "elem_ord x \<equiv> if elem_exponents x \<noteq> {} then (Least (\<lambda>n::nat. n \<in> elem_exponents x))  else 0"
lemma elem_ord_simp1:"elem_ord x \<noteq> 0 \<Longrightarrow> elem_ord x =  Least (\<lambda>n::nat. n \<in> (elem_exponents x))"  using elem_ord_def by auto
lemma elem_ord_exp:"x ^ (elem_ord x) = e"
proof(cases "elem_ord x =0")
  case True  then show ?thesis by auto
next
  case False
  then have "elem_ord x = (Least (\<lambda>n::nat. n \<in> elem_exponents x))"   using elem_ord_simp1 by auto
  also have "... \<in> (elem_exponents x)" by (metis Collect_empty_eq Collect_mem_eq False LeastI elem_ord_def)
  then show ?thesis   by (simp add: calculation elem_exponents_def) 
qed

lemma order_divides_exponent:assumes "x \<in> X" "elem_ord x \<noteq> 0" "m \<in> elem_exponents x" shows "(elem_ord x) dvd m"
proof-
  obtain n where nleast:"n =(Least (\<lambda>k::nat. k \<in> elem_exponents x))" and "n \<in> elem_exponents x"   by (meson LeastI assms) 
  obtain "x ^ m = e" and "0 < m" using assms elem_exponents_def by auto
  then obtain "m \<in> elem_exponents x"   by (simp add: assms)
  then obtain "n \<le> m"   by (simp add: \<open>(n::nat) = (LEAST n::nat. n \<in> elem_exponents (x::'a))\<close> wellorder_Least_lemma(2))
  define q where "q \<equiv> m div n"
  define r where "r = m mod n"
  then obtain mf:"m = q * n + r" and "0 \<le> r" and "r < n"
    by (metis \<open>(n::nat) = (LEAST n::nat. n \<in> elem_exponents (x::'a))\<close> assms(2) bot_nat_0.extremum bot_nat_0.not_eq_extremum div_mod_decomp elem_ord_def mod_less_divisor q_def)
  then have "e = x ^ m"  using \<open>(x::'a) ^ (m::nat) = (e::'a)\<close> by auto
  also  have "...  = x ^ (q * n + r)"  by (simp add: \<open>(m::nat) = (q::nat) * (n::nat) + (r::nat)\<close>)
  also have "... = (x ^ (q * n)) \<cdot> (x ^ r) " by (simp add: assms(1) local.power_add)
  also have "... = (e) \<cdot> (x ^ r)"   by (metis \<open>(n::nat) = (LEAST n::nat. n \<in> elem_exponents (x::'a))\<close> assms(1) assms(2) elem_ord_def elem_ord_exp local.power_mult local.power_one mult.commute)
  also have "... = x ^ r"   by (simp add: assms(1) leftid)
  finally have "r = 0"
  proof-
    assume "e = x ^ r"
    show " r = (0::nat)"
    proof(rule ccontr)
      assume "r \<noteq> 0" then obtain "0<r" and "r < n"   using \<open>(r::nat) < (n::nat)\<close> by blast
      also have rmem:"r \<in> elem_exponents x"
        using \<open>(e::'a) = (x::'a) ^ (r::nat)\<close> calculation(1) elem_exponents_def by fastforce
      show False
        using not_less_Least[of r "(\<lambda>k. k \<in> elem_exponents x)"] nleast rmem calculation by blast
    qed
  qed
  then have "m = q * n" by (simp add: mf)
  also have "... = q * (elem_ord x) "   using assms(2) elem_ord_simp1 nleast by presburger
  finally  show ?thesis by simp
qed

lemma elem_exp_memD1:"\<lbrakk>x \<in> X; elem_ord x \<noteq> 0; m \<in> elem_exponents x\<rbrakk> \<Longrightarrow> (\<exists>k. m =(elem_ord x) * k )" using order_divides_exponent by blast
lemma elem_exp_memD2:"\<lbrakk>x \<in> X; elem_ord x \<noteq> 0; m \<in> elem_exponents x\<rbrakk> \<Longrightarrow> (\<exists>k. k \<ge>1 \<and> m =(elem_ord x) * k )" by (metis Least_eq_0 One_nat_def elem_exp_memD1 elem_ord_simp1 linorder_not_le nat_0_less_mult_iff not_gr0 not_less_eq_eq) 
lemma elem_exp_memI:"\<lbrakk>x \<in> X; elem_ord x \<noteq> 0;(\<exists>k. k \<ge> 1 \<and> m =(elem_ord x) * k)\<rbrakk> \<Longrightarrow> m \<in> elem_exponents x "
proof-
  assume xmem:"x \<in> X" and nzo:" elem_ord x \<noteq> 0" and mul1:"\<exists>k. k \<ge> 1 \<and> m =(elem_ord x) * k "
  then obtain k where geq1:"k \<ge> 1" and mul2:"m =(elem_ord x) * k" by blast
  have "x ^ (elem_ord x) = e "  by (simp add: elem_ord_exp)
  then obtain "(x ^ (elem_ord x)) ^ k = e"  by simp
  then obtain "x ^ m = e"  by (simp add: local.power_mult mul2 xmem)
  then show "m \<in> elem_exponents x"
    using elem_exponents_def mul1 nzo by force
qed
lemma elem_exp_memI2:"\<lbrakk>x \<in> X; elem_ord x \<noteq> 0;m > 0; (elem_ord x dvd m)\<rbrakk> \<Longrightarrow> m \<in> elem_exponents x "  using elem_exp_memI by auto

lemma elem_pow_eq_id:"\<lbrakk>a \<in> X; elem_ord a \<noteq> 0; k>0; m>0\<rbrakk> \<Longrightarrow> (a^k)^m = e \<longleftrightarrow> (elem_ord a) dvd (k * m)"
proof-
  assume amem:"a \<in> X" and nzo:"elem_ord a \<noteq> 0" and kgeqz:"k > 0" and mgeqz:"m>0"
  show "(a^k)^m = e \<longleftrightarrow> (elem_ord a) dvd (k * m)"
  proof
    assume "(a ^ k) ^ m = e"
    then obtain "a ^ (k * m) = e" using amem local.power_mult by auto
    then obtain "(k * m) \<in> elem_exponents a" unfolding elem_exponents_def by (simp add: kgeqz mgeqz)
    then show "(elem_ord a) dvd (k * m)"   using amem nzo order_divides_exponent by blast
  next assume "(elem_ord a) dvd (k * m)"
  then show "(a^k)^m = e"  by (metis amem dvd_def elem_ord_exp local.power_mult monoid.power_one monoid_axioms)
  qed
qed

lemma id_exps:"elem_exponents e \<noteq> {}" using elem_exponents_def by auto

lemma elem_ord_id:"elem_ord e = 1" 
  unfolding elem_ord_def
  apply(simp add:id_exps)
  apply(rule Least_equality)
  apply (simp add: elem_exponents_def)
  by (simp add: elem_exponents_def)
   
lemma ord_pow1:"\<lbrakk>a \<in> X; elem_ord a \<noteq> 0; (1::nat) \<le> (k::nat)\<rbrakk> \<Longrightarrow> elem_ord (a ^ k) = (elem_ord a) div (gcd( elem_ord a) k) "
proof-
  let ?b="a^k" let ?n="elem_ord a" let ?j="?n div (gcd ?n k)"
  assume amem:"a \<in> X" and nzo:"elem_ord a \<noteq> 0" and kgeq1:"1 \<le> k" 
  have B1:"\<And>m. m>0 \<Longrightarrow>  (?b ^ m =e) \<longleftrightarrow>  ?j dvd m"
  proof-
    fix m::nat assume mgtz:"m>0"
    then have "(?b ^ m =e) \<longleftrightarrow> ?n dvd k*m" using amem elem_pow_eq_id kgeq1 nzo by force
    also have "... \<longleftrightarrow> ?j dvd ((k * m) div ((gcd ?n k)))" by simp
    also have "... \<longleftrightarrow> ?j dvd m"  by (simp add: div_dvd_iff_mult gcd_mult_distrib_nat mult.commute nzo)
    finally  show "(?b ^ m =e) \<longleftrightarrow>  ?j dvd m"  by blast
  qed
  then have B2:"?j \<in> elem_exponents ?b"  by (simp add: div_greater_zero_iff elem_exponents_def nzo)
  have B3:"\<And>m. m \<in> elem_exponents ?b \<Longrightarrow> ?j dvd m"  using B1 elem_exponents_def by auto
  then have B4:"\<And>m. m \<in> elem_exponents ?b \<Longrightarrow>  ?j \<le> m" using dvd_imp_le elem_exponents_def by blast
  have B5:"Least (\<lambda>i::nat. i \<in> elem_exponents ?b) = ?j "
    unfolding elem_ord_def  
    apply(rule Least_equality)  
    using B2 elem_ord_def apply force
    using B4 elem_ord_def by force
  show "elem_ord ?b = ?j"  by (metis B2 B5 elem_ord_def empty_iff)
qed

lemma pow_fin_ord:"\<lbrakk>a \<in> X; elem_ord a \<noteq> 0\<rbrakk> \<Longrightarrow> elem_ord (a ^ (k::nat)) \<noteq> 0 "
proof-
  assume amem:"a \<in> X" and ford:"elem_ord a \<noteq> 0"
  let ?b="a^(k::nat)"
  show "elem_ord ?b \<noteq> 0"
  proof(cases "k=0")
    case True then show ?thesis by (simp add: elem_ord_id) 
  next
    case False then show ?thesis  by (simp add: amem div_greater_zero_iff ford ord_pow1) 
  qed
qed

lemma ord_pow2:"\<lbrakk>a \<in> X; elem_ord a \<noteq> 0;(k::nat)>0;(d::nat)>0; d dvd (elem_ord a)\<rbrakk> \<Longrightarrow> elem_ord (a^k) = d \<longleftrightarrow> (\<exists>r::nat. r > 0 \<and> gcd r d = 1 \<and> k = r * (elem_ord a) div d)"
proof-
  assume amem:"a \<in> X" and ford:"elem_ord a \<noteq> 0" and knz:"(k::nat)>0" and dnz:"(d::nat)>0" and ddvd:"d dvd (elem_ord a)"
  let ?b="a^k" let ?n="elem_ord a" let ?m="?n div d"
  have "elem_ord ?b = d \<longleftrightarrow> d = ?n div (gcd ?n k)"  using amem ford knz ord_pow1 by auto
  also have "... \<longleftrightarrow> (gcd ?n k) = ?m"   by (metis ddvd dnz dvd_mult_div_cancel gcd.commute gcd_dvd2 gcd_eq_0_iff gcd_pos_nat knz nonzero_mult_div_cancel_right)
  also have "... \<longleftrightarrow> gcd (d * ?m) k = ?m" by (simp add: ddvd)
  also have "... \<longleftrightarrow> (\<exists>r::nat. r > 0 \<and> gcd r d = 1 \<and> k = r * ?m)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then show ?rhs
    proof -
      have f1: "\<forall>n na. \<not> (n::nat) dvd na \<or> na div n * n = na"
        using dvd_div_mult_self by blast
      have f2: "gcd (elem_ord a) k = elem_ord a div d"
        using \<open>(gcd (elem_ord (a::'a)) (k::nat) = elem_ord a div (d::nat)) = (gcd (d * (elem_ord a div d)) k = elem_ord a div d)\<close> \<open>gcd ((d::nat) * (elem_ord (a::'a) div d)) (k::nat) = elem_ord a div d\<close> by blast
      then have f3: "elem_ord a div d dvd elem_ord a \<and> elem_ord a div d dvd k \<and> (\<forall>n. \<not> n dvd elem_ord a \<or> \<not> n dvd k \<or> n dvd elem_ord a div d)"
        by (metis (no_types) gcd_unique_nat)
      have f4: "k \<noteq> 0"
        using knz by force
      have f5: "\<forall>n na. \<not> (n::nat) dvd na \<or> \<not> 0 < na \<or> n \<le> na"
        by force
      have f6: "\<forall>n na. \<not> (n::nat) dvd na \<or> n * (na div n) = na"
        using dvd_mult_div_cancel by blast
      have "Suc 0 \<le> d"
        using dnz by presburger
      then have f7: "1 \<le> d"
        by simp
      have f8: "d div d = 1"
        by (simp add: dnz)
      have f9: "d div d dvd elem_ord a div d"
        by (simp add: ddvd)
      then have f10: "d div d * (elem_ord a div d div (d div d)) = elem_ord a div d"
        using f6 by blast
      have "elem_ord a div d = elem_ord a div d div (d div d)"
        using f8 by simp
      then show ?thesis
        using f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 by (smt (z3) One_nat_def \<open>gcd ((d::nat) * (elem_ord (a::'a) div d)) (k::nat) = elem_ord a div d\<close> amem ddvd div_greater_zero_iff dnz dvd_div_eq_0_iff dvd_refl elem_ord_exp elem_ord_id ford gcd.commute gcd_mult_distrib_nat gcd_nat.absorb_iff2 gcd_pos_nat knz local.power_mult monoid.ord_pow1 monoid_axioms nat_mult_eq_cancel1 nonzero_mult_div_cancel_right)
    qed
    next
    assume ?rhs
    then obtain r::nat where "r > 0" and "gcd r d = 1" and "k = r * ?m" by metis
    then show ?lhs  by (metis gcd.commute gcd_mult_distrib_nat mult.comm_neutral mult.commute)
  qed
  finally show "elem_ord ?b =d \<longleftrightarrow>  (\<exists>r::nat. r > 0 \<and> gcd r d = 1 \<and> k = r * ?n div d)"
    by (simp add: ddvd div_mult_swap) 
qed


lemma commute_pow1:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow>x \<cdot> y = y \<cdot> x \<Longrightarrow> x^(n::nat) \<cdot> y = y \<cdot> x^n"
proof-
  assume xmem:"x\<in>X" and ymem:"y \<in> X" and comm:"x \<cdot> y = y \<cdot> x "
  let ?xn="x^n" 
  show "?xn \<cdot> y = y \<cdot> ?xn"  proof(induct n)  case 0 then show ?case  by (simp add: leftid rightid ymem)   next
    case (Suc n)  then obtain "x^n \<cdot> y = y \<cdot> x ^n"   by simp  let ?n1="Suc n"
    have "x^?n1 \<cdot> y = x^n \<cdot> (x \<cdot> y)"   using associative local.power_Suc2 pow_closed xmem ymem by presburger
    also have "... = x^n \<cdot> (y \<cdot> x)"   by (simp add: comm)
    also have "... = (x^n \<cdot> y) \<cdot> x"  by (simp add: associative xmem ymem)
    also have "... = (y \<cdot> x ^n) \<cdot> x"    by (simp add: Suc)
    also have "... = y \<cdot> x^?n1"  using associative local.power_Suc2 pow_closed xmem ymem by presburger
    then show ?case   using calculation by auto 
  qed
qed
     

lemma commute_pow2:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow>x \<cdot> y = y \<cdot> x \<Longrightarrow> x^(n::nat) \<cdot> y^(m::nat) = y^m \<cdot> x^n"
proof-
  assume xmem:"x\<in>X" and ymem:"y \<in> X" and comm:"x \<cdot> y = y \<cdot> x "
  let ?xn="x^n" let ?ym="y^m"
  show "?xn \<cdot> ?ym = ?ym \<cdot> ?xn"
  proof(induct m)  case 0 then show ?case using leftid rightid xmem by auto next case (Suc m)   then show ?case   by (metis comm commute_pow1 pow_closed xmem ymem)   qed
qed

lemma commute_pow3:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow>x \<cdot> y = y \<cdot> x \<Longrightarrow> (x \<cdot> y)^(n::nat) = x^n \<cdot> y^n"
proof-
  assume xmem:"x\<in>X" and ymem:"y \<in> X" and comm:"x \<cdot> y = y \<cdot> x "
  let ?a="x^n" let ?b="y^n" let ?c="x \<cdot> y"
  show "(x \<cdot> y)^n = (x^n) \<cdot> (y^n)"
  proof(induct n)
    case 0  then show ?case by (simp add: idmem rightid) 
  next
    case (Suc n)
    then obtain "(x \<cdot> y) ^ n = x ^ n \<cdot> y ^ n"  by blast
    let ?m="Suc n"
    have "(x \<cdot> y) ^ (Suc n) = (x \<cdot> y)^n \<cdot> (x \<cdot> y)"  using closed local.power_Suc2 xmem ymem by auto
    also have "... = (x ^ n \<cdot> y ^ n) \<cdot> (x \<cdot> y)"  by (simp add: Suc)
    also have "... = x^n \<cdot>( y^n \<cdot> x) \<cdot> y"   by (simp add: associative closed xmem ymem)
    also have "... = x^n \<cdot>(x \<cdot> y^n) \<cdot> y" using comm commute_pow1 xmem ymem by auto
    also have "... = x^(Suc n) \<cdot> y^ (Suc n)" by (metis associative local.power_Suc2 pow_closed xmem ymem)
    finally show ?case by simp
  qed
qed

lemma commute_invertible:"\<lbrakk>x \<in> X; y \<in> X; invertible x; invertible y; x \<cdot> y = y \<cdot> x\<rbrakk> \<Longrightarrow> inv_elem x \<cdot> inv_elem y = inv_elem y \<cdot> inv_elem x" by (metis invprod(2))


lemma fin_prod_ord:
  assumes amem:"a \<in> X" and bmem:"b \<in> X" and commute:"a \<cdot> b = b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0"
  shows "elem_ord (a \<cdot> b) \<noteq> 0"
proof-
  let ?m="lcm (elem_ord a) (elem_ord b)"
  have "(a \<cdot> b)^?m = a^?m \<cdot> b^?m"  using amem bmem commute commute_pow3 by blast
  also have "... = e" by (metis amem bmem dvdE dvd_lcm1 dvd_lcm2 elem_ord_exp local.power_mult local.power_one pow_closed rightid)
  then obtain "?m \<in> elem_exponents (a \<cdot> b)"  using aford bford calculation elem_exponents_def by fastforce
  then show ?thesis by (metis (no_types, lifting) LeastI_ex elem_exponents_def elem_ord_def empty_iff mem_Collect_eq order_less_irrefl) 
qed

lemma commute_ords:
  assumes amem:"a \<in> X" and bmem:"b \<in> X" and commute:"a \<cdot> b = b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0"
  shows "(lcm (elem_ord a) (elem_ord b)) div (gcd (elem_ord a) (elem_ord b)) dvd elem_ord (a \<cdot> b)" and
        "elem_ord (a \<cdot> b) dvd (lcm (elem_ord a) (elem_ord b))"
proof-
  let ?\<alpha>="elem_ord a" let ?\<beta>="elem_ord b" 
  have B0:"elem_ord (a \<cdot> b) \<noteq> 0" by (simp add: aford amem bford bmem commute fin_prod_ord)
  have B1:"(a \<cdot> b)^?\<beta> = a ^ ?\<beta>"  using commute commute_pow3 elem_ord_exp pow_closed rightid amem bmem by presburger
  then have B2:"elem_ord ((a \<cdot> b)^?\<beta>) = elem_ord (a ^ ?\<beta>)" by simp
  also have B3:"... = ?\<alpha> div (gcd ?\<alpha> ?\<beta>)" using aford amem bford ord_pow1 by auto
  also have B4:"elem_ord ((a \<cdot> b)^?\<beta>) dvd (elem_ord (a \<cdot> b))"  by (metis One_nat_def Suc_le_eq \<open>elem_ord ((a::'a) \<cdot> (b::'a)) \<noteq> (0::nat)\<close> amem bford bmem bot_nat_0.not_eq_extremum closed dvd_div_mult_self dvd_mult2 gcd_dvd1 gcd_nat.refl ord_pow1)
  then have B5:"?\<alpha> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))" by (simp add: \<open>((a::'a) \<cdot> (b::'a)) ^ elem_ord b = a ^ elem_ord b\<close> \<open>elem_ord ((a::'a) ^ elem_ord (b::'a)) = elem_ord a div gcd (elem_ord a) (elem_ord b)\<close>)
  have B6:"(a \<cdot> b)^?\<alpha> = b ^ ?\<alpha>"   using amem bmem commute commute_pow3 elem_ord_exp leftid pow_closed by presburger 
  then have B7:"elem_ord ((a \<cdot> b)^?\<alpha>) = elem_ord (b ^ ?\<alpha>)" by simp
  have B8:"... = ?\<beta> div (gcd ?\<alpha> ?\<beta>)"  by (metis aford bford bmem gcd.bottom_right_bottom gcd.commute gcd_le1_nat ord_pow1) 
  have B9:"elem_ord ((a \<cdot> b)^?\<alpha>) dvd (elem_ord (a \<cdot> b))"  by (metis One_nat_def Suc_le_eq \<open>elem_ord ((a::'a) \<cdot> (b::'a)) \<noteq> (0::nat)\<close> aford amem bmem bot_nat_0.not_eq_extremum closed dvd_div_mult_self dvd_mult2 gcd_dvd1 gcd_nat.refl ord_pow1) 
  then have B10:"?\<beta> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))"  by (simp add: B6 B8) 
  have B11:"gcd (?\<beta> div (gcd ?\<alpha> ?\<beta>)) (?\<alpha> div (gcd ?\<alpha> ?\<beta>)) = 1"
  proof -
    have "gcd (elem_ord a) (elem_ord b) * 1 = gcd (elem_ord a) (elem_ord b) * gcd (elem_ord a div gcd (elem_ord a) (elem_ord b)) (elem_ord b div gcd (elem_ord a) (elem_ord b))"
      by (metis (no_types) dvd_mult_div_cancel gcd_dvd1 gcd_dvd2 gcd_mult_distrib_nat mult.right_neutral)
    then show ?thesis
      by (metis (no_types) aford gcd.commute gcd_eq_0_iff mult_left_cancel)
  qed
  have B12:"coprime (?\<alpha> div (gcd ?\<alpha> ?\<beta>)) (?\<beta> div (gcd ?\<alpha> ?\<beta>))"  using aford div_gcd_coprime by blast
  have B13:"((?\<alpha>*?\<beta>) div ((gcd ?\<alpha> ?\<beta>)*(gcd ?\<alpha> ?\<beta>))) dvd  (elem_ord (a \<cdot> b))"  by (metis B10 B12 B5 div_mult_div_if_dvd divides_mult gcd_dvd1 gcd_dvd2)
  have B14:"(?\<alpha>*?\<beta>) div ((gcd ?\<alpha> ?\<beta>)*(gcd ?\<alpha> ?\<beta>)) = (lcm ?\<alpha> ?\<beta>) div (gcd ?\<alpha> ?\<beta>)"  using div_mult2_eq lcm_nat_def by presburger
  show "(lcm (elem_ord a) (elem_ord b)) div (gcd (elem_ord a) (elem_ord b)) dvd elem_ord (a \<cdot> b)"   by (metis B13 B14)  
  show "elem_ord (a \<cdot> b) dvd (lcm (elem_ord a) (elem_ord b))"   by (metis (no_types, lifting) B0 B6 B8 aford amem bford bmem bot_nat_0.not_eq_extremum closed div_greater_zero_iff div_mult_swap elem_ord_exp elem_pow_eq_id gcd_dvd2 gcd_le2_nat gcd_pos_nat lcm_nat_def)
qed

definition set_exponents where "set_exponents A \<equiv> {n::nat. 0<n \<and> (\<forall>a. a \<in> A \<longrightarrow> a^n = e)}"

end



locale commutative_monoid=monoid X "(\<cdot>)" e for X and f (infixl "\<cdot>" 70) and e+
    assumes commutes:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y = y \<cdot> x"
begin
lemma lcomm:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)" using associate3 commutes by force
lemma idmem_simp[simp]:"e \<in> X"  by (simp add: idmem)
lemma commutative_monoidI: "(\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow>    (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)) \<Longrightarrow>e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x \<and> x \<cdot> e = x) \<Longrightarrow>     (\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow> commutative_monoid X f e" using commutative_monoid_axioms by blast
lemma commutative_monoidI2:"(\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow>  (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)) \<Longrightarrow> (e \<in> X) \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x) \<Longrightarrow>   (\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow> commutative_monoid X f e"  using commutative_monoid_axioms by blast
lemma commutative_monoidI3:"monoid X f e \<Longrightarrow>  (\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow> commutative_monoid X f e"  by (simp add: commutative_monoid_axioms)



end


declare [[show_hyps=true,show_main_goal=true, thy_output_display=true,trace_locales=false]]

locale subgroup=group G "(\<cdot>)" e for H and G and f (infixl "\<cdot>" 70) and unit ("e")+
  assumes subset:"H \<subseteq> G" and
          closed:"\<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H" and
          id_mem:"e \<in> H" and
          inv_cl:"a \<in> H \<Longrightarrow> inv_elem a \<in> H"
begin
lemma sub_mem[intro,simp]:"a \<in> H \<Longrightarrow> a \<in> G" using subset by auto
sublocale sub:group H "(\<cdot>)" e  by (metis closed group.invertible group_axioms id_mem inv_cl monoid_subgroup.axioms(2) monoid_subgroupI2 sub_mem subset) 
sublocale submonoid:submonoid H G f e  by (simp add: id_mem monoid_axioms sub.closed submonoidI subset)
lemma subgroup_inverse_equality [simp]: "u \<in> H \<Longrightarrow> inv_elem u = sub.inv_elem u"  by (simp add: inverse_equality)
end

context group
begin

lemma subgroupI1:
  assumes subset: "H \<subseteq> X" and non_empty: "H \<noteq> {}"
    and closed: "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H"
    and inv_cl: "\<And>a. a \<in> H \<Longrightarrow> inv_elem a \<in> H"
  shows "subgroup H X f e"
  apply(unfold_locales)
  apply(auto simp add:subset closed inv_cl)
proof-
  obtain a where A0:"a \<in> H"  using non_empty by auto 
  then obtain A1:"inv_elem a \<in> H"  using inv_cl by auto
  have "e = a \<cdot> inv_elem a"  using A0 A1 subset by auto
  also have "... \<in> H" using A0 A1 closed by blast
  finally show "e \<in> H" by blast
qed

lemma subgroupE1:
  assumes "subgroup H X f e"
  shows "H \<subseteq> X" and "H \<noteq> {}" and "\<And>a. a \<in> H \<Longrightarrow> inv_elem a \<in> H" and "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
  using assms unfolding subgroup_def subgroup_axioms_def by(auto)+
  

end

section Subgroups
context subgroup
begin


lemma assoc_cancel:"a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> (b \<cdot> inv_elem a) \<cdot> (a \<cdot> h) = b \<cdot> h"  using remove_id1 by blast

lemma lcoset_absorb:"g \<in> G \<Longrightarrow> g \<in> l_coset g H" by (metis id_mem l_coset_memI rightid) 
lemma rcoset_absorb:"g \<in> G \<Longrightarrow> g \<in> r_coset H g" by (metis id_mem r_coset_memI leftid) 
lemma l_coset_sub:"g \<in> G \<Longrightarrow> l_coset g H \<subseteq> G" by (simp add: l_coset_prod set_prod_closed subset)
lemma r_coset_sub:"g \<in> G \<Longrightarrow> r_coset H g \<subseteq> G" by (simp add: r_coset_prod set_prod_closed subset)
lemma l_coset_sub_mem:"g \<in> G \<Longrightarrow> b \<in> l_coset g H \<Longrightarrow> b \<in>  G" using l_coset_sub by blast
lemma r_coset_sub_mem:"g \<in> G \<Longrightarrow> b \<in> r_coset H g \<Longrightarrow> b \<in>  G" using r_coset_sub by blast

lemma coset_absorb_iff:
  assumes "a \<in> G"
  shows "l_coset a H = H \<longleftrightarrow> a \<in> H" and  "r_coset H a = H \<longleftrightarrow> a \<in> H"
proof-
  show  "l_coset a H = H \<longleftrightarrow> a \<in> H"
  proof
    assume A0:"l_coset a H = H"
    have "a = a \<cdot> e" by (simp add: assms rightid)
    also have "... \<in> l_coset a H"  by (simp add: id_mem l_coset_memI)
    finally show "a \<in> H" by (simp add:A0)
    next
    assume A0:"a \<in> H"
    show "l_coset a H = H"
    proof
      show "l_coset a H \<subseteq> H"    using A0 sub.closed by auto
      next 
      show "H \<subseteq> l_coset a H"
      proof
        fix h assume "h \<in> H"
        then obtain "inv_elem a \<cdot> h \<in> H"  using A0 sub.closed by auto
        then have "h = e \<cdot> h" using \<open>(h::'a) \<in> (H::'a set)\<close> sub.leftid by presburger
        also have "... = (a \<cdot> inv_elem a) \<cdot> h"   by (simp add: assms)
        also have "... = a \<cdot> (inv_elem a \<cdot> h)"   by (meson A0 \<open>(h::'a) \<in> (H::'a set)\<close> inv_cl sub.associative)
        also have "... \<in> l_coset a H" using \<open>inv_elem (a::'a) \<cdot> (h::'a) \<in> (H::'a set)\<close> by blast
        finally show "h \<in> l_coset a H" by simp
      qed
    qed
  qed
  show  "r_coset H a = H \<longleftrightarrow> a \<in> H"
  proof
    assume A0:"r_coset H a = H"
    have "a = e \<cdot> a" by (simp add: assms leftid)
    also have "... \<in> r_coset H a"  by (simp add: id_mem r_coset_memI)
    finally show "a \<in> H" by (simp add:A0)
    next
    assume A0:"a \<in> H"
    show "r_coset H a = H"
    proof
      show "r_coset H a \<subseteq> H" using A0 sub.closed by auto
      next 
      show "H \<subseteq> r_coset H a"
      proof
        fix h assume "h \<in> H"
        then obtain "h \<cdot> inv_elem a  \<in> H" using A0 sub.closed by auto
        then have "h = h \<cdot> e" using \<open>(h::'a) \<in> (H::'a set)\<close> sub.rightid by presburger
        also have "... = h \<cdot>(inv_elem a \<cdot> a)"   by (simp add: assms)
        also have "... = (h \<cdot> inv_elem a) \<cdot> a"   by (simp add: \<open>(h::'a) \<in> (H::'a set)\<close> assms associative)  
        also have "... \<in> r_coset H a"   by (simp add: \<open>(h::'a) \<cdot> inv_elem (a::'a) \<in> (H::'a set)\<close> r_coset_memI) 
        finally show "h \<in> r_coset H a " by simp
      qed
    qed
  qed
qed

lemma coset_assoc:
  assumes A0:"a \<in> G" "b \<in> G"
  shows "l_coset (a \<cdot> b) H = l_coset a (l_coset b H)" and "r_coset H  (a \<cdot> b) = r_coset (r_coset H a) b"
proof-
  have "\<And>x. x \<in> l_coset (a \<cdot> b) H \<longleftrightarrow> x \<in> l_coset a (l_coset b H)"
  proof-
    fix x
    have  "x \<in>l_coset (a \<cdot> b) H \<longleftrightarrow> (\<exists>h \<in> H. x =(a \<cdot> b) \<cdot> h)" by blast
    also have "... \<longleftrightarrow> (\<exists>h \<in> H. x = a \<cdot> (b \<cdot> h))"  by (simp add: assms(1) assms(2) associative)
    also have "... \<longleftrightarrow> (\<exists>bh \<in> (l_coset b H). x = a \<cdot> bh)" by blast
    also have "... \<longleftrightarrow> x \<in>l_coset a (l_coset b H)" by blast
    finally show "x \<in> l_coset (a \<cdot> b) H \<longleftrightarrow> x \<in> l_coset a (l_coset b H)" by simp
  qed
  then show "l_coset (a \<cdot> b) H = l_coset a (l_coset b H)" by auto
  have  "\<And>x. x \<in> r_coset H  (a \<cdot> b) \<longleftrightarrow> x \<in> r_coset (r_coset H a) b"
  proof-
    fix x
    have  "x \<in> r_coset H  (a \<cdot> b) \<longleftrightarrow> (\<exists>h \<in> H. x =h \<cdot> (a \<cdot> b))" by blast
    also have "... \<longleftrightarrow> (\<exists>h \<in> H. x = (h \<cdot>a) \<cdot> b)"  by (simp add: assms(1) assms(2) associative)
    also have "... \<longleftrightarrow> (\<exists>ha \<in> (r_coset H a). x = ha \<cdot> b)" by blast
    also have "... \<longleftrightarrow> x \<in>r_coset (r_coset H a) b" by blast
    finally show "x \<in> r_coset H  (a \<cdot> b) \<longleftrightarrow> x \<in> r_coset (r_coset H a) b" by simp
  qed
  then show  "r_coset H  (a \<cdot> b) = r_coset (r_coset H a) b" by blast
qed

lemma lcoset_mem:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> (f (inv_elem x) y \<in> H)  \<longleftrightarrow> (y \<in> (l_coset x H))"
proof-
  fix x y assume A0:"x \<in> G" "y \<in> G" 
  obtain A1:"inv_elem x \<in> G" using A0 by blast
  then have "(f (inv_elem x)  y) \<in> H \<longleftrightarrow> f x (f (inv_elem x)  y) \<in> l_coset x H"  by (metis A0 inv_left_cancel invertible invertible_right_inverse2 l_coset_memE l_coset_memI sub_mem)
  also have "... \<longleftrightarrow> f (f x (inv_elem x)) y \<in> (l_coset x H)"  using A0 A1 associative by presburger
  also have "... \<longleftrightarrow> y \<in> (l_coset x H)"   by (simp add: A0 leftid)
  finally show "(f (inv_elem x) y \<in> H)  \<longleftrightarrow> (y \<in> (l_coset x H))" by blast
qed

lemma rcoset_mem:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> (f y (inv_elem x) \<in> H)  \<longleftrightarrow> (y \<in> (r_coset H x))"
proof-
  fix x y assume A0:"x \<in> G" "y \<in> G" 
  obtain A1:"inv_elem x \<in> G" using A0 by blast
  then have " (f y (inv_elem x) \<in> H) \<longleftrightarrow> f (f y (inv_elem x)) x \<in> r_coset H x "  by (smt (verit) A0(1) A0(2) group_def associative invertible invertible_right_inverse monoid.invertible_left_inverse r_coset_memE r_coset_memI rightid sub_mem subgroup.axioms(1) subgroup_axioms)
  also have "... \<longleftrightarrow> f y (f (inv_elem x) x) \<in> (r_coset H x)"  using A0 A1 associative by presburger
  also have "... \<longleftrightarrow> y \<in> (r_coset H x)"  by (simp add: A0 rightid)
  finally show "(f y (inv_elem x) \<in> H) \<longleftrightarrow> y \<in> (r_coset H x)" by blast
qed


lemma l_coset_bij:"g \<in> G \<Longrightarrow> bij_betw (\<lambda>x. g\<cdot>x) H (l_coset g H)" by(auto simp add:bij_betw_def, auto intro: inj_onI)
lemma r_coset_bij:"g \<in> G \<Longrightarrow> bij_betw (\<lambda>x. x\<cdot>g) H (r_coset H g)" by(auto simp add:bij_betw_def, auto intro: inj_onI)



lemma l_coset_inj:
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "inj_on (\<lambda>x. inv_elem (a \<cdot> inv_elem b) \<cdot> x)  (l_coset a H)" and
        "inj_on (\<lambda>x. inv_elem (a \<cdot> inv_elem b) \<cdot> x)  (l_coset b H)" and
        "inj_on (\<lambda>x. (b \<cdot> inv_elem a) \<cdot> x)  (l_coset a H)" and
        "inj_on (\<lambda>x. (b \<cdot> inv_elem a) \<cdot> x)  (l_coset b H)"
proof-
  let ?c="inv_elem (a \<cdot> inv_elem b)"
  obtain B0:"?c\<in>G" using A0 A1 double_inv_prod by blast
  show P0:"inj_on (\<lambda>x. inv_elem (a \<cdot> inv_elem b) \<cdot> x)  (l_coset a H)"
  proof(rule inj_onI)
    fix x y assume A2:"x \<in> l_coset a H" and A3:" y \<in>l_coset a H" and  A4:"?c \<cdot> x = ?c \<cdot> y"
    then show "x = y" using left_cancellation[of ?c x y]  A0 B0 l_coset_sub_mem by blast
  qed
  show P1:"inj_on (\<lambda>x. inv_elem (a \<cdot> inv_elem b) \<cdot> x)  (l_coset b H)"
  proof(rule inj_onI)
    fix x y assume A2:"x \<in> l_coset b H" and A3:" y \<in>l_coset b H" and  A4:"?c \<cdot> x = ?c \<cdot> y"
    then show "x = y" using left_cancellation[of ?c x y] A1 B0 l_coset_sub_mem by presburger 
  qed
  have B1:"inv_elem (a \<cdot> inv_elem b) = (b \<cdot> inv_elem a)"  by (simp add: A0 A1 invprod)
  show P2:"inj_on (\<lambda>x. (b \<cdot> inv_elem a) \<cdot> x)  (l_coset a H)" using B1 P0 by presburger 
  show P2:"inj_on (\<lambda>x. (b \<cdot> inv_elem a) \<cdot> x)  (l_coset b H)" using B1 P1 by presburger 
qed

lemma r_coset_inj:
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "inj_on (\<lambda>x. x \<cdot> (inv_elem b \<cdot> a)) (r_coset H a)" and
        "inj_on (\<lambda>x. x \<cdot> (inv_elem b \<cdot> a)) (r_coset H b)" and
        "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv_elem a)) (r_coset H a)" and
        "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv_elem a)) (r_coset H b)" and
        "inj_on (\<lambda>x. x \<cdot> (inv_elem a \<cdot> b)) (r_coset H a)"       
proof -
  let ?c = "inv_elem b \<cdot> a"
  have B0:"?c \<in> G"  by (simp add: A0 A1 magma.closed magma_axioms) 
  show "inj_on (\<lambda>x. x \<cdot> (inv_elem b \<cdot> a)) (r_coset H a)"
  proof (rule inj_onI)
    fix x y assume "x \<in> r_coset H a" and "y \<in> r_coset H a" and "x \<cdot> ?c = y \<cdot> ?c"
    then show "x = y" using  A0 B0 r_coset_sub_mem right_cancellation[of ?c x y] by blast
  qed
  show "inj_on (\<lambda>x. x \<cdot> (inv_elem b \<cdot> a)) (r_coset H b)"
  proof (rule inj_onI)
    fix x y assume "x \<in> r_coset H b" and "y \<in> r_coset H b" and "x \<cdot> ?c = y \<cdot> ?c"
    then show "x = y" using  A1 B0 r_coset_sub_mem right_cancellation[of ?c x y] by blast
  qed
  have B3:"inv_elem (a \<cdot> inv_elem b) = (b \<cdot> inv_elem a)"  by (simp add: A0 A1 invprod(2))
  have B4:"(b \<cdot> inv_elem a) \<in> G"    by (simp add: A0 A1 magma.closed magma_axioms)
  show "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv_elem a)) (r_coset H a)"  by (meson A0 B4 inj_onI r_coset_sub_mem right_cancellation) 
  show "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv_elem a)) (r_coset H b)" by (meson A1 B4 inj_onI r_coset_sub_mem right_cancellation)    
  show "inj_on (\<lambda>x. x \<cdot> (inv_elem a \<cdot> b)) (r_coset H a)"   by(auto simp add:inj_on_def,metis A0 A1 invertible invertible_inverse_closed magma.closed magma_axioms r_coset_sub_mem right_cancellation)
qed    
 


lemma coset_bij1: 
  assumes A0:"a \<in> G"
  shows "bij_betw (\<lambda>x. inv_elem x) (l_coset a H) (r_coset H (inv_elem a))"
proof(auto simp add:bij_betw_def)
  show "inj_on inv_elem (l_coset a H)"  by (metis A0 inj_onI invertible invertible_inverse_inverse l_coset_sub_mem)
  show "\<And>x. x \<in> (l_coset a H) \<Longrightarrow> inv_elem x \<in> (r_coset H (inv_elem a))" using assms monoid.invprod(2) monoid_axioms by fastforce
  show "\<And>x. x \<in> r_coset H( inv_elem a) \<Longrightarrow> x \<in> inv_elem ` (l_coset a H)"   by (metis assms imageI inv_cl invertible invertible_inverse_closed invertible_inverse_inverse invprod(2) lcoset_mem r_coset_sub_mem rcoset_mem)
qed

lemma coset_bij2: 
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "bij_betw (\<lambda>x. b \<cdot> inv_elem a \<cdot> x) (l_coset a H) (l_coset b H)" 
proof-
  show "bij_betw (\<lambda>x. b \<cdot> inv_elem a \<cdot> x) (l_coset a H) (l_coset b H)"
  proof(auto simp add:bij_betw_def)
    show "inj_on (\<lambda>x. b \<cdot> inv_elem a \<cdot> x)  (l_coset a H)"  by (simp add: A0 A1 l_coset_inj(3))
    show "\<And>x. x \<in> (l_coset a H) \<Longrightarrow> b \<cdot> inv_elem a \<cdot> x \<in> (l_coset b H)"
    proof-
      fix x assume "x \<in> (l_coset a H) " then obtain h where "h \<in> H" and "x = a \<cdot> h" by auto
      then have "(b \<cdot> inv_elem a) \<cdot> x = (b \<cdot> inv_elem a) \<cdot> (a \<cdot> h)" by blast
      also have "... = b \<cdot> h"   using A0 A1 \<open>(h::'a) \<in> (H::'a set)\<close> remove_id1 by blast
      also have "... \<in> l_coset b H" using \<open>(h::'a) \<in> (H::'a set)\<close> by auto
      finally show "b \<cdot> inv_elem a \<cdot> x \<in> (l_coset b H)" by blast
    qed
    show "\<And>x. x \<in> l_coset b H \<Longrightarrow> x \<in> (\<lambda>x. b \<cdot> inv_elem a \<cdot> x) ` (l_coset a H)"
    proof-
      fix x assume B0:"x \<in> (l_coset b H) " then obtain h where B1:"h \<in> H" and B2:"x = b \<cdot> h" by auto
      then have "b \<cdot> h = b \<cdot> (inv_elem a \<cdot> a) \<cdot> h"  by (simp add: A0 A1 rightid)
      also have "... = (b \<cdot> inv_elem a) \<cdot> (a \<cdot> h)"using A0 A1 B1 calculation remove_id1 sub_mem by presburger
      also have "... \<in> (\<lambda>x. b \<cdot> inv_elem a \<cdot> x) ` (l_coset a H)" using B1 by blast
      finally show "x \<in> (\<lambda>x. b \<cdot> inv_elem a \<cdot> x) ` (l_coset a H)"  using B2 by fastforce
    qed
  qed
qed


lemma coset_eq_iff:
  assumes A0:"a \<in>G" and A1:"b \<in> G"
  shows "l_coset a H = l_coset b H \<longleftrightarrow>  a \<in> l_coset b H" and
        "l_coset a H = l_coset b H \<longleftrightarrow> inv_elem a \<cdot> b \<in> H" and
        "r_coset H a = r_coset H b \<longleftrightarrow> b \<in> r_coset H a" and
        "r_coset H a = r_coset H b \<longleftrightarrow> b\<cdot> inv_elem a  \<in> H"
proof-
  show P0:"l_coset a H = l_coset b H \<longleftrightarrow>  a \<in> l_coset b H"
    by (metis A0 A1 coset_absorb_iff(1) coset_assoc(1) l_coset_memE lcoset_absorb sub_mem) 
  show P1: "l_coset a H = l_coset b H \<longleftrightarrow> inv_elem a \<cdot> b \<in> H"
    by (metis A0 A1 coset_absorb_iff(1) coset_assoc(1) l_coset_memE lcoset_absorb lcoset_mem sub_mem) 
  show P2:"r_coset H a = r_coset H b \<longleftrightarrow> b \<in> r_coset H a"
    by (metis A0 A1 coset_absorb_iff(2) coset_assoc(2) r_coset_memE rcoset_absorb sub_mem) 
  show P3:"r_coset H a = r_coset H b \<longleftrightarrow> b\<cdot> inv_elem a  \<in> H"
    by (simp add: A0 A1 P2 rcoset_mem)
qed

lemma l_coset_eq_or_disjoint:
  assumes A0:"a \<in> G" and A1:"b \<in> G" and A2:"l_coset a H \<inter> l_coset b H \<noteq> {}" 
  shows "l_coset a H = l_coset b H"
  by (metis A0 A1 A2 Int_emptyI coset_eq_iff(1) l_coset_sub_mem)

lemma r_coset_eq_or_disjoint:
  assumes A0:"a \<in> G" and A1:"b \<in> G" and A2:"r_coset H a \<inter> r_coset H b \<noteq> {}" 
  shows "r_coset H a = r_coset H b"
  by (metis A0 A1 A2 coset_eq_iff(3) disjoint_iff r_coset_sub_mem)

lemma l_coset_card1:"\<lbrakk> x \<in> G; y \<in> G \<rbrakk> \<Longrightarrow> card (l_coset x H) = card (l_coset y H)" by (fast intro: bij_betw_same_card coset_bij2)
lemma r_coset_card1:"\<lbrakk> x \<in> G; y \<in> G \<rbrakk> \<Longrightarrow> card (r_coset H x) = card (r_coset H y)" by (metis bij_betw_same_card r_coset_bij)
lemma l_coset_card2:"\<lbrakk> x \<in> G\<rbrakk> \<Longrightarrow> card (l_coset x H) = card (r_coset H x)"  by (metis bij_betw_same_card l_coset_bij r_coset_bij) 
lemma r_coset_card2:"\<lbrakk> x \<in> G\<rbrakk> \<Longrightarrow> card (r_coset H x) = card (r_coset H x)" by (metis bij_betw_same_card r_coset_bij)

lemma l_coset_id: "l_coset e H = H" by (simp add: coset_absorb_iff(1) id_mem)
lemma r_coset_id: "r_coset H e = H" by (simp add: coset_absorb_iff(2) id_mem)

theorem l_coset_card3:  "x \<in> G \<Longrightarrow> card (l_coset x H) = card H" using idmem l_coset_card1 l_coset_id by presburger
theorem r_coset_card3:  "x \<in> G \<Longrightarrow> card (r_coset H x) = card H" using idmem r_coset_card1 r_coset_id by presburger


definition l_sub_eq where "l_sub_eq \<equiv> {(x, y) \<in> G \<times> G. (inv_elem x)\<cdot>y \<in> H}" 
definition r_sub_eq where "r_sub_eq \<equiv> {(x, y) \<in> G \<times> G. y\<cdot>(inv_elem x) \<in> H}" 

lemma id_in_l_sub_eq:"(e,e) \<in> l_sub_eq" by (simp add: l_sub_eq_def rightid sub.idmem)
lemma id_in_r_sub_eq:"(e,e) \<in> r_sub_eq" by (simp add: r_sub_eq_def leftid sub.idmem)
lemma l_sub_eq_mem:"x \<in> G \<Longrightarrow> (x,x)\<in> l_sub_eq" using coset_eq_iff(2) l_sub_eq_def by blast
lemma r_sub_eq_mem:"x \<in> G \<Longrightarrow> (x,x)\<in> r_sub_eq" using coset_eq_iff(4) r_sub_eq_def by blast
lemma l_sub_eq_refl:"refl_on G l_sub_eq" apply(simp add:id_mem refl_on_def l_sub_eq_def)  using id_mem by blast
lemma r_sub_eq_refl:"refl_on G r_sub_eq" apply(simp add:id_mem refl_on_def r_sub_eq_def)  using id_mem by blast
lemma l_sub_eq_sym:"sym l_sub_eq" unfolding l_sub_eq_def apply(auto simp add:sym_def) using coset_eq_iff(2) by blast
lemma r_sub_eq_sym:"sym r_sub_eq" unfolding r_sub_eq_def apply(auto simp add:sym_def) using coset_eq_iff(4) by blast
lemma l_sub_eq_trans:"trans l_sub_eq" unfolding l_sub_eq_def apply(auto simp add:trans_on_def)  by (metis coset_eq_iff(2))
lemma r_sub_eq_trans:"trans r_sub_eq" unfolding r_sub_eq_def apply(auto simp add:trans_on_def)  by (metis coset_eq_iff(4))
lemma l_sub_eqr:"is_eqrel G l_sub_eq"  by (simp add: is_eqrel_def l_sub_eq_refl l_sub_eq_sym l_sub_eq_trans) 
lemma r_sub_eqr:"is_eqrel G r_sub_eq"  by (simp add: is_eqrel_def r_sub_eq_refl r_sub_eq_sym r_sub_eq_trans)


(*
lemma prp215:
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "l_coset a H = l_coset b H \<longleftrightarrow> (inv_elem a) \<cdot> b \<in> H" and
        "l_coset a H = l_coset b H \<longleftrightarrow> (inv_elem b) \<cdot> a \<in> H" and
        "r_coset H a = r_coset H b \<longleftrightarrow> b \<cdot> (inv_elem a) \<in> H" and
        "r_coset H a = r_coset H b \<longleftrightarrow> a \<cdot> (inv_elem b)\<in> H"
proof-
   show P0:"l_coset a H = l_coset b H \<longleftrightarrow> (inv_elem a) \<cdot> b \<in> H"
     using A0 A1 coset_eq_iff(2) by presburger 
   show P1:"l_coset a H = l_coset b H \<longleftrightarrow> (inv_elem b) \<cdot> a \<in> H"
     using A0 A1 coset_eq_iff(2) by blast 
   show P2:"r_coset H a = r_coset H b \<longleftrightarrow> b \<cdot> (inv_elem a) \<in> H"
     by (simp add: A0 A1 coset_eq_iff(3) rcoset_mem) 
   show P3:"r_coset H a = r_coset H b \<longleftrightarrow> a \<cdot> (inv_elem b)\<in> H"
     using A0 A1 coset_eq_iff(4) by blast
qed*)

definition r_cosets  where "r_cosets = (\<Union>g\<in>G. {r_coset H g})"
definition l_cosets  where "l_cosets = (\<Union>g\<in>G. {l_coset g H})"

lemma r_cosets_memD:"t \<in>r_cosets \<Longrightarrow> \<exists>g \<in> G. t = r_coset H g" unfolding r_cosets_def by blast
lemma l_cosets_memD:"t \<in>l_cosets \<Longrightarrow> \<exists>g \<in> G. t = l_coset g H" unfolding l_cosets_def by blast


lemma r_cosets_memD2:"t \<in>r_cosets \<Longrightarrow> g \<in> G \<Longrightarrow> t = r_coset H g \<Longrightarrow> g \<in> t"  using rcoset_absorb by auto 
lemma l_cosets_memD2:"t \<in>l_cosets \<Longrightarrow> g \<in> G \<Longrightarrow> t = l_coset g H \<Longrightarrow> g \<in> t"  using lcoset_absorb by auto 



lemma r_cosets_memD3:"t \<in>r_cosets \<Longrightarrow> t \<subseteq> G" using r_coset_sub r_cosets_memD by blast 
lemma l_cosets_memD3:"t \<in>l_cosets \<Longrightarrow> t \<subseteq> G" using l_coset_sub l_cosets_memD by blast 


lemma r_cosets_memI1:"g \<in> G\<Longrightarrow> r_coset H g \<in> r_cosets" unfolding r_cosets_def by(auto)
lemma l_cosets_memI1:"g \<in> G\<Longrightarrow> l_coset g H \<in> l_cosets" unfolding l_cosets_def by(auto)


lemma r_cosets_ne:"t \<in> r_cosets \<Longrightarrow> t \<noteq> {}"  using r_cosets_memD rcoset_absorb by auto
lemma l_cosets_ne:"t \<in> l_cosets \<Longrightarrow> t \<noteq> {}"  using l_cosets_memD lcoset_absorb by auto

lemma r_cosets_disj:"t \<in> r_cosets \<Longrightarrow> s \<in> r_cosets \<Longrightarrow> t \<inter> s \<noteq> {} \<Longrightarrow> t = s"  by (metis r_coset_eq_or_disjoint r_cosets_memD)
lemma l_cosets_disj:"t \<in> l_cosets \<Longrightarrow> s \<in> l_cosets \<Longrightarrow> t \<inter> s \<noteq> {} \<Longrightarrow> t = s"  by (metis l_coset_eq_or_disjoint l_cosets_memD)
lemma r_cosets_card:"t \<in> r_cosets \<Longrightarrow> card t = card H" using r_coset_card3 r_cosets_memD by blast
lemma l_cosets_card:"t \<in> l_cosets \<Longrightarrow> card t = card H" using l_coset_card3 l_cosets_memD by blast
lemma r_cosets_un:"\<Union>r_cosets = G" apply(rule order_antisym) using r_cosets_memD3 apply blast  using r_cosets_memD2 r_cosets_memI1 by blast
lemma l_cosets_un:"\<Union>l_cosets = G" apply(rule order_antisym) using l_cosets_memD3 apply blast  using l_cosets_memD2 l_cosets_memI1 by blast


lemma lagrange_l:
  "(card H) * (card r_cosets) = card G"
  by (metis (no_types, lifting) card_eq_0_iff card_partition finite_Union finite_UnionD mult.commute mult_0_right r_cosets_card r_cosets_disj r_cosets_un)

lemma lagrange_r:
  "(card H) * (card l_cosets) = card G"
  by (metis card.infinite card_partition finite_Union finite_UnionD l_cosets_card l_cosets_disj l_cosets_un mult_is_0)




end



context group
begin

 
end 



lemma monoid_subgroupD:
  assumes "group G f e" and "monoid_subgroup H G f e"
  shows "H \<subseteq> G" and "\<And>h1 h2. \<lbrakk>h1 \<in> H; h2 \<in> H\<rbrakk> \<Longrightarrow> f h1 h2 \<in> H" and "e \<in> H"
  apply (meson assms(2) monoid_subgroup_submonoid submonoid.setsub)
  apply (meson assms(2) monoid_subgroup_submonoid submonoid.opsub)
  by (meson assms(2) monoid_subgroup_submonoid submonoid.idsub)



locale group_homomorphism=set_morphism f X Y+ dom:group X "(\<cdot>)" e + cod:group Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) and e and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)" 
begin
lemma map_id:"f e = d" by (metis cmp cod cod.idmem cod.leftid cod.right_cancellation dom.idmem dom.leftid) 
lemma map_inv_id:
  assumes A0:"x \<in> X"
  shows "d =  (f x)\<star>(f (dom.inv_elem x))" and "d = (f (dom.inv_elem x))\<star>(f x)"
proof-
  have "d = f e" by (simp add: map_id)
  also have "... =  f (x \<cdot> (dom.inv_elem x))" by(simp add:A0)
  also have "... = (f x)\<star>(f (dom.inv_elem x))"  using A0 cmp by blast
  finally show "d =  (f x)\<star>(f (dom.inv_elem x))" by blast
  have "d = f e" by (simp add: map_id)
  also have "... =  f ((dom.inv_elem x)\<cdot> x)" by(simp add:A0)
  also have "... = (f (dom.inv_elem x))\<star>(f x)"  using A0 cmp by blast
  finally show "d =  (f (dom.inv_elem x))\<star>(f x)" by blast
qed

lemma map_inv:"x \<in> X \<Longrightarrow> cod.inv_elem (f x) = f (dom.inv_elem x)"  using cod.inverse_equality map_inv_id by auto
lemma map_ord1:assumes "x \<in> X" shows " f (dom.pow_nat x n) = cod.pow_nat (f x) n"
proof(induct n)
  case 0 then show ?case  by (simp add: map_id) next
  case (Suc n) then show ?case    by (simp add: assms cmp) 
qed

lemma map_ord2:"x \<in> X \<Longrightarrow> dom.elem_ord x \<noteq> 0 \<Longrightarrow> cod.elem_ord (f x) dvd dom.elem_ord x"
proof-
  assume A0:"x \<in> X" and A1:"dom.elem_ord x \<noteq> 0"
  have "dom.pow_nat x (dom.elem_ord x) = e"   by (simp add: dom.elem_ord_exp)
  then have "cod.pow_nat (f x) (dom.elem_ord x) = cod.pow_nat (f e) (dom.elem_ord x)"by (metis A0 cod.power_one map_id map_ord1)
  also have "... = d"  by (simp add: map_id)
  finally show "cod.elem_ord (f x) dvd dom.elem_ord x"  by (metis (mono_tags, lifting) A0 A1 Collect_empty_eq cod cod.elem_exponents_def cod.elem_ord_def cod.order_divides_exponent gr0I less_irrefl mem_Collect_eq wellorder_Least_lemma(1))
qed
lemma tempker:"x \<in> X \<Longrightarrow> f x = d \<Longrightarrow> y \<in> X \<Longrightarrow> f y = d \<Longrightarrow> f (x \<cdot> y) = d"  by (simp add: cmp cod.idmem cod.leftid)
definition Ker where "Ker \<equiv> {x \<in> X. f x = d}"
lemma Ker_equality: "Ker = {x \<in> X. f x = d}"unfolding Ker_def by auto
lemma Ker_closed[intro, simp]:"a \<in> Ker \<Longrightarrow> a \<in>X"  unfolding Ker_def by simp
lemma Ker_image[intro]:"a \<in> Ker \<Longrightarrow> f a = d" unfolding Ker_def by simp
lemma Ker_memI1:"\<lbrakk>f a = d; a\<in>X\<rbrakk> \<Longrightarrow> a \<in> Ker" unfolding Ker_def by simp
lemma Ker_opc:"a \<in> Ker \<Longrightarrow> b \<in> Ker \<Longrightarrow> (a \<cdot> b) \<in> Ker"  by (meson Ker_closed Ker_image Ker_memI1 dom.closed tempker)
lemma ker_inc:"a \<in> Ker \<Longrightarrow> dom.inv_elem a \<in> Ker"  by (metis Ker_closed Ker_image Ker_memI1 cod.inv_ident dom.invertible dom.invertible_inverse_closed map_inv)
lemma Ker_memI2:assumes A0:"x \<in> X" and A1:"k \<in> Ker" shows "(dom.inv_elem x) \<cdot> k \<cdot> x \<in> Ker" by (metis (full_types) A0 A1 Ker_closed Ker_image Ker_memI1 cmp dom.closed dom.idmem dom.invertible dom.invertible_inverse_closed dom.rightid map_id map_inv_id(2))
lemma Ker_sub:"subgroup Ker X (\<cdot>) e" 
  apply(unfold_locales)
  apply (simp add: subsetI)
  apply (simp add: Ker_opc)
  apply (simp add: Ker_memI1 dom.idmem map_id)
  by (simp add: ker_inc)

lemma injD:"set_monomorphism f X Y \<Longrightarrow> Ker = {e} " 
  apply(auto simp add:set_monomorphism_def inj_locale_def) 
  apply (simp add: Ker_image dom.idmem inj_onD map_id)
  by (simp add: Ker_memI1 dom.idmem map_id)

lemma injI:" Ker = {e}  \<Longrightarrow> set_monomorphism f X Y " 
  apply(auto simp add:set_monomorphism_def inj_locale_def)
  apply (simp add: set_morphism_axioms) 
  apply(auto simp add:inj_on_def)
  by (metis Ker_memI1 cmp dom.closed dom.invertible dom.invertible_def dom.right_cancellation map_id singletonD)
end

locale group_epimorphism=set_epimorphism f X Y+ dom:group X "(\<cdot>)" e + cod:group Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) and e and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale group_homomorphism by(unfold_locales,simp add: cmp)
end

locale group_monomorphism=set_monomorphism f X Y+ dom:group X "(\<cdot>)" e + cod:group Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) and e and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale group_homomorphism by(unfold_locales,simp add: cmp)
lemma ker_id:"Ker = {e}" by (simp add: injD set_monomorphism_axioms) 
end
           
locale abelian_group=group X "(\<cdot>)" e+comm_locale X "(\<cdot>)" for X and f (infixl "\<cdot>" 70) and e 

locale group_isomorphism=set_isomorphism f X Y+ dom:group X "(\<cdot>)" e + cod:group Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) and e and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale group_homomorphism by(unfold_locales,simp add: cmp)
sublocale group_epimorphism by(unfold_locales,simp add: cmp)
sublocale group_monomorphism by(unfold_locales,simp add: cmp)
lemma ker_id:"Ker = {e}" by (simp add: injD set_monomorphism_axioms) 
lemma card_eq:"card X = card Y" using bij_betw_same_card by blast

end


context magma
begin
inductive_set magma_generated::"'a set \<Rightarrow> 'a set" for A where
 iso:"a \<in> A \<Longrightarrow> a \<in> magma_generated A"
 |opc:"a \<in> magma_generated A \<Longrightarrow> b \<in> magma_generated A \<Longrightarrow> a\<cdot>b \<in> magma_generated A"

lemma generate_into: "a \<in> magma_generated (X \<inter> A) \<Longrightarrow> a \<in> X"
  apply (induction rule: magma_generated.induct)
  apply simp
  by (simp add: closed)

definition cl_magma :: "'a set \<Rightarrow> 'a set"  where "cl_magma S = magma_generated (X \<inter> S)"

lemma cl_magma_sub:"cl_magma H \<subseteq> X" using cl_magma_def generate_into by auto
lemma cl_submgama: "submagma (cl_magma H) X (\<cdot>)"  by (metis cl_magma_def cl_magma_sub magma_generated.opc magma_axioms submagmaI)

lemma cl_magma_ub:
  assumes A0:"A \<subseteq> B" and A1:"submagma B X (\<cdot>)" 
  shows "cl_magma A \<subseteq> B"
proof
  fix x assume "x \<in> cl_magma A"
  then show "x \<in> B"
    unfolding cl_magma_def
    apply(induction rule: magma_generated.induct)
    using A0 apply blast
    by (meson A1 submagma.subfun)
qed

lemma cl_magma_iso:
  assumes A0:"A \<subseteq> B"  shows "cl_magma A \<subseteq> cl_magma B"
proof
  fix x assume "x \<in> cl_magma A"
  then show "x \<in> cl_magma B" unfolding cl_magma_def
   apply(induction rule: magma_generated.induct)
    using assms magma_generated.iso apply auto[1]
    using magma_generated.opc by auto
qed

lemma cl_magma_extensive:
   assumes A0:"A \<subseteq> X" shows "A \<subseteq>cl_magma A"
proof
  fix x assume "x \<in> A" then show "x \<in>cl_magma A"  unfolding cl_magma_def  by (simp add: assms inf_absorb2 magma_generated.iso)
qed

lemma cl_magma_idempotent:
  assumes A0:"A \<subseteq> X" shows "cl_magma A = cl_magma (cl_magma A)"
  by (simp add: cl_magma_extensive cl_magma_sub cl_magma_ub cl_submgama subset_antisym)

lemma cl_magma_moore1:
  assumes A0:"A \<subseteq> X" 
  shows "cl_magma A = \<Inter>{C. submagma C X (\<cdot>) \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    by (metis (mono_tags, lifting) Inf_greatest cl_magma_ub mem_Collect_eq)
next
  show "?RHS \<subseteq> ?LHS"
    by (simp add: Inter_lower assms cl_magma_extensive cl_submgama)
qed

end
      


context group
begin
inductive_set generated::"'a set \<Rightarrow> 'a set" for A where
  idm:"e \<in> generated A"
 |iso:"a \<in> A \<Longrightarrow> a \<in> generated A"
 |inv:"a \<in> A \<Longrightarrow> inv_elem a \<in> generated A"
 |opc:"a \<in> generated A \<Longrightarrow> b \<in> generated A \<Longrightarrow> a\<cdot>b \<in> generated A"

lemma generate_into: "a \<in> generated (X \<inter> A) \<Longrightarrow> a \<in> X"
  apply (induction rule: generated.induct)
  apply (simp add: idmem)
  apply simp
  apply simp
  by (simp add: closed) 


definition cl :: "'a set \<Rightarrow> 'a set"  where "cl S = generated (X \<inter> S)"

lemma inverse_in_cl: "a \<in> cl H \<Longrightarrow> inv_elem a \<in> cl H"
  unfolding cl_def
apply(induction rule: generated.induct)
  apply (simp add: generated.idm)
  using generated.inv apply force
  using generated.iso apply force
  by (simp add: generate_into generated.opc invprod(2))

lemma cl_monoid: "monoid (cl H) (\<cdot>) e"
  unfolding cl_def monoid_def semigroup_def magma_def semigroup_axioms_def monoid_axioms_def
  apply(auto)
  using generated.opc apply auto[1]
  apply (simp add: associative generate_into)
  apply (simp add: generated.idm)
  apply (simp add: generate_into leftid)
  by (simp add: generate_into rightid)
  
lemma cl_sub: "cl H \<subseteq> X" using cl_def generate_into by auto

lemma cl_subgroup: "subgroup (cl H) X (\<cdot>) e"
  apply(rule subgroupI1)
  apply (simp add: cl_sub)
  using cl_def generated.idm apply auto[1]
  apply (simp add: cl_def generated.opc)
  by (simp add: inverse_in_cl)


end
      

end

 