theory Algebrah8
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

section \<open>Set Morphisms\<close>
definition Pi :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set" where "Pi A B = {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B x}"
definition maps_to::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  where "maps_to A B \<equiv> {f. (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)}"
definition maps_on::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) set" where "maps_on A \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined)}"
definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b" where "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"
syntax "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
translations "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"
definition compose::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where "compose A g f = (\<lambda>x\<in>A. g (f x))"
definition hom::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where "hom A B \<equiv> {f. ((\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B))}"
abbreviation Id where "Id X \<equiv> (\<lambda>x \<in> X. x)"
definition surj::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set   \<Rightarrow> 'b set \<Rightarrow> bool" where"surj f X Y \<equiv> f`X=Y"
definition rinv::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'a" where "rinv f X Y \<equiv> (\<lambda>y \<in> Y. SOME x.  x \<in> X \<and> f x = y)"
definition is_right_inv::"'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where "is_right_inv Y f s \<equiv> compose Y f s = Id Y"
definition is_left_inv ::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where "is_left_inv X f r \<equiv> compose X r f = Id X"
definition is_eqrel::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where "is_eqrel X R \<equiv> refl_on X R \<and> sym R \<and> trans R"
definition quotient::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set" (infixl "'/" 75) where "quotient X R \<equiv> (\<Union>x \<in> X. {R``{x}})"
definition eqr_comp::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where "eqr_comp X R f \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. (x, y) \<in> R \<longrightarrow> f x = f y)"
definition ker_pair::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set" where  "ker_pair X f \<equiv> {(x, y) \<in> X \<times> X. f x = f y}"
definition qproj::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set" where "qproj X R \<equiv> (\<lambda>x \<in> X. THE t. t \<in> (X/R) \<and>  x \<in> t)"
definition qsect::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a" where "qsect X R \<equiv> rinv (qproj X R) X (X/R)"
definition qmap::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where "qmap X R f \<equiv> compose (X/R) f (qsect X R)"

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
lemma maps_to_comp: "f \<in> maps_to A B \<Longrightarrow> g \<in> maps_to B C \<Longrightarrow> compose A g f \<in> maps_to A C"  by (simp add: maps_to_def compose_def restrict_def)
lemma compose_assoc:"f \<in> maps_to A B \<Longrightarrow>compose A h (compose A g f) = compose A (compose B h g) f "by (simp add: fun_eq_iff maps_to_def compose_def restrict_def)
lemma compose_eq: "x \<in> A \<Longrightarrow> compose A g f x = g (f x)" by (simp add: compose_def restrict_def)
lemma surj_compose: "f ` A = B \<Longrightarrow> g ` B = C \<Longrightarrow> compose A g f ` A = C"  by (auto simp add: image_def compose_eq)
lemma restrict_cong: "I = J \<Longrightarrow> (\<And>i. i \<in> J =simp=> f i = g i) \<Longrightarrow> restrict f I = restrict g J"  by (auto simp: restrict_def fun_eq_iff simp_implies_def)
lemma restrictI1[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> Pi A B"  by (simp add: Pi_def restrict_def)
lemma restrictI2[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> maps_to A B"  by (simp add: maps_to_def restrict_def)
lemma restrict_apply[simp]: "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"  by (simp add: restrict_def)
lemma restrict_apply1: "x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x" by simp
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

section \<open>Extensionality\<close>
lemma maps_on_memI[intro]:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> maps_on A" by (simp add: maps_on_def)
lemma maps_on_memD:"f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" by (simp add: maps_on_def)
lemma maps_on_empty[simp]: "maps_on {} = {\<lambda>x. undefined}"  unfolding maps_on_def by auto
lemma maps_on_arb: "f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined"  by (simp add: maps_on_def)
lemma restrict_maps_on [simp]: "restrict f A \<in> maps_on A" by (simp add: restrict_def maps_on_def)
lemma compose_maps_on [simp]: "compose A f g \<in> maps_on A"  by (simp add: compose_def)
lemma maps_on_equalityI:"f \<in> maps_on A \<Longrightarrow> g \<in> maps_on A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g" by (force simp add: fun_eq_iff maps_on_def)
lemma maps_on_restrict:"f \<in> maps_on A \<Longrightarrow> restrict f A = f"  by (rule maps_on_equalityI[OF restrict_maps_on]) auto
lemma maps_on_subset: "f \<in> maps_on A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f \<in> maps_on B" unfolding maps_on_def by auto
lemma maps_on_Int[simp]: "maps_on I \<inter> maps_on I' = maps_on (I \<inter> I')"  unfolding maps_on_def by auto
lemma maps_on_UNIV[simp]: "maps_on UNIV = UNIV"  by (auto simp: maps_on_def)
lemma restrict_maps_on_sub[intro]:"A \<subseteq> B \<Longrightarrow> restrict f A \<in> maps_on B"  unfolding restrict_def maps_on_def by auto
lemma maps_on_insert_cancel[intro, simp]:  "a \<in> maps_on I \<Longrightarrow> a \<in> maps_on (insert i I)"  unfolding maps_on_def by auto

lemma hom_memI1:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> hom A B" unfolding hom_def by fast
lemma hom_memI2:"f \<in> maps_on A \<Longrightarrow> f \<in>maps_to A B \<Longrightarrow> f \<in> hom A B"   by(rule hom_memI1,auto elim: maps_on_memD)
lemma hom_memD1:"f \<in> hom A B \<Longrightarrow> f \<in> maps_on A" unfolding hom_def maps_on_def by(auto)
lemma hom_memD2:"f \<in> hom A B \<Longrightarrow> f \<in> maps_to A B" unfolding hom_def maps_to_def by(auto)
lemma id1[simp]:"Id X x = (if x \<in> X then x else undefined)" by (simp add:Id_def)
lemma hom1:"hom {} Y = {\<lambda>x. undefined}"  by(auto simp add:hom_def) 
lemma hom2:"f \<in> hom A B \<Longrightarrow> g \<in> hom B C \<Longrightarrow> compose A g f \<in> hom A C" by(auto simp add:hom_def compose_def)
lemma hom3:"f \<in> hom A B \<Longrightarrow> compose A h (compose A g f) = compose A (compose B h g) f" by(auto simp add:hom_def fun_eq_iff compose_def)

lemma fun_eqI:"f \<in> hom A Y \<Longrightarrow> g \<in> hom A Z \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g"  by (meson hom_memD1 maps_on_equalityI) 
lemma hom5:"f \<in> hom A B \<Longrightarrow> compose A (Id B) f = f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom6:"f \<in> hom A B  \<Longrightarrow> compose A f (Id A) = f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom7:"(Id A) \<in> hom A A" unfolding hom_def by(auto)
lemma hom8:"A \<subseteq> B \<Longrightarrow> (Id A) \<in> hom A B"  using hom_def by fastforce 
lemma hom9:"f \<in> hom A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B" unfolding hom_def by simp
lemma hom10:"f \<in> hom A B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" unfolding hom_def by simp
lemma hom11:"f \<in> hom A B \<Longrightarrow> g \<in> hom A C \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = g x" unfolding hom_def by(auto)


lemma is_right_invI1: "(\<And>y. y \<in> Y \<Longrightarrow> f (s y) = y) \<Longrightarrow> is_right_inv Y f s" unfolding is_right_inv_def compose_def using restrict_ext[of Y]   by auto
lemma is_right_invI2:  "(\<And>y. y \<in> Y \<Longrightarrow> y = f (s y)) \<Longrightarrow> is_right_inv Y f s" by (simp add: is_right_invI1)
lemma is_right_invE1:"is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> f (s y) = y"  by (metis compose_eq id1 is_right_inv_def)
lemma is_right_invE2:"is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> y = f (s y) " by (metis compose_eq id1 is_right_inv_def)
lemma ex_rinv_imp_surj: "\<exists>s. is_right_inv Y f s \<Longrightarrow> surj f (vimage f Y) Y" unfolding surj_def is_right_inv_def  by (metis image_ident image_restrict_eq image_subset_iff_subset_vimage subsetI subset_antisym subset_image_iff surj_compose) 
lemma is_rinv_imp_surj: "is_right_inv Y f s \<Longrightarrow> surj f (vimage f Y) Y" using ex_rinv_imp_surj by blast



lemma is_left_invI1[intro]:"(\<And>x. x \<in> X \<Longrightarrow> r (f x) = x) \<Longrightarrow> is_left_inv X f r" unfolding is_left_inv_def compose_def by auto
lemma is_left_invI2[intro]:"(\<And>x. x \<in> X \<Longrightarrow> x = r (f x)) \<Longrightarrow> is_left_inv X f r"   by (simp add: is_left_invI1)
lemma is_left_invE1:"is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> r (f x) = x"   by (metis compose_eq id1 is_left_inv_def) 
lemma is_left_invE2:"is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> x = r (f x)"   by (simp add: is_left_invE1) 
lemma is_left_inv_id:"is_left_inv X f r \<Longrightarrow> compose X r f = Id X"  using maps_on_equalityI[of "compose X r f" X "Id X"]  by (simp add: Id_def compose_eq is_left_invE1)
lemma linv_cancel:"is_left_inv X f r \<Longrightarrow> x1 \<in>X \<Longrightarrow>  x2 \<in> X \<Longrightarrow> f x1 = f x2 \<Longrightarrow> x1 =x2"  by (metis (no_types) is_left_invE1)
lemma ex_linv_implies_inj:"\<exists>s. is_left_inv X f r \<Longrightarrow> inj_on f X" by (simp add: inj_on_def linv_cancel)
lemma is_linv_implies_inj:"is_left_inv X f r \<Longrightarrow> inj_on f X"by (simp add: inj_on_def linv_cancel)
lemma inj_implies_ex_linv:"inj_on f X \<Longrightarrow> \<exists>r. is_left_inv X f r" unfolding is_left_inv_def  by (metis is_left_invI1 is_left_inv_id the_inv_into_f_f)


lemma rinv_simp:"y \<in> Y \<Longrightarrow> rinv f X Y y = (\<lambda>y. SOME x. x \<in> X \<and> f x = y) y" by (simp add: rinv_def)
lemma rinv_closed:"y \<in> f`X \<inter> Y \<Longrightarrow> rinv f X Y y \<in> X"  by(simp add:rinv_def,fast intro: someI2)
lemma rinv_undef:"y \<notin> Y \<Longrightarrow> rinv f X Y y = undefined"  by(simp add:rinv_def)
lemma rinv_map_to: "f ` A = B \<Longrightarrow> (rinv f A B) \<in> maps_to B A"  by (unfold rinv_def) (fast intro: someI2)
lemma id_surj:"(Id A)`A = A"  by force
lemma rinv_comp_to:"f ` A = B \<Longrightarrow> compose B f (rinv f A B) \<in> maps_to B B"  apply(rule maps_to_memI)
  using compose_eq[ of _ B f "rinv f A B"] rinv_closed[of _ f A B] by blast

lemma rinv_into_into:"f \<in> hom A B \<Longrightarrow> y \<in> f ` A \<Longrightarrow> rinv f A B y \<in> A"
  apply(auto simp add: rinv_def)
   apply(fast intro:someI2)
  by (simp add: hom9)

lemma rinv_identity[simp]:"rinv (Id A) A A= Id A"  by (force simp add: rinv_def)
lemma rinv_into_f_f [simp]: "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> (rinv f A (f`(A))) (f x) = x"   by (simp add: rinv_def inj_on_def) (blast intro: someI2)
lemma f_inv_into_f: "y \<in> f`A \<Longrightarrow> f (rinv f A (f`A) y) = y"  by (simp add: rinv_def) (fast intro: someI2)
lemma rinv_into_f_eq: "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> f x = y \<Longrightarrow> rinv f A (f`A) y = x"  by (erule subst) (fast intro: rinv_into_f_f)

lemma rinv_into_injective:
  assumes eq: "rinv f A (f`A) x = rinv f A (f`A) y"
    and x: "x \<in> f`A"
    and y: "y \<in> f`A"
  shows "x = y"
proof -
  from eq have "f (rinv f A (f`A) x) = f (rinv f A (f`A) y)"
    by simp
  with x y show ?thesis
    by (simp add: f_inv_into_f)
qed

lemma inj_on_rinv_into: "B \<subseteq> f`A \<Longrightarrow> inj_on (rinv f A (f`A)) B"  by (blast intro: inj_onI dest: rinv_into_injective injD)

lemma bij_betw_rinv_into: "bij_betw f A B \<Longrightarrow> bij_betw (rinv f A B) B A"  by (auto simp add: bij_betw_def inj_on_rinv_into image_iff)


lemma rinv_into_f:"f`A = B \<Longrightarrow> y \<in> f`A \<Longrightarrow> f (rinv f A B y) = y"  by (simp add: rinv_def) (fast intro: someI2)
lemma into_rinv_f:assumes A0:"f \<in> maps_to A B" and A1:"inj_on f A" and A2:"x \<in> A" shows "rinv f A B (f x) = x"  
proof(auto simp add:rinv_def)
  show "f x \<in> B \<Longrightarrow> (SOME xa::'a. xa \<in> A \<and> f xa = f x) = x"
  proof-
    assume A3:"f x \<in> B" then show "(SOME xa::'a. xa \<in> A \<and> f xa = f x) = x"
      using A1 A2 inj_onD by fastforce
  qed
  show "f x \<notin> B \<Longrightarrow> undefined = x"
    using A0 A2 by blast
qed
lemma into_rinv_f2:"bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow> rinv f A B (f x) = x"  by (simp add: bijD1 bij_betw_imp_inj_on into_rinv_f)

lemma rinv_inv: "f ` A = B \<Longrightarrow> compose B f (rinv f A B) = Id B"
  unfolding compose_def Id_def using restrict_ext[of B] rinv_into_f[of f A B]  by auto

lemma inv_rinv: "f \<in> maps_to A B \<Longrightarrow> inj_on f A \<Longrightarrow> compose A (rinv f A B) f= Id A" 
  unfolding compose_def Id_def using restrict_ext[of B] into_rinv_f[of f A B] by auto
lemma inv_rinv2: "bij_betw f A B \<Longrightarrow> compose A (rinv f A B) f= Id A"  by (simp add: bijD1 bij_betw_imp_inj_on inv_rinv) 

lemma rinv_restrict:"f`A = B \<Longrightarrow> restrict (rinv f A B) B = rinv f A B"  by (simp add: rinv_def)
lemma rinv_is_rinv:"f ` A = B \<Longrightarrow> is_right_inv B f (rinv f A B)"  by (simp add: is_right_inv_def rinv_inv)
lemma rinv_is_linv:"f \<in> maps_to A B \<Longrightarrow> inj_on f A \<Longrightarrow> is_left_inv A f (rinv f A B)"  by (simp add: is_left_inv_def inv_rinv)

lemma rinv_unique_on:
  assumes A0:"f`A = B" and A1:"\<And>y. y \<in> B \<Longrightarrow> f (s y) = y" and A2:"s`B = (rinv f A B)`B"
  shows "\<And>y. y \<in> B \<Longrightarrow> s y = rinv f A B y"
proof-
  fix y assume A3:"y \<in> B"
  then obtain t where b0:"t \<in> B" and b1:"s y = (rinv f A B) t"
    using A2 by auto
  have "y = f (s y)"
    using A1 A3  by simp 
  also have "... = f ((rinv f A B) t)"
    by (simp add: b1)
  also have "... = t"
    by (simp add: A0 b0 rinv_into_f)
  finally show "s y = (rinv f A B) y"
    using b1 by blast
qed

lemma surj_implies_ex_rinv:
  "surj f (vimage f Y) Y \<Longrightarrow> \<exists>s. is_right_inv Y f s"
proof-
  assume onto:"surj f (vimage f Y) Y"
  have "\<exists>s. \<forall>y \<in> Y. y = f (s y)"
  proof(rule bchoice[of Y "\<lambda>a b. a = f b"])
    show "\<forall>y::'b\<in>Y. \<exists>ya::'a. y = f ya"
    using onto unfolding surj_def by fastforce
  qed
  then show "\<exists>s. is_right_inv Y f s"
    by (metis is_right_invI1)
qed

lemma surj_implies_factors1:
  fixes X::"'a set" and Y::"'b set" and  g::"'a \<Rightarrow> 'b" and f::"'a \<Rightarrow> 'c"
  assumes surj:"g`X=Y" and compat:"\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> g x = g y \<Longrightarrow> f x = f y"
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = f (rinv g X Y (g x))"
proof-
let ?s="rinv g X Y"
  fix x assume A0:"x \<in> X"  then obtain B0:"g x \<in> Y" and B1:"?s (g x) \<in> X"   by (metis IntI rev_image_eqI rinv_closed surj)
  then obtain B2:"g (?s (g x)) = g x"  by (simp add: rinv_into_f surj)
  then obtain "f (?s (g x)) = f x" using compat A0 B1 by blast
  then show "f x = f (?s (g x))"
    by simp
qed

lemma surj_implies_factors2:
  fixes X::"'a set" and Y::"'b set" and g::"'a \<Rightarrow>'b" and f::"'a \<Rightarrow> 'c"
  assumes surj:"g`X=Y" and compat:"\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> g x = g y \<Longrightarrow> f x = f y"
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = compose Y f (rinv g X Y) (g x)"
proof-
  fix x assume x0:"x \<in> X"
  then obtain "f x = f (rinv g X Y (g x))" and "g x \<in> Y"
    using surj compat surj_implies_factors1[of g X Y f] by blast
  then show "f x = compose Y f (rinv g X Y) (g x)"
    by (simp add: compose_eq)
qed  

lemma left_inv_target: "is_left_inv X f r \<Longrightarrow> r`(f`X) = X "  unfolding is_left_inv_def  by (metis image_ident image_restrict_eq surj_compose)
lemma right_inv_target: "is_right_inv Y f s \<Longrightarrow> f`(s`Y) = Y"  unfolding is_right_inv_def by (metis image_ident image_restrict_eq surj_compose)
lemma rinv_l: "is_left_inv X f r \<Longrightarrow> is_right_inv X r f"  by (simp add: is_left_inv_id is_right_inv_def)
lemma linv_r:"is_right_inv (Y::'b set) f s \<Longrightarrow> is_left_inv Y s f"  by (simp add: is_left_inv_def is_right_inv_def) 
lemma rinv_surj:"is_left_inv X f r \<Longrightarrow> surj r (f`X) X" using ex_rinv_imp_surj rinv_l  by (simp add: surj_def left_inv_target) 
lemma linv_inj: "is_right_inv (Y::'b set) f s \<Longrightarrow> inj_on s Y"  using is_linv_implies_inj linv_r by blast

lemma bij_betw_rinv: "bij_betw f A B \<Longrightarrow> y \<in> B \<Longrightarrow> f (rinv f A B y) = y"  by (simp add: bij_betw_imp_surj_on rinv_into_f)

lemma bij_betw_linv: "bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow> (rinv f A B) (f x)= x" by(simp add:  bij_betw_def,force)

lemma bij_betw_hom_rev:"bij_betw f A B \<Longrightarrow> rinv f A B \<in> hom B A"  by(rule hom_memI2,simp add: rinv_def,simp add:bijD1 bij_betw_rinv_into)

locale set_morphism=
  fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"
  assumes dom[intro]:"x \<notin> A \<longrightarrow> f x = undefined" and  
          cod[intro,simp]:"x \<in> A \<Longrightarrow> f x \<in> B"
begin
lemma mem_maps_to:"f \<in> maps_to A B" by (simp add: maps_to_memI)
lemma mem_maps_on:"f \<in> maps_on A" by (simp add: dom maps_on_memI) 
lemma mem_hom:"f \<in> hom A B" by (simp add: hom_memI2 mem_maps_on mem_maps_to)
end

lemma set_morphism1I:"f \<in> hom A B \<Longrightarrow> set_morphism f A B" unfolding hom_def by(auto intro!: set_morphism.intro)

locale sur_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes sur[intro]:"f `A = B"
locale inj_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes inj[intro, simp]:"inj_on f A"
locale iso_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes iso[intro, simp]:"bij_betw f A B"
locale set_epimorphism = set_morphism f A B + sur_locale f A B for f and A and B
begin
definition right_inverse ("s") where "right_inverse \<equiv> rinv f A B"
lemma right_inverse_comp1:"compose B f s = Id B"  by (simp add: right_inverse_def rinv_inv sur)
lemma right_inverse_comp2:"y \<in> B \<Longrightarrow> compose B f s y = y" by (simp add: right_inverse_comp1)
lemma right_inverse_comp3:"y \<in> B \<Longrightarrow> f (s y) = y"  by (simp add: right_inverse_def rinv_into_f sur)
lemma right_inverse_inv:"is_right_inv B f s"  by (simp add: right_inverse_def rinv_is_rinv sur)
end

lemma set_epiI1:"f \<in> hom A B \<Longrightarrow> f`A=B \<Longrightarrow> set_epimorphism f A B"  by (simp add: set_epimorphism_def set_morphism1I sur_locale.intro) 


locale set_monomorphism=set_morphism f A B+ inj_locale f A B for f and A and B
begin
definition left_inverse ("r") where "left_inverse \<equiv> rinv f A B"
lemma left_inverse_comp1:"compose A r f = Id A" by (simp add: inv_rinv left_inverse_def mem_maps_to) 
lemma left_inverse_comp2:"x \<in> A \<Longrightarrow> compose A r f x = x"  by (simp add: left_inverse_comp1) 
lemma left_inverse_comp3:"x \<in> A \<Longrightarrow> r (f  x) = x"  by (simp add: into_rinv_f left_inverse_def mem_maps_to)
lemma left_inverse_inv:"is_left_inv A f r" by (simp add: is_left_inv_def left_inverse_comp1) 
end


locale set_isomorphism =set_morphism + iso_locale
begin
sublocale set_epimorphism by unfold_locales (simp add:bij_betw_imp_surj_on)
sublocale set_monomorphism using bij_betw_def by unfold_locales fast
sublocale inverse:set_morphism "rinv f A B" B A by(unfold_locales,simp add: rinv_undef,simp add: mem_hom rinv_into_into sur)
sublocale inverse:iso_locale "rinv f A B" B A by(unfold_locales;simp add: bij_betw_rinv_into)
end




context set_morphism
begin
theorem bij_betw_iff_has_inverse: "bij_betw f A B \<longleftrightarrow> (\<exists>g \<in> hom B A. compose A g f = Id A \<and> compose B f g = Id B)"  (is "_ \<longleftrightarrow> (\<exists>g \<in> hom B A. ?INV g)")
proof
  let ?inv = "rinv f A B"
  assume A0:"bij_betw f A B" then obtain "?INV ?inv" and "?inv \<in> hom B A"   by (simp add: bij_betw_hom_rev bij_betw_imp_surj_on inv_rinv2 rinv_inv)
  then show "\<exists>g \<in> hom B A. ?INV g" by auto
next
  assume "\<exists>g \<in> hom B A. ?INV g"
  then obtain g where "f \<in> maps_to A B" "g \<in> maps_to B A" and "\<And>x. x\<in>A\<Longrightarrow>g(f x) = x" and "\<And>y. y\<in>B \<Longrightarrow> f(g y) = y" 
    by (metis mem_maps_to compose_eq hom_memD2 id1)
  then show "bij_betw f A B" by (rule bijI) 
qed
end


locale equivalence_relation=
  fixes X :: "'a set" and R :: "('a \<times> 'a) set"
  assumes sub[intro, simp]:"R \<subseteq> X \<times> X" and
          ref[intro, simp]: "a \<in> X \<Longrightarrow> (a, a) \<in> R" and 
          sym[sym]: "(a, b) \<in> R \<Longrightarrow> (b, a) \<in> R" and
          trn[trans]: "\<lbrakk>(a, b) \<in> R; (b, c) \<in> R \<rbrakk> \<Longrightarrow> (a, c) \<in> R"
begin
definition "p \<equiv> (\<lambda>x \<in> X. {y \<in> X. (x, y) \<in> R})"
definition "pinv \<equiv> rinv p X (X/R)"
lemma l_closed[intro]:"(a, b) \<in> R \<Longrightarrow> a \<in> X" using sub by blast
lemma r_closed[intro]:"(a, b) \<in> R \<Longrightarrow> b \<in> X" using sub by blast
lemma p_def2:"p = (\<lambda>x \<in> X. R``{x})" using p_def by fastforce
lemma p_closed1[dest]:"x \<in> X \<Longrightarrow> y \<in> p x \<Longrightarrow> y \<in> X" unfolding p_def by auto
lemma p_closed2[intro, simp]:"a \<in> X \<Longrightarrow> p a \<subseteq> X" unfolding p_def by auto
lemma p_undefined[intro, simp]: "a \<notin> X \<Longrightarrow> p a = undefined" unfolding p_def by simp
lemma p_I1[intro, simp]:"(a, b) \<in> R \<Longrightarrow> b \<in> p a"  unfolding p_def by (simp add: l_closed r_closed)
lemma p_revI [intro, simp]: "(a, b) \<in> R \<Longrightarrow> a \<in> p a"  by (blast intro: sym)
lemma p_D1[dest]:"\<lbrakk>a \<in> X; b \<in> p a\<rbrakk> \<Longrightarrow> (a, b) \<in> R"  unfolding p_def by simp
lemma p_self [intro, simp]:"a \<in> X \<Longrightarrow> a \<in> p a"  unfolding p_def by simp
lemma p_un [simp]:"(\<Union>a\<in>X. p a) = X" by blast
lemma p_subset1:"(a, b) \<in> R \<Longrightarrow> p a \<subseteq> p b" by (meson l_closed local.sym p_D1 p_I1 subsetI trn)
lemma p_eq1:"(a, b) \<in> R \<Longrightarrow> p a = p b"  by (auto intro!: p_subset1 intro: sym)
lemma p_equivalence:"\<lbrakk>a \<in> X;b \<in> X\<rbrakk> \<Longrightarrow> p a = p b \<longleftrightarrow> (a, b) \<in> R"  by (metis p_D1 p_eq1 p_self)
lemma p_meet_eq1:"\<lbrakk>a \<in> X; b \<in> X; p a \<inter> p b \<noteq> {}\<rbrakk> \<Longrightarrow> p a = p b" by (metis disjoint_iff p_D1 p_eq1)
lemma p_in_quotient1[intro, simp]: "a \<in> X \<Longrightarrow> p a \<in> (X/R)"  unfolding quotient_def by blast
lemma elem_ex1:"x \<in> X \<Longrightarrow> \<exists>t. x \<in> t \<and> t \<in> (X/R)"  using p_self by blast
lemma elem_ex2:"p`X = (X/R)" by (simp add: quotient_def UNION_singleton_eq_range p_def2)
lemma elem_ex3:"t \<in> (X/R) \<Longrightarrow> t \<in> p`X"  by (simp add: elem_ex2)
lemma elem_ex4:"t \<in> (X/R) \<Longrightarrow> (\<exists>x \<in> X. p x = t)" using elem_ex3 by blast 
lemma elem_un1:"t \<in> (X/R) \<Longrightarrow> s \<in> (X/R) \<Longrightarrow> t \<noteq> s \<Longrightarrow>  t \<inter> s = {}"
proof-
  assume t0:"t \<in> (X/R)" and t1:"s \<in> (X/R)"
  then obtain x y where x0:"x \<in> X" and x1:"p x = t" and y0:"y \<in> X" and y1:"p y =s" 
    using elem_ex4[of t] elem_ex4[of s] by blast
  assume st0:"t \<noteq> s"
  then show "t \<inter> s = {}"
  proof(rule contrapos_np)
    assume n:"t \<inter> s \<noteq> {}"
    then show "t =s"
      using p_meet_eq1 st0 x0 x1 y0 y1 by blast
  qed
qed
lemma elem_un2:"t \<in> (X/R) \<Longrightarrow> s \<in> (X/R) \<Longrightarrow> a \<in> t \<Longrightarrow> a \<in> s \<Longrightarrow> t = s"  by (metis disjoint_iff elem_un1)
lemma p_mem_closed[intro]:"x \<in> t \<Longrightarrow> t \<in> (X/R) \<Longrightarrow> x \<in> X" using elem_ex2 by auto
lemma elem_ex5:"t \<in> (X/R) \<Longrightarrow> \<exists>x \<in> X. x \<in> t"  using elem_ex4 by blast
lemma proj_hom:"set_morphism p X (X/R)" by (simp add: set_morphism.intro) 
lemma proj_epi:"set_epimorphism p X (X/R)"  by (simp add: elem_ex2 proj_hom set_epimorphism.intro sur_locale.intro)  
lemma rep_ex[dest]:"t \<in> X/R \<Longrightarrow> \<exists>x \<in> X. x \<in> t \<and> p x = t"  using elem_ex4 by blast
lemma projE:"t \<in> X/R \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> Q (p x)) \<Longrightarrow> Q t"  by blast

lemma sec_rinv:"is_right_inv (X/R) p pinv"  by (simp add: elem_ex2 pinv_def rinv_is_rinv)
lemma sec_hom:"pinv \<in> hom (X/R) X"  by (simp add: elem_ex2 hom_memI1 pinv_def rinv_into_into rinv_undef)
lemma sec_closed[intro]:"t \<in> X/R \<Longrightarrow> pinv t \<in> X"  by (meson hom9 sec_hom)
lemma sec_undef:"t \<notin> X/R \<Longrightarrow> pinv t = undefined"  by (simp add: pinv_def rinv_undef)

lemma compat_factors1:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" 
  shows "\<And>x. x \<in> X \<Longrightarrow> f x =  compose (X/R) f (rinv p X (X/R)) (p x)"
  by(rule surj_implies_factors2,simp add:elem_ex2,fast elim:compat)

lemma compat_factors2:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" and set_hom:"f \<in> hom X Y"
  defines "h \<equiv> compose (X/R) f (rinv p X (X/R))"
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = compose X h p x" and "f = compose X h p"
proof-
  show P0:"\<And>x. x \<in> X \<Longrightarrow> f x = compose X h p x"
  proof-
    fix x assume a1: "x \<in> X" 
  then have "f x = compose (X / R) f (rinv p X (X / R)) (p x)"
    unfolding h_def using compat compat_factors1 by blast
  also have "... = compose X h p x"
    by (simp add: a1 compose_eq h_def)
  finally show " f x = compose X h p x"
    by simp
qed
   show "f = compose X h p"
proof(rule maps_on_equalityI)
  show "f \<in> maps_on X"
    using hom_memD1 set_hom by blast
  show "compose X h p \<in> maps_on X"
    by simp
  show "\<And>x. x \<in> X \<Longrightarrow> f x = compose X h p x"
    by (simp add:P0)
  qed
qed
lemma psecE1:"t \<in> X/R \<Longrightarrow> p (pinv t) = t"  by (meson is_right_invE1 sec_rinv) 



end

locale kernel_pair_notation=fixes X::"'a set"
begin
definition kernel_pair_object ("Ker'(_')") where "kernel_pair_object f \<equiv> {(x, y). x \<in> X \<and> y \<in> X \<and> f x = f y} "
end

locale kernel_pair=set_morphism f X Y for f and X and Y
begin
sublocale kernel_pair_notation  X.
sublocale equivalence_relation where X=X and R="Ker(f)" unfolding kernel_pair_object_def by(unfold_locales;auto)
definition "h \<equiv> compose (X/Ker(f)) f pinv"
(*definition "h \<equiv> (\<lambda>t \<in> X/Ker(f). THE y. \<exists>x \<in> t. y = f x)"*)
lemma h_eq:"\<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> p x = p y \<longleftrightarrow> f x = f y"  unfolding p_equivalence unfolding kernel_pair_object_def by simp
lemma h_simp[simp]:"x \<in> X \<Longrightarrow> h (p x) = f x" unfolding h_def pinv_def using h_eq compat_factors1[of f]  by presburger

interpretation quotient_map:set_morphism h "X/Ker(f)" Y  using h_def hom2 mem_hom sec_hom set_morphism1I by fastforce
sublocale quotient_map: set_monomorphism h "X/Ker(f)" Y proof  show "inj_on h (X / Ker(f))" unfolding inj_on_def  by (metis h_eq h_simp rep_ex) qed
lemma factorization1:"x\<in>X \<Longrightarrow> compose X h p a = f a" by (simp add: compose_def dom)
lemma factorization2[simp]:"compose X h p = f"  by (rule ext) (simp add: compose_def dom)
lemma factorization3:
  assumes A0:"g \<in> hom (X/Ker(f)) Y" and A1:"compose X g p = f"
  shows "g = h" 
proof
  fix t show "g t = h t"
  proof (cases "t \<in> X/Ker(f)")
    case True
    then obtain x where [simp]: "t = p x" "x \<in> X" 
      by fast
    then have "g (p x) = f x"
      by (metis compose_eq A1)
    also have "\<dots> = h (p x)"
      by simp
    finally show ?thesis
      by simp
  next
    case False  then show ?thesis using A0 hom10 quotient_map.dom by fastforce
  qed
qed


end



definition magma_stable :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where  "magma_stable X f A \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A. f x y \<in> A) \<and> (A \<subseteq> X)"

locale magma=
  fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) 
  assumes closed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> X" 
begin
definition stable where  "stable A \<equiv> magma_stable X f A"

definition commutes where  "commutes A B \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B. a \<cdot> b = b \<cdot> a)"
lemma commutesI:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a) \<Longrightarrow> commutes A B"  using commutes_def by auto
definition centralizer where "centralizer E \<equiv> {x \<in> X. \<forall>y \<in> E. commutes {x} {y}}"
definition center where "center = centralizer X"
lemma centralizer_memI1:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> E \<Longrightarrow> commutes {x} {y}) \<Longrightarrow> x \<in> centralizer E" by (simp add: centralizer_def)
lemma centralizer_memI2:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> E \<Longrightarrow> x \<cdot> y = y \<cdot> x) \<Longrightarrow> x \<in> centralizer E"  by (simp add: centralizer_memI1 commutes_def) 
lemma centralizer_memI3:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> E \<Longrightarrow> y \<cdot> x = x \<cdot> y) \<Longrightarrow> x \<in> centralizer E"  by (simp add: centralizer_memI1 commutes_def) 
lemma centralizer_memD:"x \<in> centralizer E \<Longrightarrow> (\<And>a. a \<in> E \<Longrightarrow>  a \<cdot> x = x \<cdot> a)"  by (simp add: centralizer_def commutes_def)
lemma center_memI1:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow>  commutes {x} {y}) \<Longrightarrow> x \<in> center"  using center_def centralizer_memI1 by auto
lemma center_memI2:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow>  x \<cdot> y = y \<cdot> x) \<Longrightarrow> x \<in> center"  using center_def centralizer_memI2 by auto  
lemma center_memI3:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow>  y \<cdot> x = x \<cdot> y) \<Longrightarrow> x \<in> center"  by (simp add: center_memI2) 
lemma center_memD:"x \<in> center \<Longrightarrow> (\<And>a. a \<in> X \<Longrightarrow>  a \<cdot> x = x \<cdot> a)"  using center_def centralizer_memD by blast  

abbreviation bicentralizer where "bicentralizer \<equiv> centralizer \<circ> centralizer"
definition l_identity where "l_identity e \<equiv> (\<forall>x \<in>X. e \<cdot> x = x)"
definition r_identity where "r_identity e \<equiv> (\<forall>x \<in>X. x \<cdot> e = x)"

definition l_cancellable where "l_cancellable a \<equiv> a \<in> X \<and> (\<forall>x \<in> X. \<forall>y \<in> X.  a \<cdot> x = a \<cdot> y \<longrightarrow> x = y)"
definition r_cancellable where "r_cancellable a \<equiv> a \<in> X \<and> (\<forall>x \<in> X. \<forall>y \<in> X.  x \<cdot> a = y \<cdot> a \<longrightarrow> x = y)"
definition cancellable where "cancellable a \<equiv> a \<in> X \<and> (\<forall>x \<in> X. \<forall>y \<in> X.  x \<cdot> a = y \<cdot> a \<longrightarrow> x = y) \<and> (\<forall>x \<in> X. \<forall>y \<in> X.  a \<cdot> x = a \<cdot> y \<longrightarrow> x = y)"

definition id_elem where "id_elem e \<equiv>(\<forall>x \<in>X. e \<cdot> x = x \<and> x \<cdot> e = x)"
definition l_trans where "l_trans \<equiv> (\<lambda>a \<in> X. \<lambda>x \<in> X. a \<cdot> x)"
definition r_trans where "r_trans \<equiv> (\<lambda>a \<in> X. \<lambda>x \<in> X. x \<cdot> a)"

definition r_coset::"'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where "r_coset H a = (\<Union>h\<in>H. {h \<cdot> a})"
definition l_coset::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where "l_coset a H = (\<Union>h\<in>H. {a \<cdot> h})"
definition r_cosets::"'a set \<Rightarrow> ('a set) set" where "r_cosets H = (\<Union>a\<in>X. {r_coset H a})"
definition l_cosets::"'a set \<Rightarrow> ('a set) set" where "l_cosets H = (\<Union>a\<in>X. {l_coset a H})"
definition set_prod::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  where "set_prod H K = (\<Union>h\<in>H. \<Union>k\<in>K. {h \<cdot> k})"


lemma l_cancellableI1:"a \<in> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X;a\<cdot>x=a\<cdot>y\<rbrakk> \<Longrightarrow> x = y ) \<Longrightarrow> l_cancellable a"  by (simp add: l_cancellable_def)
lemma r_cancellableI1:"a \<in> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X;x\<cdot>a=y\<cdot>a\<rbrakk> \<Longrightarrow> x = y ) \<Longrightarrow> r_cancellable a"  by (simp add: r_cancellable_def)
lemma cancellableI1:"a \<in> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X;a\<cdot>x=a\<cdot>y\<rbrakk> \<Longrightarrow> x = y )  \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X;x\<cdot>a=y\<cdot>a\<rbrakk> \<Longrightarrow> x = y ) \<Longrightarrow> cancellable a"  by (simp add: cancellable_def)

lemma l_cancellableI2:"a \<in> X \<Longrightarrow> inj_on (l_trans a) X \<Longrightarrow> l_cancellable a"  by (simp add: inj_on_def l_cancellableI1 l_trans_def) 
lemma r_cancellableI2:"a \<in> X \<Longrightarrow> inj_on (r_trans a) X \<Longrightarrow> r_cancellable a"  by (simp add: inj_on_def r_cancellableI1 r_trans_def) 
lemma cancellableI2:"a \<in> X \<Longrightarrow> inj_on (l_trans a) X \<Longrightarrow> inj_on (r_trans a) X \<Longrightarrow> cancellable a"  by (simp add: inj_on_def cancellableI1 l_trans_def r_trans_def) 
lemma cancellableI3:" l_cancellable a \<Longrightarrow> r_cancellable a \<Longrightarrow> cancellable a" by (simp add: cancellableI1 l_cancellable_def r_cancellable_def)  


lemma l_cancellableD1:"l_cancellable a \<Longrightarrow> inj_on (l_trans a) X"  by (simp add: inj_on_def l_cancellable_def l_trans_def) 
lemma r_cancellableD1:"r_cancellable a \<Longrightarrow> inj_on (r_trans a) X"  by (simp add: inj_on_def r_cancellable_def r_trans_def) 
lemma cancellableD1:"cancellable a \<Longrightarrow> inj_on (l_trans a) X \<and>  inj_on (r_trans a) X"  by (simp add: cancellable_def l_cancellableD1 l_cancellableI1 r_cancellableD1 r_cancellableI1) 

lemma l_cancellable_iff_l_trans_inj:"a \<in> X \<Longrightarrow> l_cancellable a \<longleftrightarrow> inj_on (l_trans a) X" using l_cancellableD1 l_cancellableI2 by blast
lemma r_cancellable_iff_r_trans_inj:"a \<in> X \<Longrightarrow> r_cancellable a \<longleftrightarrow> inj_on (r_trans a) X" using r_cancellableD1 r_cancellableI2 by blast
lemma cancellable_iff_trans_inj:"a \<in> X \<Longrightarrow> cancellable a \<longleftrightarrow>inj_on (l_trans a) X \<and> inj_on (r_trans a) X" using cancellableD1 cancellableI2 by blast 

lemma stableI:  "A \<subseteq> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> A) \<Longrightarrow> stable A" by (simp add: local.stable_def magma_stable_def)
lemma stableE1: "stable A \<Longrightarrow> A \<subseteq> X" by (simp add: local.stable_def magma_stable_def)
lemma stableE2:  "stable A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x\<cdot>y \<in> A" by (simp add: local.stable_def magma_stable_def)
lemma centralizer_sub:"centralizer A \<subseteq> X" unfolding centralizer_def by blast
lemma centralizer_antitone:"A \<subseteq> B \<Longrightarrow> centralizer B \<subseteq> centralizer A" unfolding centralizer_def by blast
lemma centralizer_comp_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> centralizer (centralizer A)" unfolding centralizer_def commutes_def by force
lemma bicentralizer_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq>bicentralizer A" unfolding centralizer_def commutes_def by force
lemma bicentralizer_isotone:"A \<subseteq> B \<Longrightarrow> bicentralizer A \<subseteq>bicentralizer B" unfolding centralizer_def commutes_def by force
lemma bicentralizer_idempotent:"bicentralizer (bicentralizer A) = bicentralizer A" unfolding centralizer_def commutes_def by force

lemma commutes_sub_centralizer1:"B \<subseteq> X \<Longrightarrow> commutes A B \<Longrightarrow> B \<subseteq> centralizer A" unfolding centralizer_def commutes_def by fastforce
lemma commutes_sub_centralizer2:"B \<subseteq> X \<Longrightarrow> commutes B A \<Longrightarrow> B \<subseteq> centralizer A" unfolding centralizer_def commutes_def by fastforce
lemma centralizer_commutes1:"commutes A (centralizer A)" unfolding centralizer_def commutes_def by fastforce
lemma centralizer_commutes2:"commutes (centralizer A) A" unfolding centralizer_def commutes_def by fastforce
lemma bicentralizer_commutes1:"commutes (centralizer A) (bicentralizer A)" unfolding centralizer_def commutes_def by(auto)
lemma bicentralizer_commutes2:"commutes (bicentralizer A) (centralizer A)" unfolding centralizer_def commutes_def by(auto)


lemma bicentralizer_mem_iff:"A \<subseteq> X \<Longrightarrow>y \<in> X \<Longrightarrow> y \<in> bicentralizer A \<longleftrightarrow> (\<forall>x \<in> X. (\<forall>a \<in> A. x \<cdot> a = a \<cdot> x) \<longrightarrow> x \<cdot> y = y \<cdot> x)"  unfolding centralizer_def commutes_def by(auto)

lemma id_elem_unique:"\<And>e1 e2. id_elem e1 \<Longrightarrow> id_elem e2 \<Longrightarrow>e1 \<in> X \<Longrightarrow> e2 \<in> X \<Longrightarrow>  e1 = e2" unfolding id_elem_def by auto
lemma id_commutes:"id_elem e \<Longrightarrow> e \<in> X \<Longrightarrow> commutes {e} X" unfolding id_elem_def commutes_def by(auto)
lemma l_trans_app:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> l_trans x y = r_trans y x" unfolding l_trans_def r_trans_def by(auto)
lemma l_trans_hom:"\<And>a. a \<in> X \<Longrightarrow> l_trans a \<in> hom X X" by (simp add: closed hom_memI1 l_trans_def)
lemma r_trans_hom:"\<And>a. a \<in> X \<Longrightarrow> r_trans a \<in> hom X X" by (simp add: closed hom_memI1 r_trans_def)
lemma id_elem_linj:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> inj_on (l_trans e) X " unfolding inj_on_def l_trans_def id_elem_def by(auto)
lemma id_elem_rinj:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> inj_on (r_trans e) X " unfolding inj_on_def r_trans_def id_elem_def by(auto)

inductive_set magma_generated::"'a set \<Rightarrow> 'a set" for A where
 iso:"a \<in> A \<Longrightarrow> a \<in> magma_generated A"
 |opc:"a \<in> magma_generated A \<Longrightarrow> b \<in> magma_generated A \<Longrightarrow> a\<cdot>b \<in> magma_generated A"

lemma generate_into: "a \<in> magma_generated (X \<inter> A) \<Longrightarrow> a \<in> X"  apply (induction rule: magma_generated.induct)  apply simp by (simp add: closed)

definition cl :: "'a set \<Rightarrow> 'a set"  where "cl S = magma_generated (X \<inter> S)"
lemma cl_magma_sub:"cl H \<subseteq> X" using cl_def generate_into by auto

lemma cl_magma_iso:
  assumes A0:"A \<subseteq> B"  shows "cl A \<subseteq> cl B"
proof
  fix x assume "x \<in> cl A"
  then show "x \<in> cl B" unfolding cl_def
   apply(induction rule: magma_generated.induct)
    using assms magma_generated.iso apply auto[1]
    using magma_generated.opc by auto
qed

lemma cl_magma_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> cl A" 
  unfolding cl_def using magma_generated.simps by blast 

lemma cl_magma_stable_ub:"A \<subseteq> B \<Longrightarrow> stable B \<Longrightarrow> cl A \<subseteq> B" 
  by (metis Int_absorb1 cl_def magma.cl_def magma.cl_magma_sub magma_def stableE1 stableE2 subset_trans) 

lemma cl_magma_idempotent:
  assumes A0:"A \<subseteq> X" 
  shows "cl A = cl (cl A)"
  apply(rule subset_antisym)
  apply (simp add: cl_magma_extensive cl_magma_sub)
  using cl_def cl_magma_stable_ub cl_magma_sub magma_generated.opc stableI by auto

lemma cl_magma_moore0:
  assumes A0:"A \<subseteq> X" 
  shows "cl A = \<Inter>{C. stable C \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    by (simp add: le_Inf_iff magma.cl_magma_stable_ub magma_axioms)
next
  show "?RHS \<subseteq> ?LHS"
    using assms cl_def cl_magma_extensive cl_magma_sub magma_generated.opc stableI by force
qed

lemma generated_stable:"stable (cl A)"  
  using cl_def cl_magma_sub magma_generated.opc stableI by presburger 

lemma r_coset_singleton_prod:"r_coset H a = set_prod H {a}" unfolding r_coset_def set_prod_def by blast
lemma l_coset_singleton_prod:"l_coset a H = set_prod {a} H" unfolding l_coset_def set_prod_def by blast

lemma set_prod_closed:"A \<subseteq> X \<Longrightarrow> B \<subseteq> X \<Longrightarrow> set_prod A B \<subseteq> X" by(auto simp add:closed set_prod_def subsetD)
lemma l_coset_memI[intro]:"h \<in> H \<Longrightarrow> x \<cdot> h \<in> l_coset x H" unfolding l_coset_def  by blast
lemma r_coset_memI[intro]:"h \<in> H \<Longrightarrow> h \<cdot> x \<in> r_coset H x" unfolding r_coset_def by blast
lemma l_coset_memE[elim]:"a \<in> l_coset x H \<Longrightarrow> (\<And>h. \<lbrakk>h\<in>H;a=x\<cdot>h\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" unfolding l_coset_def  by blast
lemma r_coset_memE[elim]:"a \<in> r_coset H x \<Longrightarrow> (\<And>h. \<lbrakk>h\<in>H;a=h\<cdot>x\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P" unfolding r_coset_def  by blast

lemma r_coset_sub:"A \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> r_coset A x \<subseteq> X" using closed by blast
lemma l_coset_sub:"A \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> l_coset x A \<subseteq> X" using closed by blast

end

interpretation ex1a:magma "Pow X" "(\<lambda>A. \<lambda>B. A \<union> B)" apply(unfold_locales) by simp
interpretation ex1b:magma "Pow X" "(\<lambda>A. \<lambda>B. A \<inter> B)" apply(unfold_locales) by blast
interpretation ex2a:magma "UNIV::nat set" "(\<lambda>x. \<lambda>y. x+y)"  by (simp add: magma.intro)
interpretation ex2b:magma "UNIV::nat set" "(\<lambda>x. \<lambda>y. x*y)"  by (simp add: magma.intro)

section \<open>Submagma Locale\<close>
locale submagma=magma X "(\<cdot>)" for A and X and magma_law (infixl "\<cdot>" 70)+
  assumes submem:"A \<subseteq> X" and 
          subfun:"\<lbrakk>x \<in>A; y \<in> A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> A" 
begin
lemma sub[intro,simp]:"x \<in> A \<Longrightarrow> x \<in> X" using submem by auto
sublocale sub:magma A "(\<cdot>)" by (simp add: magma.intro subfun) 

lemma cl_submgama: "submagma (cl H) X (\<cdot>)" 
  apply(rule submagma.intro)
  apply(rule magma.intro)
  apply (simp add: closed)
  apply(auto simp add:submagma_axioms_def)
  apply (simp add: cl_def generate_into)
  by (simp add: cl_def sub.magma_generated.opc)

lemma cl_magma_ub:
  assumes A0:"A \<subseteq> B" and A1:"submagma B X (\<cdot>)"   shows "cl A \<subseteq> B"
proof
  fix x assume "x \<in> cl A"
  then show "x \<in> B"
    unfolding cl_def
    apply(induction rule: magma_generated.induct)
    using A0 apply blast
    by (meson A1 submagma.subfun)
qed

lemma cl_magma_moore1:
  assumes A0:"A \<subseteq> X"   shows "cl A = \<Inter>{C. submagma C X (\<cdot>) \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    using cl_magma_ub by auto
next
  show "?RHS \<subseteq> ?LHS"
    by (simp add: Inter_lower assms cl_magma_extensive cl_submgama)
qed
end




lemma submamga_trans: 
  assumes "submagma A B f" and 
          "submagma B C f" 
  shows   "submagma A C f" 
proof-
  interpret A: submagma A B f
    by fact 
  interpret C: submagma B C f 
    by fact 
  show ?thesis 
    by (simp add: A.subfun C.magma_axioms submagma.intro submagma_axioms_def subset_iff) 
qed

lemma submagmaI:"magma X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (f x y) \<in> A) \<Longrightarrow> submagma A X f" 
  by (simp add: submagma.intro submagma_axioms.intro subsetD)


section \<open>Unital Magma Locale\<close>
locale unital_magma=magma+fixes e 
  assumes idin:"e \<in> X" and
          lid:"x \<in> X \<Longrightarrow> e \<cdot> x = x" and 
          rid:"x \<in> X \<Longrightarrow> x \<cdot> e = x"
begin
lemma islid:"l_identity e" by (simp add: l_identity_def lid)
lemma isrid:"r_identity e" by (simp add: r_identity_def rid)
lemma isid:"id_elem e"  by (simp add: id_elem_def lid rid)
sublocale magma:magma X "(\<cdot>)" using magma_axioms by blast 
end

section \<open>Magma Homomorphism Locale\<close>


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

sublocale kernel_pair f X Y  by (simp add: kernel_pair_def set_morphism_axioms)
notation kernel_pair_object ("R'(_')")
sublocale im:submagma "f`X" Y "(\<star>)" by (simp add: dom.closed dom.magma_axioms submagma1 submagmaI)
end

section \<open>Magma Epimorphism Locale\<close>

locale magma_epimorphism=set_epimorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
end

section \<open>Magma Monomorphism Locale\<close>

locale magma_monomorphism=set_monomorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
end


section \<open>Magma Isomorphism Locale\<close>

locale magma_isomorphism=set_isomorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
sublocale magma_epimorphism by(unfold_locales,simp add: cmp)
sublocale magma_monomorphism by(unfold_locales,simp add: cmp)
end

     
section \<open>Quotient Magma Locale\<close>

definition l_cong::"'a set\<Rightarrow>('a\<Rightarrow>'b\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where "l_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f a x, f a y) \<in> R)"
definition r_cong::"'a set\<Rightarrow>('b\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where "r_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f x a, f y a) \<in> R)"
definition cong::"'a set\<Rightarrow>('a\<Rightarrow>'a\<Rightarrow>'a)\<Rightarrow>('a\<times>'a) set \<Rightarrow> bool" where "cong X f R \<equiv> (\<forall>(x1, x2) \<in> R. \<forall>(y1, y2) \<in> R.  (f x1 y1, f x2 y2) \<in> R)"

lemma l_congI1:"(\<And>a x y. a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R) \<Longrightarrow> l_cong X f R" using l_cong_def by fastforce
lemma r_congI1:"(\<And>a x y. a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R) \<Longrightarrow> r_cong X f R" using r_cong_def by fastforce
lemma congI1:"(\<And>x1 x2 y1 y2. (x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (f x1 y1 , f x2 y2) \<in> R) \<Longrightarrow> cong X f R" using cong_def by fastforce
lemma congD1:"cong X f R \<Longrightarrow> (x1,x2)\<in>R \<Longrightarrow> (y1,y2) \<in> R \<Longrightarrow> (f x1 y1, f x2 y2) \<in> R"  using cong_def by fastforce
lemma l_congD1:"l_cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R" using l_cong_def by fastforce
lemma r_congD1:"r_cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R" using r_cong_def by fastforce
lemma congDR:"refl_on X R \<Longrightarrow> cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R"  proof-  assume A0:"refl_on X R" "cong X f R" "a \<in> X" "(x,y)\<in>R"  then have B0:"(a,a)\<in>R"   by (simp add: refl_onD)  then show "(f x a, f y a) \<in> R"  using A0 cong_def by fastforce qed
lemma congDL:"refl_on X R \<Longrightarrow> cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R"  proof-  assume A0:"refl_on X R" "cong X f R" "a \<in> X" "(x,y)\<in>R"  then have B0:"(a,a)\<in>R"   by (simp add: refl_onD)  then show "(f a x, f a y) \<in> R"  using A0 cong_def by fastforce qed
lemma l_congI2:
  assumes A0:"equivalence_relation X R" and A1:"cong X f R" 
  shows "l_cong X f R" 
proof(rule l_congI1)
  fix a x y assume a:"a \<in> X" and xy:"(x, y) \<in> R"
  then have "(a, a) \<in> R"
    by (meson assms(1) equivalence_relation.ref)
  then show "(f a x, f a y) \<in> R"
    using A1 xy congD1[of X f R a a x y] by blast
qed
lemma r_congI2:
  assumes A0:"equivalence_relation X R" and A1:"cong X f R" 
  shows "r_cong X f R" 
proof(rule r_congI1)
  fix a x y assume a:"a \<in> X" and xy:"(x, y) \<in> R"
  then have "(a, a) \<in> R"
    by (meson assms(1) equivalence_relation.ref)
  then show "(f x a, f y a) \<in> R"
    using A1 xy congD1[of X f R x y a a] by blast
qed

lemma congI2:"equivalence_relation X R \<Longrightarrow> l_cong X f R \<Longrightarrow> r_cong X f R \<Longrightarrow> cong X f R"
proof- 
  assume A0:"equivalence_relation X R" "l_cong X f R" "r_cong X f R"
  show "cong X f R"
  proof(rule congI1)
    fix x1 x2 y1 y2 assume A1:"(x1, x2) \<in> R" "(y1, y2) \<in> R" 
    then obtain B0:"x1 \<in> X" "x2 \<in> X""y1 \<in> X" "y1 \<in> X"   by (meson A0(1) equivalence_relation.l_closed equivalence_relation.r_closed)
    then obtain "(f x1 y1, f x1 y2) \<in> R" and "(f x1 y2, f x2 y2) \<in> R"
      by (meson A0(1) A0(2) A0(3) A1(1) A1(2) equivalence_relation.r_closed l_congD1 r_congD1)  
    then show "(f x1 y1, f x2 y2) \<in> R"
      by (meson A0(1) equivalence_relation.trn) 
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

notation pinv ("\<sigma>")
notation p ("\<pi>")
definition quotient_law (infixl "\<bullet>" 70) where "quotient_law \<equiv> (\<lambda>t \<in> X/R. \<lambda>s \<in> X/R.  \<pi> ((\<sigma> t) \<cdot> (\<sigma> s)))"
lemma op_compat1:"\<pi> x1 = \<pi> x2 \<Longrightarrow>\<pi> y1 = \<pi> y2 \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> y1 \<in> X \<Longrightarrow> y2 \<in> X \<Longrightarrow> \<pi> (x1 \<cdot>y1) = \<pi> (x2 \<cdot> y2)"  by (meson closed p_equivalence quotient_magma.compatible quotient_magma_axioms) 

lemma left_compatible:"a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (a\<cdot>x, a\<cdot>y) \<in> R"  using compatible by auto 
lemma right_compatible:"a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (x\<cdot>a, y\<cdot>a) \<in> R"  using compatible by auto 
lemma left_trans_compat:"\<And>a. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (l_trans a x, l_trans a y)\<in>R"   by (simp add: compatible l_closed l_trans_def r_closed)
lemma right_trans_compat:"\<And>a. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (r_trans a x, r_trans a y)\<in>R"    by (simp add: compatible r_closed r_trans_def l_closed)

lemma psecE3:"t \<in> X/R \<Longrightarrow> s \<in> X/R \<Longrightarrow>  (\<sigma> t)\<cdot>(\<sigma> s) \<in> X" by (simp add: closed sec_closed) 
lemma qlaw1:"t \<in> X/R \<Longrightarrow> s \<in> X/R  \<Longrightarrow> t\<bullet>s \<in> X/R" by (simp add: closed sec_closed quotient_law_def)  
lemma qlaw2:"x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> y1 \<in> \<pi> x1 \<Longrightarrow> y2 \<in> \<pi> x2 \<Longrightarrow> y1 \<cdot> y2 \<in> \<pi> (x1 \<cdot> x2)"  by (meson compatible p_D1 p_I1)  

lemma qlaw3: 
  assumes x0:"x \<in> X" and x1:"y \<in> X" 
  shows "(\<pi> x)\<bullet>\<pi>(y) = \<pi>(x \<cdot> y)"
proof- 
  let ?t="(\<pi> x)" and ?s="(\<pi> y)"  
  obtain a b where A0:"a \<in> X" and A1:"b \<in> X" and "a = \<sigma> ?t" and "b = \<sigma> ?s" and "\<pi> a = ?t" and "\<pi> b = ?s"
    using x0 x1 p_in_quotient1 psecE1 sec_closed by presburger
  then obtain B0:"\<sigma> (\<pi> a) = a" "\<sigma> (\<pi> b) = b" "\<pi> x = \<pi> a" "\<pi> y = \<pi> b" 
    by force
  have "(\<pi> x)\<bullet>\<pi>(y) = \<pi> ((\<sigma> (\<pi> x)) \<cdot> (\<sigma> (\<pi> y)))"  
    by (simp add: x0 x1 quotient_law_def restrict_def)
  also have "... = \<pi> (a\<cdot>b)"  
    by(simp add:B0)
  also have "... = \<pi> (x \<cdot> y)"
    by (metis A0 A1 B0(3) B0(4) x0 x1 op_compat1)  
  finally show ?thesis  
    by blast
qed

lemma qlaw4:"\<lbrakk>t \<in> X/R;s \<in> X/R\<rbrakk> \<Longrightarrow>t\<bullet>s = \<pi>((\<sigma> t) \<cdot> (\<sigma> s))"  by (metis psecE1 qlaw3 sec_closed) 

sublocale quotient: magma "X/R" "(\<bullet>)"  by (simp add: magma.intro qlaw1)

lemma proj_homomorphism:"magma_homomorphism \<pi> X (\<cdot>) (X/R) (\<bullet>)"  by(unfold_locales)(auto simp add:qlaw3)

lemma proj_epimorphism:"magma_epimorphism \<pi> X (\<cdot>) (X/R) (\<bullet>)"    by(unfold_locales)(auto simp add:qlaw3)

sublocale proj:magma_homomorphism \<pi> X f "(X/R)" "(\<bullet>)"  by (simp add: proj_homomorphism) 
sublocale proj:magma_epimorphism \<pi> X f "(X/R)" "(\<bullet>)" by (simp add: proj_epimorphism) 
lemma qlaw5:"\<lbrakk>t \<in> X/R;s \<in> X/R\<rbrakk> \<Longrightarrow>t\<bullet>s = (\<pi> (\<sigma> t)) \<bullet> (\<pi>(\<sigma> s))"  using psecE1 by auto 
lemma qlaw6:"\<lbrakk>t \<in> X/R;s \<in> X/R\<rbrakk> \<Longrightarrow>(\<pi> (\<sigma> t)) \<bullet> (\<pi>(\<sigma> s)) =\<pi>((\<sigma> t) \<cdot> (\<sigma> s))"   using psecE1 qlaw4 by presburger 

end


section \<open>Semigroup Locale\<close>
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

lemma commute_prod1:"\<lbrakk>x\<in>X;y\<in>X;z\<in>X; x\<cdot>y=y\<cdot>x;x\<cdot>z=z\<cdot>x\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x"  using commutes_assoc by auto
lemma commute_prod2:"\<lbrakk>x\<in>X;y\<in>X;z\<in>X; x\<cdot>y=y\<cdot>x;x\<cdot>z=z\<cdot>x\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = (y \<cdot> z) \<cdot> x"  by (simp add: associative) 
lemma commute_prod3:"\<lbrakk>x\<in>X;y\<in>X;z\<in>X; commutes {x} {y,z}\<rbrakk> \<Longrightarrow> commutes {x} {y \<cdot> z}" unfolding commutes_def  by (simp add: commutes_assoc)



lemma centralizer_stable:"A \<subseteq> X \<Longrightarrow> stable (centralizer A)"
  apply(rule stableI)
   apply (simp add: centralizer_sub)
  apply(rule centralizer_memI2)
  using closed magma.centralizer_sub magma_axioms apply blast
  by (simp add: centralizer_def commutes_assoc commutes_def in_mono)

lemma bicentralizer_stable:"A \<subseteq> X \<Longrightarrow> stable (bicentralizer A)"  by (simp add: centralizer_stable centralizer_sub)

lemma commuting_set_stability:
  assumes A0:"A \<subseteq> X" and A1:"B \<subseteq> X" and A2:"commutes A B"
  shows "commutes (cl A) (cl B)"
proof-
  obtain "A \<subseteq> bicentralizer A" and "B \<subseteq> centralizer A"
    using A0 A1 A2 bicentralizer_extensive commutes_sub_centralizer1 by presburger
  then obtain "cl A \<subseteq> bicentralizer A" and "cl B \<subseteq> centralizer A"
    using A0 bicentralizer_stable centralizer_stable cl_magma_stable_ub by presburger
  then show ?thesis
    using bicentralizer_commutes1 commutes_def by fastforce
qed
  
lemma left_trans_comp:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "l_trans (x \<cdot> y) = compose X (l_trans x) (l_trans y)"
proof(rule fun_eqI)
  show "l_trans (x \<cdot> y) \<in> hom X X"
    by (simp add: A0 A1 closed l_trans_hom)
  show "compose X (l_trans x) (l_trans y) \<in> hom X X"
    using A0 A1 hom2 l_trans_hom by blast
  show "\<And>z. z \<in> X \<Longrightarrow> l_trans (x \<cdot> y) z = compose X (l_trans x) (l_trans y) z"
    by (simp add: A0 A1 ltranslation_comp)
qed


lemma right_trans_comp:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "r_trans (x \<cdot> y) = compose X (r_trans y) (r_trans x)"
proof(rule fun_eqI)
  show "r_trans (x \<cdot> y) \<in> hom X X"
    by (simp add: A0 A1 closed r_trans_hom)
  show "compose X (r_trans y) (r_trans x) \<in> hom X X"
    using A0 A1 hom2 r_trans_hom by blast
  show "\<And>z. z \<in> X \<Longrightarrow> r_trans (x \<cdot> y) z = compose X (r_trans y) (r_trans x) z"
    by (simp add: A0 A1 rtranslation_comp)
qed

lemma l_cancellable_prod:
  assumes A0:"l_cancellable x" and A1:"l_cancellable y" and
          A2:"a \<in> X" and A3:"b \<in> X" and A4:"x \<cdot> y \<cdot> a = x \<cdot> y \<cdot> b" 
        shows "a = b"
proof-
  obtain x:"x \<in> X" and y:"y \<in> X" and ya:"y \<cdot> a \<in>X" and yb:"y \<cdot> b \<in> X"
    using A0 A1 A2 A3 closed l_cancellable_def by blast
  obtain "x \<cdot> (y \<cdot> a) = x \<cdot> (y \<cdot> b)"
    using A2 A3 A4 associative x y by force
  then obtain "y \<cdot> a = y \<cdot> b"
    using A0 l_cancellable_def ya yb by blast 
  then show "a = b"
    using A1 A2 A3 l_cancellable_def by blast
qed

lemma r_cancellable_prod:
  assumes A0:"r_cancellable x" and A1:"r_cancellable y" and
          A2:"a \<in> X" and A3:"b \<in> X" and A4:"a \<cdot> (x \<cdot> y) = b \<cdot> (x \<cdot> y)" 
        shows "a = b"
proof-
  obtain x:"x \<in> X" and y:"y \<in> X" and ya:"a \<cdot> x \<in>X" and yb:"b\<cdot>x \<in> X"
    using A0 A1 A2 A3 closed r_cancellable_def by blast
  obtain "(a \<cdot> x) \<cdot> y = (b \<cdot> x) \<cdot> y"
    using A2 A3 A4 associative x y by force
  then obtain "a \<cdot> x = b \<cdot> x"
    using A1 r_cancellable_def ya yb by blast 
  then show "a = b"
    using A0 A2 A3 r_cancellable_def by blast
qed

lemma l_cancellable_prod_closed:"\<lbrakk>x \<in> X;y \<in> X; l_cancellable x; l_cancellable y\<rbrakk> \<Longrightarrow> l_cancellable (x \<cdot> y)"
  by(rule l_cancellableI1, simp add: closed, auto elim:l_cancellable_prod)

lemma r_cancellable_prod_closed:"\<lbrakk>x \<in> X;y \<in> X; r_cancellable x; r_cancellable y\<rbrakk> \<Longrightarrow> r_cancellable (x \<cdot> y)"
  by(rule r_cancellableI1, simp add: closed, auto elim:r_cancellable_prod)

lemma cancellable_prod_closed:"\<lbrakk>x \<in> X;y \<in> X; cancellable x; cancellable y\<rbrakk> \<Longrightarrow> cancellable (x \<cdot> y)"
  by (meson cancellableD1 cancellableI3 l_cancellableI2 l_cancellable_prod_closed r_cancellableI2 r_cancellable_prod_closed)


lemma left_cancellable_submagma:"submagma {x \<in> X. l_cancellable x} X (\<cdot>)"
  by(unfold_locales, auto simp add:closed l_cancellable_prod_closed)

lemma right_cancellable_submagma:"submagma {x \<in> X. r_cancellable x} X (\<cdot>)"
  by(unfold_locales, auto simp add:closed r_cancellable_prod_closed)

lemma cancellable_submagma:"submagma {x \<in> X. cancellable x} X (\<cdot>)"
  by(unfold_locales, auto simp add:closed cancellable_prod_closed)

sublocale sub:magma X "(\<cdot>)"  by (simp add: magma_axioms)

lemma set_prod_assoc:"A \<subseteq> X \<Longrightarrow> B \<subseteq> X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> set_prod (set_prod A B) C= set_prod A (set_prod B C) "
proof-
  assume A0:"A \<subseteq> X" "B \<subseteq> X" "C \<subseteq> X "
  let ?AB="set_prod A B" let ?BC="set_prod B C" 
  let ?L="set_prod ?AB C" let ?R="set_prod A ?BC"
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

lemma r_coset_assoc:
  assumes A0:"E \<subseteq> X" and A1:"a\<in>X" and A2:"b\<in>X"
  shows "r_coset (r_coset E a) b = r_coset E (a \<cdot> b)" 
proof-
  have "\<And>x. x \<in> r_coset (r_coset E a) b \<longleftrightarrow> x \<in> r_coset E (a \<cdot> b)"
  proof-
    fix x
    have "x \<in> r_coset (r_coset E a) b  \<longleftrightarrow> (\<exists>y \<in> r_coset E a. x = y \<cdot> b) " by blast
    also have "... \<longleftrightarrow> (\<exists>y \<in> E. x = y \<cdot> a \<cdot> b)" by blast
    also have "... \<longleftrightarrow> (\<exists>y \<in> E. x = y \<cdot> (a \<cdot> b))"   by (metis A0 A1 A2 associative subsetD)
    also have "... \<longleftrightarrow> x \<in> r_coset E (a \<cdot> b)" by blast
    finally show "x \<in> r_coset (r_coset E a) b \<longleftrightarrow> x \<in> r_coset E (a \<cdot> b)" by blast
  qed
  then show ?thesis by blast
qed


lemma l_coset_assoc:
  assumes A0:"E \<subseteq> X" and A1:"a\<in>X" and A2:"b\<in>X"
  shows "l_coset a (l_coset b E) = l_coset (a \<cdot> b) E" 
proof-
  have "\<And>x. x \<in> l_coset a (l_coset b E) \<longleftrightarrow> x \<in> l_coset (a \<cdot> b) E"
  proof-
    fix x
    have "x \<in> l_coset a (l_coset b E)  \<longleftrightarrow> (\<exists>y \<in> l_coset b E. x = a \<cdot> y) " by blast
    also have "... \<longleftrightarrow> (\<exists>y \<in> E. x = a \<cdot> (b \<cdot> y))" by blast
    also have "... \<longleftrightarrow> (\<exists>y \<in> E. x = (a \<cdot> b) \<cdot>y)" by (metis A0 A1 A2 associative subsetD)   
    also have "... \<longleftrightarrow> x \<in> l_coset (a \<cdot> b) E" by blast
    finally show "x \<in> l_coset a (l_coset b E) \<longleftrightarrow> x \<in> l_coset (a \<cdot> b) E" by blast
  qed
  then show ?thesis by blast
qed

lemma lr_coset_assoc:
  assumes "x \<in> X" "y \<in>X" "H \<subseteq>X"
  shows "l_coset x (r_coset H y) = r_coset (l_coset x H) y"
  using set_prod_assoc[of "{x}" H "{y}"]
  by (simp add: assms l_coset_singleton_prod r_coset_singleton_prod)


end


section \<open>Quotient Semigroup Locale\<close>
locale quotient_semigroup=
  semigroup X "(\<cdot>)"+quotient_magma X "(\<cdot>)" R for X::"'a set" and f (infixl "\<cdot>" 70) and R
begin
lemma p_associative:"\<lbrakk>x \<in> X; y \<in> X; z \<in>X\<rbrakk> \<Longrightarrow> ((p x) \<bullet> (p y)) \<bullet> (p z) = (p x)\<bullet>((p y)\<bullet>(p z))" by (simp add: associative closed qlaw3)
lemma associative:"\<lbrakk>t \<in> X/R; s \<in> X/R; r \<in> X/R\<rbrakk>  \<Longrightarrow> (t\<bullet>s)\<bullet>r = t\<bullet>(s\<bullet>r)"  apply(erule projE)+  using p_associative by presburger
sublocale quotient:semigroup "X/R" "(\<bullet>)" using semigroup.intro associative quotient.magma_axioms semigroup_axioms_def by blast
lemma rel_is_cong:"cong X (\<cdot>) R" by (simp add: congI1 local.compatible)
end

locale comm_locale=fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "(\<cdot>)" 70)  assumes commutative:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow>x\<cdot>y = y\<cdot>x"
locale comm_semigroup=semigroup X "(\<cdot>)"+comm_locale X "(\<cdot>)" for X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
begin
lemma lcom:"\<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow> y\<cdot>(x\<cdot>z) = x \<cdot> (y \<cdot> z) "  by (metis associative commutative)
end

section \<open>Monoid Locale\<close>
locale monoid=semigroup+fixes unit ("e")  
  assumes idmem:"e\<in>X" and 
          leftid:"x \<in> X \<Longrightarrow> e \<cdot> x = x" and 
          rightid:"x \<in> X \<Longrightarrow> x \<cdot> e = x"
begin
definition invertible where "u \<in> X \<Longrightarrow> invertible u \<longleftrightarrow> (\<exists>v \<in> X. u \<cdot> v = e \<and> v \<cdot> u = e)"
definition inv where "inv = (\<lambda>u \<in> X. THE v. v \<in>X \<and> u \<cdot> v = e \<and> v \<cdot> u = e)"
definition set_inv where "set_inv H = (\<Union>h\<in>H. {inv h})"
lemma monoidI2:"semigroup X f \<Longrightarrow> e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x \<and> x \<cdot> e = x) \<Longrightarrow> monoid X f e" using monoid_axioms by blast
lemma ltranslation_id:"l_trans e = Id X "  by (simp add: id_elem_def id_elem_id_map(1) idmem leftid rightid)
lemma rtranslation_id:"r_trans e = Id X "  by (simp add: id_elem_def id_elem_id_map(2) idmem leftid rightid)
lemma m_closed:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y \<in> X"  by (simp add: closed)
lemma invertibleI [intro]:  "\<lbrakk> u \<cdot> v = e; v \<cdot> u = e; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> invertible u" unfolding invertible_def by fast
lemma invertibleE [elim]: "\<lbrakk>invertible u; \<And>v. \<lbrakk> u \<cdot> v = e; v \<cdot> u = e; v \<in> X \<rbrakk> \<Longrightarrow> P; u \<in> X\<rbrakk> \<Longrightarrow> P"  unfolding invertible_def by fast
lemma inverse_unique:  "\<lbrakk>u \<cdot> v' =e; v \<cdot> u = e; u \<in> X;  v \<in> X; v' \<in> X \<rbrakk> \<Longrightarrow> v = v'" by (metis associative leftid rightid)
lemma inverse_equality:  "\<lbrakk>u \<cdot> v = e; v \<cdot> u = e; u \<in> X; v \<in> X \<rbrakk> \<Longrightarrow> inv u = v" unfolding inv_def using inverse_unique by simp blast
lemma invertible_inverse_closed [intro, simp]: "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv u \<in> X" using inverse_equality by auto
lemma inverse_undefined [intro, simp]:  "u \<notin> X \<Longrightarrow> inv u = undefined"  by (simp add: inv_def)
lemma invertible_left_inverse [simp]: "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv u \<cdot> u = e" using inverse_equality by auto
lemma invertible_right_inverse [simp]:  "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> u \<cdot> inv u = e"  using inverse_equality by auto
lemma invertible_left_cancel [simp]:  "\<lbrakk> invertible x; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow> x \<cdot> y = x \<cdot> z \<longleftrightarrow> y = z" by (metis associative invertible_def leftid)
lemma invertible_right_cancel [simp]:  "\<lbrakk> invertible x; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow> y \<cdot> x = z \<cdot> x \<longleftrightarrow> y = z"  by (metis associative invertible_def rightid)
lemma inv_ident [simp]: "inv e = e"  using inverse_equality idmem leftid by blast
lemma invertible_inverse_invertible [intro, simp]:  "\<lbrakk> invertible u; u \<in> X\<rbrakk> \<Longrightarrow> invertible (inv u)"  using invertible_left_inverse invertible_right_inverse by blast
lemma invertible_inverse_inverse [simp]:  "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv (inv u) = u" by (simp add: inverse_equality)
lemma invprod:assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"invertible x" and A3:"invertible y" 
  shows "invertible (x \<cdot> y)" and "inv (x \<cdot> y) = (inv y) \<cdot> (inv x )"
proof-
  let ?a="inv x" let  ?b="inv y" let ?u="x \<cdot> y" let ?v="?b \<cdot> ?a"
  have "?u \<cdot> ?v = e"  by (simp add: associate3 associative closed leftid A0 A1 A2 A3)
  also have  "?v \<cdot> ?u = e"  by (metis A0 A1 A2 A3 associative closed invertible_inverse_closed invertible_left_inverse rightid)
  then show "inv (x \<cdot> y) = (inv y) \<cdot> (inv x) "  by (simp add: A0 A1 A2 A3 calculation closed inverse_equality)
  then show "invertible (x \<cdot> y)"
    using A0 A1 A2 A3 \<open>inv (y::'a) \<cdot> inv (x::'a) \<cdot> (x \<cdot> y) = e\<close> calculation closed invertibleI invertible_inverse_closed by presburger
qed
lemma invid:"invertible e" using idmem rightid by auto
lemma inv_right_cancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> (inv x \<cdot> y) = y" by (simp add: associate3 leftid)
lemma inv_left_cancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x \<cdot> (x \<cdot> y) = y" by (metis associative invertible_inverse_closed invertible_left_inverse leftid) 
lemma l_trans_inv1:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans x) (l_trans (inv x)) = Id X"  by (simp add: ltranslation_comp ltranslation_id)
lemma l_trans_inv2:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans (inv x)) (l_trans x) = Id X"  by (simp add: ltranslation_comp ltranslation_id) 
lemma r_trans_inv1:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans x) (r_trans (inv x)) = Id X"  by (simp add: rtranslation_comp rtranslation_id) 
lemma r_trans_inv2:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans (inv x)) (r_trans x) = Id X"  using rtranslation_comp rtranslation_id by auto 
lemma l_coset_id_prod:"H \<subseteq> X \<Longrightarrow> l_coset e H = H"
  apply(rule subset_antisym)
  using leftid subset_eq apply fastforce
  by (metis l_coset_memI leftid subset_eq)

lemma r_coset_id_prod:"H \<subseteq> X \<Longrightarrow> r_coset H e = H"
  apply(rule subset_antisym)
  using rightid subset_eq apply fastforce
  by (metis r_coset_memI rightid subset_eq)
lemma r_coset_id[simp]: "A \<subseteq> X \<Longrightarrow> r_coset A e = A" by (auto simp add: r_coset_def rightid subsetD)
lemma l_coset_id[simp]: "A \<subseteq> X \<Longrightarrow> l_coset e A = A" by (auto simp add: l_coset_def leftid subsetD)
lemma r_set_prod_id[simp]: "A \<subseteq> X \<Longrightarrow> set_prod A {e} = A" using r_coset_id r_coset_singleton_prod by auto
lemma l_set_prod_id[simp]: "A \<subseteq> X \<Longrightarrow> set_prod {e} A = A" using l_coset_id l_coset_singleton_prod by auto

end


section \<open>Sub Monoid Locale\<close>
locale submonoid=monoid X "(\<cdot>)" e   for A and X and f (infixl "\<cdot>" 70) and unit ("e") + assumes setsub:"A \<subseteq> X" and   opsub:"\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A" and   idsub:"e \<in> A"
begin
lemma subD[intro,simp]:"a \<in> A \<Longrightarrow> a \<in> X" using setsub by auto  
sublocale sub:monoid A "(\<cdot>)" e by (simp add: monoid_axioms_def monoid_def semigroup.intro associative idsub leftid magma_def opsub rightid semigroup_axioms_def)
lemma submonoid_invertible [intro, simp]:  "\<lbrakk> sub.invertible u; u \<in> A \<rbrakk> \<Longrightarrow> invertible u"  using invertibleI by blast
lemma submonoid_inverse_closed [intro, simp]:  "\<lbrakk> sub.invertible u; u \<in> A \<rbrakk> \<Longrightarrow> inv u \<in> A"using inverse_equality by auto
end

lemma submonoid_submagma:"submonoid A X f e \<Longrightarrow> submagma A X f"  by (simp add: monoid_def semigroup.axioms(1) submagmaI submonoid.opsub submonoid.setsub submonoid_def)
lemma submonoidI:"monoid X f e \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (f x y) \<in> A) \<Longrightarrow> e \<in> A \<Longrightarrow> submonoid A X f e" by (simp add: submonoid.intro submonoid_axioms.intro) 
lemma submonoid_transitive:assumes "submonoid A B f e" and "submonoid B C f e" shows "submonoid A C f e" proof-  interpret A: submonoid A B f e by fact  interpret B: submonoid B C f e by fact show ?thesis   by (simp add: A.opsub A.sub.idmem B.monoid_axioms submonoidI subset_eq) qed



locale monoid_homomorphism=
  magma_homomorphism f X "(\<cdot>)" Y "(\<star>)"+
  dom:monoid X "(\<cdot>)" e +
  cod:monoid Y "(\<star>)" i for
  X::"'a set"and  domain_law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and domain_identity ("e") and
  Y::"'b set" and codomain_law::"'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<star>" 70) and codomain_identity ("i") and 
  f::"'a \<Rightarrow> 'b"+assumes
  unital:"f e = i"
begin
lemma inverse_image_id1:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> (f x) \<star> (f (dom.inv x)) = i"  by (metis cmp dom.invertible_inverse_closed dom.invertible_right_inverse unital)
lemma inverse_image_id2:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> (f (dom.inv x)) \<star> (f x) = i"   by (metis cmp dom.invertible_inverse_closed dom.invertible_left_inverse unital) 
lemma dom_inv_cod_inv:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> cod.invertible (f x)"  using inverse_image_id1 inverse_image_id2 by auto
lemma inv_comm:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> f (dom.inv x) = cod.inv (f x)"  by (metis cod cod.inverse_equality dom.invertible_inverse_closed inverse_image_id1 inverse_image_id2)
end

lemma composition_monoid:"monoid (hom X X) (compose X) (Id X)"by(unfold_locales, auto simp add:hom2 hom3 hom5 hom6 hom7)

section \<open>Composition Monoid Locale\<close>
locale compositional_monoid =submonoid M "hom E E" "compose E" "Id E" for M and E
begin
lemma hom_mem:"f \<in> M \<Longrightarrow> f \<in> hom E E" using subD by blast
lemma eval_simp[intro, simp]:"f \<in> M  \<Longrightarrow> x \<in> E \<Longrightarrow> f x \<in> E" by(auto intro:  hom9)
lemma eval_ndef[intro,simp]:"f \<in> M \<Longrightarrow> x \<notin> E \<Longrightarrow> f x = undefined" using hom10 by fastforce
end


section \<open>Quotient Monoid Locale\<close>
locale quotient_monoid=
  monoid X "(\<cdot>)" e + 
  quotient_semigroup X "(\<cdot>)" R for
  X::"'a set" and
  f::"'a \<Rightarrow> 'a \<Rightarrow>'a" (infixl "\<cdot>" 70) and
  R::"('a \<times> 'a) set" and
  e::"'a"
begin
lemma quotient_lid:"\<And>t. t \<in> X / R \<Longrightarrow> (p e) \<bullet> t = t" by (metis idmem leftid qlaw3 rep_ex) 
lemma quotient_rid:"\<And>t. t \<in> X / R \<Longrightarrow> t \<bullet> (p e) = t" by (metis idmem rightid qlaw3 rep_ex) 
definition "H = p e"
lemma quotient_identity:"H \<in> X/R"  using H_def idmem by blast

lemma quotient_id1:"\<And>t. t \<in> X / R \<Longrightarrow> H \<bullet> t = t" using H_def quotient_lid by presburger 
lemma quotient_id2:"\<And>t. t \<in> X / R \<Longrightarrow> t \<bullet> H = t" using H_def quotient_rid by presburger 

sublocale quotient: monoid "X/R" "(\<bullet>)" "H"   by(unfold_locales)(auto simp add:quotient_identity quotient_id1 quotient_id2)
lemma rel_is_cong:"cong X (\<cdot>) R" by (simp add: congI1 local.compatible)
end


section \<open>Group Locale\<close>
locale group = 
  monoid X "(\<cdot>)" e for X and f (infixl "\<cdot>" 70) and unit ("e") + 
  assumes invertible [simp, intro]: "u \<in> X \<Longrightarrow> invertible u"
begin
lemma groupI:"(\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> X) \<Longrightarrow>  (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)) \<Longrightarrow> e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x \<and> x \<cdot> e = x) \<Longrightarrow>(\<And>x. x \<in> X \<Longrightarrow> invertible x) \<Longrightarrow>  group X f e" using group_axioms by blast 
lemma left_cancellation:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X; a\<cdot>x=a\<cdot>y\<rbrakk> \<Longrightarrow> x = y " by simp
lemma right_cancellation:"\<lbrakk>b \<in> X; x \<in> X; y \<in> X;x\<cdot>b=y\<cdot>b\<rbrakk> \<Longrightarrow> x = y " by simp
lemma double_inv_prod:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> inv (a \<cdot> inv b) \<in> X" using closed by fastforce
lemma insert_id1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (c \<cdot> inv c) \<cdot>b " using rightid by fastforce 
lemma insert_id2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (inv c \<cdot> c) \<cdot>b " using rightid by fastforce 
lemma remove_id1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> (a \<cdot> inv c) \<cdot> (c \<cdot> b) = a \<cdot>b " by (simp add: assoc4 rightid)
lemma remove_id2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> (a \<cdot> c) \<cdot> (inv c \<cdot> b) = a \<cdot>b " by (simp add: assoc4 rightid)
lemma l_inv_ex[simp]:"x \<in> X \<Longrightarrow> \<exists>y \<in> X. y \<cdot>x  = e" using invertible_left_inverse by blast
lemma r_inv_ex[simp]:"x \<in> X \<Longrightarrow> \<exists>y \<in> X. x\<cdot>y  = e" using invertible_right_inverse by blast
lemma l_inv_simp[simp]:"x \<in> X \<Longrightarrow> inv x \<cdot> x = e"  using invertible_left_inverse by blast
lemma inv_id_iff[simp]:"x \<in> X \<Longrightarrow> inv x = e \<longleftrightarrow> x = e" using invertible_inverse_inverse by fastforce
lemma r_inv_simp[simp]:"x \<in> X \<Longrightarrow> x \<cdot> inv x = e" using invertible_right_inverse by blast
lemma r_cancel[simp]:"\<lbrakk>x \<in>X; y \<in>X; z \<in>X\<rbrakk> \<Longrightarrow> y\<cdot>x = z \<cdot> x \<longleftrightarrow> y = z" by auto
lemma l_cancel[simp]:"\<lbrakk>x \<in>X; y \<in>X; z \<in>X\<rbrakk> \<Longrightarrow> x\<cdot>y =x\<cdot>z \<longleftrightarrow> y = z" by auto
lemma double_inv[simp]:"x \<in> X \<Longrightarrow> inv (inv x) = x" by simp
lemma inv_commute:"\<lbrakk>x \<cdot> y  = e; x \<in> X ; y \<in> X\<rbrakk> \<Longrightarrow> y \<cdot> x = e"  using l_inv_ex local.inverse_unique by blast
lemma inv_equality:"\<lbrakk>y \<cdot> x =e; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x = y"  using inv_commute inverse_equality by blast
lemma inv_solve_left1:"\<lbrakk>a \<in> X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a = inv b \<cdot> c \<longleftrightarrow> c = b \<cdot> a"  using inv_left_cancel inv_right_cancel by force
lemma inv_solve_right1:"\<lbrakk> a \<in>X; b \<in>X; c \<in>X\<rbrakk> \<Longrightarrow> a = b \<cdot> inv c \<longleftrightarrow> b = a \<cdot> c"  using associative rightid by force
lemma inv_solve_left2:"\<lbrakk>a \<in> X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> inv b \<cdot> c=a \<longleftrightarrow> c = b \<cdot> a"  using inv_left_cancel inv_right_cancel by force
lemma inv_solve_right2:"\<lbrakk> a \<in>X; b \<in>X; c \<in>X\<rbrakk> \<Longrightarrow>  b \<cdot> inv c=a \<longleftrightarrow> b = a \<cdot> c"  using associative rightid by force
lemma set_inv_sub:"H \<subseteq> X \<Longrightarrow> set_inv H \<subseteq> X" unfolding set_inv_def by blast
lemma set_inv_iso:"A \<subseteq> B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> set_inv A \<subseteq> set_inv B" unfolding set_inv_def   by blast
lemma set_inv_memI1:"H \<subseteq> X \<Longrightarrow> (\<exists>h \<in> H. x = inv h) \<Longrightarrow> x \<in> set_inv H"  by (simp add: set_inv_def)
lemma set_inv_memI2:"H \<subseteq> X \<Longrightarrow> h \<in> H \<Longrightarrow> x = inv h \<Longrightarrow> x \<in> set_inv H"  using set_inv_memI1 by blast 
lemma inv_prod_l_coset1:"\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;l_coset (inv x \<cdot> y) H = H\<rbrakk> \<Longrightarrow> l_coset x H = l_coset y H" by (metis invertible l_coset_assoc m_closed monoid.inv_right_cancel monoid.invertible_inverse_closed monoid_axioms)
lemma inv_prod_r_coset1:"\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;r_coset H (x \<cdot> inv y) = H\<rbrakk> \<Longrightarrow> r_coset H x = r_coset H y"  by (metis inv_solve_right1 invertible invertible_inverse_closed magma_axioms magma_def r_coset_assoc)

lemma inv_prod_l_coset2:"\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;l_coset x H = l_coset y H\<rbrakk> \<Longrightarrow> l_coset (inv x \<cdot> y) H = H"  by (metis invertible l_coset_assoc l_coset_id_prod l_inv_simp monoid.invertible_inverse_closed monoid_axioms) 
lemma inv_prod_r_coset2:"\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;r_coset H x = r_coset H y\<rbrakk> \<Longrightarrow> r_coset H (x \<cdot> inv y) = H"  by (metis invertible monoid.invertible_inverse_closed monoid_axioms r_coset_assoc r_coset_id_prod r_inv_simp) 

end

section Monoid_subgroup
locale monoid_subgroup= submonoid A X "(\<cdot>)" e + sub: group A "(\<cdot>)" e for A and X and f (infixl "\<cdot>" 70) and unit ("e")
begin
lemma monoid_subgroup_inverse_equality [simp]:  "u \<in> A \<Longrightarrow> inv u = sub.inv u" by (simp add: inverse_equality)
lemma monoid_subgroup_inverse_iff [simp]: "\<lbrakk>invertible x; x \<in> X \<rbrakk> \<Longrightarrow> inv x \<in> A\<longleftrightarrow> x \<in> A"using invertible_inverse_inverse sub.invertible_inverse_closed by fastforce
end 

lemma monoid_subgroup_transitive [trans]:  assumes "monoid_subgroup K H f e" and "monoid_subgroup H G f e" shows "monoid_subgroup K G f e" proof- interpret K: monoid_subgroup K H f e by fact  interpret H: monoid_subgroup H G f e by fact show ?thesis  by (meson H.submonoid_axioms K.sub.group_axioms K.submonoid_axioms monoid_subgroup.intro submonoid_transitive)  qed
lemma monoid_subgroup_submonoid:"monoid_subgroup H G f e \<Longrightarrow> submonoid H G f e" by (simp add: monoid_subgroup.axioms(1))  

context monoid begin
lemma monoid_subgroupI:"submonoid H X f e \<Longrightarrow> e \<in> H \<Longrightarrow> (\<And>x. x \<in> H \<Longrightarrow>  monoid.invertible H (\<cdot>) e x)  \<Longrightarrow> (\<And>x. x \<in> H \<Longrightarrow> inv  x \<in> H) \<Longrightarrow> monoid_subgroup H X f e" 
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
    and [intro]: "\<And>g. g \<in> A \<Longrightarrow> inv g \<in> A"
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
lemma invertible_right_inverse2:"\<lbrakk> invertible u; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> u \<cdot> ((inv u) \<cdot> v) = v"  using inv_right_cancel by blast
lemma invertible_right_inverse3:"\<lbrakk> invertible u; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> (u \<cdot> (inv u)) \<cdot> v = v" using invertible_right_inverse leftid by presburger 
lemma invertible_left_inverse2: "\<lbrakk> invertible u; u \<in> X; v\<in>X\<rbrakk> \<Longrightarrow> (inv u) \<cdot> (u \<cdot> v) = v" by (simp add: monoid.inv_left_cancel monoid_axioms)
lemma invertible_left_inverse3: "\<lbrakk> invertible u; u \<in> X; v\<in>X\<rbrakk> \<Longrightarrow> ((inv u \<cdot> u)) \<cdot> v = v"using invertible_left_inverse leftid by presburger 
lemma inverse_composition_commute: assumes [simp]: "invertible x" "invertible y" "x \<in> X" "y \<in> X"  shows "inv (x \<cdot> y) = inv y \<cdot> inv x"  by (simp add: monoid.invprod(2) monoid_axioms)
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

section \<open>Sub Group Locale\<close>
locale subgroup=group G "(\<cdot>)" e for H and G and f (infixl "\<cdot>" 70) and unit ("e")+
  assumes subset:"H \<subseteq> G" and
          closed:"\<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H" and
          id_mem:"e \<in> H" and
          inv_cl:"a \<in> H \<Longrightarrow> inv a \<in> H"
begin
lemma sub_mem[intro,simp]:"a \<in> H \<Longrightarrow> a \<in> G" using subset by auto
sublocale sub:group H "(\<cdot>)" e  by (metis closed group.invertible group_axioms id_mem inv_cl monoid_subgroup.axioms(2) monoid_subgroupI2 sub_mem subset) 
sublocale submonoid:submonoid H G f e  by (simp add: id_mem monoid_axioms sub.closed submonoidI subset)
lemma subgroup_inverse_equality [simp]: "u \<in> H \<Longrightarrow> inv u = sub.inv u"  by (simp add: inverse_equality)
lemma subgroup_is_subgroup1:"subgroup H G (\<cdot>) e" by (simp add: subgroup_axioms) 
lemma subgroup_is_group1:"group H (\<cdot>) e" by (simp add: sub.group_axioms)
end


context group
begin
lemma l_coset_absorb:"x \<in> X \<Longrightarrow> subgroup H X (\<cdot>) e \<Longrightarrow> l_coset x H =H \<Longrightarrow> x \<in> H"  by (metis l_coset_memI rightid subgroup.id_mem)
lemma r_coset_absorb:"x \<in> X \<Longrightarrow> subgroup H X (\<cdot>) e \<Longrightarrow> r_coset H x =H \<Longrightarrow> x \<in> H"  by (metis r_coset_memI leftid  subgroup.id_mem)

lemma r_coset_rel1:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; r_coset A (x \<cdot> (inv y)) = A\<rbrakk> \<Longrightarrow>r_coset A x = r_coset A y"  by (metis closed group.inv_solve_right2 group_axioms invertible invertible_inverse_closed r_coset_assoc)
lemma l_coset_rel1:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; l_coset (inv y \<cdot> x) A = A\<rbrakk> \<Longrightarrow>l_coset x A = l_coset y A" by (metis closed invertible invertible_inverse_closed invertible_right_inverse2 l_coset_assoc)
lemma r_coset_rel2:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; r_coset A x = r_coset A y\<rbrakk> \<Longrightarrow>r_coset A (x \<cdot> (inv y)) = A "  by (metis double_inv_prod inv_ident r_coset_assoc r_coset_id r_inv_simp rightid)
lemma l_coset_rel2:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; l_coset x A = l_coset y A\<rbrakk> \<Longrightarrow> l_coset (inv y \<cdot> x) A = A"  by (metis invertible invertible_inverse_closed l_coset_assoc l_inv_simp monoid.l_coset_id monoid_axioms)

lemma r_coset_absorb1:"\<lbrakk>x\<in>X; subgroup H X f e; r_coset H x = H\<rbrakk> \<Longrightarrow> x \<in> H "  by (metis leftid r_coset_memI subgroup.id_mem)
lemma l_coset_absorb1:"\<lbrakk>x\<in>X; subgroup H X f e; l_coset x H = H\<rbrakk> \<Longrightarrow> x \<in> H "  by (metis rightid l_coset_memI subgroup.id_mem)

lemma subgroup_solve_eq:
  assumes A0:"subgroup H X (\<cdot>) e" and A1:"x \<in> H" and A2:"y \<in> H"
  shows "\<exists>h \<in> H. y = h \<cdot> x" and "\<exists>h \<in> H. y = x \<cdot> h"       
proof-
  show "\<exists>h \<in> H. y = h \<cdot> x"
  proof-
    obtain "y = (y \<cdot> (inv x)) \<cdot> x" and "y \<cdot> inv x \<in> H"
      by (meson A0 A1 A2 inv_solve_right1 subgroup.closed subgroup.inv_cl subgroup.sub_mem)
    then show ?thesis
      by blast
  qed
  show "\<exists>h \<in> H. y = x \<cdot> h"    
  proof-
    obtain "inv x \<cdot> y \<in> H"
      by (meson A0 A1 A2 inv_solve_right1 subgroup.closed subgroup.inv_cl subgroup.sub_mem)
    then show ?thesis
      by (meson A0 A1 A2 inv_solve_left2 subgroup.sub_mem)
  qed
qed

lemma subgroup_l_cosets:
  assumes A0:"subgroup H X (\<cdot>) e" and A1:"t \<in> l_cosets H"
  shows "\<And>x y. \<lbrakk>x \<in> t; y \<in> t\<rbrakk> \<Longrightarrow> inv x \<cdot> y \<in> H"
proof-
  fix x y assume x0: "x \<in> t" and y0: "y \<in> t"
  obtain g where g0: "g \<in> X" and g1:"t = l_coset g H"
    using assms unfolding l_cosets_def by blast
  then obtain h k where h0:"h \<in> H" and h1:"x = g \<cdot> h" and k0: "k \<in> H" and k1:"y = g\<cdot> k"
    using x0 y0 unfolding l_coset_def by blast
  then have "inv x \<cdot> y= ((inv h) \<cdot> (inv g)) \<cdot> (g \<cdot> k)"
    by (metis A0 g0 invertible invprod(2) subgroup.sub_mem)
  also have " ... =  (inv h \<cdot>  (inv g \<cdot> g) \<cdot> k)"
    by (meson A0 assoc4 g0 h0 in_mono invertible invertible_inverse_closed k0 subgroup.subset)
  finally have "inv x \<cdot> y = inv h \<cdot> k"
    by (metis A0 g0 h0 in_mono invertible invertible_inverse_closed l_inv_simp rightid subgroup.subset)
  then show "inv x \<cdot> y \<in> H"
    by (metis A0 h0 k0 subgroup.closed subgroup.inv_cl) 
qed


lemma subgroup_r_cosets:
  assumes A0:"subgroup H X (\<cdot>) e" and A1:"t \<in> r_cosets H"
  shows "\<And>x y. \<lbrakk>x \<in> t; y \<in> t\<rbrakk> \<Longrightarrow>  x \<cdot> inv y \<in> H"
proof-
  fix x y assume x0: "x \<in> t" and y0: "y \<in> t"
  obtain g where g0: "g \<in> X" and g1:"t = r_coset H g"
    using assms unfolding r_cosets_def by blast
  then obtain h k where h0:"h \<in> H" and h1:"x = h \<cdot> g" and k0: "k \<in> H" and k1:"y = k\<cdot> g"
    using x0 y0 unfolding r_coset_def by blast
  then have "x \<cdot> inv y= (h \<cdot> g) \<cdot> ((inv g)  \<cdot> (inv k))"
    by (metis A0 g0 invertible invprod(2) subgroup.sub_mem)
  also have " ... =  (h \<cdot>  (g \<cdot> inv g) \<cdot> inv k)"
    by (meson A0 assoc4 g0 h0 in_mono invertible invertible_inverse_closed k0 subgroup.subset)
  finally have "x \<cdot> inv y = h \<cdot> inv k"
    by (metis A0 g0 h0 r_inv_simp rightid subgroup.sub_mem)
  then show "x \<cdot> inv y \<in> H"
    by (metis A0 h0 k0 subgroup.closed subgroup.inv_cl) 
qed

lemma l_coset_absorb2:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> l_coset x H" by (metis l_coset_memI rightid subgroup.id_mem)
lemma r_coset_absorb2:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> r_coset H x" by (metis r_coset_memI leftid subgroup.id_mem)
lemma l_coset_absorb3:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> H \<Longrightarrow>  l_coset x H =H"
proof-
  assume A0:"subgroup H X (\<cdot>) e" and A1: "x \<in> H"
  have B0:"l_coset x H \<subseteq> H"
    by (meson A0 A1 magma.intro magma.l_coset_sub order_refl subgroup.closed)
  also have B1:"H \<subseteq> l_coset x H"
  proof
    fix h assume A2:"h \<in> H" then obtain "inv x \<cdot> h \<in> H" and "h = x \<cdot> ( inv x \<cdot> h)"
      by (meson A0 A1 inv_solve_left1 subgroup.closed subgroup.inv_cl subgroup.sub_mem)
    then show "h \<in> l_coset x H"
      by (metis l_coset_memI)
  qed
  finally show "l_coset x H =H"
    by blast
qed

lemma r_coset_absorb3:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> H \<Longrightarrow>  r_coset H x =H"
proof-
  assume A0:"subgroup H X (\<cdot>) e" and A1: "x \<in> H"
  have B0:"r_coset H x \<subseteq> H"
    by (meson A0 A1 magma.intro magma.r_coset_sub order_refl subgroup.closed)
  also have B1:"H \<subseteq> r_coset H x"
  proof
    fix h assume A2:"h \<in> H" then obtain "h \<cdot> inv x \<in> H" and "h = (h \<cdot> inv x) \<cdot> x"
      by (meson A0 A1 inv_solve_right1 subgroup.closed subgroup.inv_cl subgroup.sub_mem)
    then show "h \<in> r_coset H x"
      by (metis r_coset_memI)
  qed
  finally show "r_coset H x =H"
    by blast
qed
    
    

end

context subgroup
begin
lemma subgroup_is_group [intro]:
  assumes "group G f e" shows "group H f e"
proof -
  interpret group G 
    by fact
  have "monoid G f e"  
    by (simp add: monoid_axioms)  
  then show ?thesis  
    by (simp add: sub.group_axioms)
qed
 
lemma r_cosets_elem_ne: 
  assumes "t \<in> r_cosets H" 
  shows "t \<noteq> {}"
proof -
  obtain g where "g \<in> G" "t =r_coset H g"  
    using assms unfolding r_cosets_def by blast
  hence "e \<cdot> g \<in> t"
    by (simp add: id_mem r_coset_memI)
  thus ?thesis by blast
qed

lemma l_cosets_elem_ne: 
  assumes "t \<in> l_cosets H" 
  shows "t \<noteq> {}"
proof -
  obtain g where "g \<in> G" "t =l_coset g H" 
    using assms unfolding l_cosets_def by blast
  hence "g \<cdot> e\<in> t" 
    by (simp add: id_mem l_coset_memI)
  thus ?thesis
    by blast
qed

lemma set_prod_sub:"H \<subseteq> set_prod H H"
proof
  fix h assume h:"h \<in> H"
  then obtain "h = e \<cdot> h" and "e \<in> H"
    using id_mem sub.leftid by auto
  then show "h \<in> set_prod H H"
    unfolding set_prod_def using h by blast
qed

lemma set_inv_eq1:"set_inv H \<subseteq> H"
proof
  fix h assume h:"h \<in> set_inv H"
  then obtain g where "g \<in> H" and "h = inv g"
    unfolding set_inv_def by(auto)
  then show "h \<in> H" 
    by auto
qed


lemma set_inv_eq2:"H \<subseteq> set_inv H"
proof
  fix h assume h:"h \<in> H"
  then obtain "inv h \<in> H" and "inv (inv h) = h"
    by simp
  then show "h \<in> set_inv H" 
    unfolding set_inv_def using UN_I by blast 
qed

lemma set_prod_idem:"set_prod H H = H" 
  apply(rule subset_antisym)
  apply (simp add: sub.set_prod_closed)
  by (simp add: set_prod_sub)

lemma set_inv_eq:"set_inv H = H"
  apply(rule subset_antisym)
  apply (simp add: set_inv_eq1)
  by (simp add: set_inv_eq2)

end


section \<open>Subgroups in Groups\<close>
context group
begin
lemma subgroupI1:
  assumes subset:"H \<subseteq> X" and 
          non_empty: "H \<noteq> {}" and
          closed: "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H" and
          inv_cl: "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  shows "subgroup H X f e"
  apply(unfold_locales)
  apply(auto simp add:subset closed inv_cl)
proof-
  obtain a where A0:"a \<in> H"  using non_empty by auto 
  then obtain A1:"inv a \<in> H"  using inv_cl by auto
  have "e = a \<cdot> inv a"  using A0 A1 subset by auto
  also have "... \<in> H" using A0 A1 closed by blast
  finally show "e \<in> H" by blast
qed

lemma subgroup_propsI1:
  assumes subset:"H \<subseteq> X" and 
          non_empty: "H \<noteq> {}" and
          prodinv:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> inv b \<in> H"
   shows "e \<in> H" and
         "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H" and
         "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H"
proof-
  obtain h where h:"h \<in> H"
    using non_empty by blast
  then have "e = h \<cdot> inv h"
    using subset by auto 
  also have "... \<in> H"
    using prodinv h by blast
  finally show P0:"e \<in> H" 
    by auto
  then show P1:"\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  proof-
    fix a assume a:"a \<in> H"
    have "inv a = e \<cdot> inv a"
      using a leftid subset by auto
    also have "... \<in> H"
       using prodinv a P0 by blast
    finally show "inv a \<in> H"
      by simp
  qed
  then show "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H"
  proof-
    fix a b assume a:"a \<in> H" and b1:"b \<in> H"
    then obtain b2:"inv b \<in> H"
      using P1 by auto
    have "a \<cdot> b = a \<cdot> inv (inv b)"
      using b1 subset by auto
    also have "... \<in> H"
      using a b2 prodinv by blast
    finally show " a\<cdot>b \<in> H"
      by simp
  qed
qed


lemma subgroup_propsI2:
  assumes subset:"H \<subseteq> X" and 
          non_empty: "H \<noteq> {}" and
          prodinv:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> inv a \<cdot> b \<in> H"
   shows "e \<in> H" and
         "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H" and
         "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H"
proof-
  obtain h where h:"h \<in> H"
    using non_empty by blast
  then have "e = inv h \<cdot> h"
    using subset by auto 
  also have "... \<in> H"
    using prodinv h by blast
  finally show P0:"e \<in> H" 
    by auto
  then show P1:"\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  proof-
    fix a assume a:"a \<in> H"
    have "inv a = inv a \<cdot> e"
      using a rightid subset by auto
    also have "... \<in> H"
       using prodinv a P0 by blast
    finally show "inv a \<in> H"
      by simp
  qed
  then show "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H"
  proof-
    fix a b assume a:"a \<in> H" and b1:"b \<in> H"
    then obtain b2:"inv a \<in> H"
      using P1 by auto
    have "a \<cdot> b = inv (inv a) \<cdot> b"
      using a subset by auto
    also have "... \<in> H"
      using b1 b2 prodinv by blast
    finally show " a\<cdot>b \<in> H"
      by simp
  qed
qed


lemma subgroupI2:
  assumes subset:"H \<subseteq> X" and 
          non_empty: "H \<noteq> {}" and
          prodinv:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> inv b \<in> H"
  shows "subgroup H X f e"
  using assms subgroup_propsI1[of H] subgroupI1 by presburger

lemma subgroupI3:
  assumes subset:"H \<subseteq> X" and 
          non_empty: "H \<noteq> {}" and
          prodinv:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> inv a \<cdot> b \<in> H"
  shows "subgroup H X f e"
  using assms subgroup_propsI2[of H] subgroupI1 by presburger

lemma subgroupE1:
  assumes "subgroup H X f e"
  shows "H \<subseteq> X" and "H \<noteq> {}" and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H" and "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
  using assms unfolding subgroup_def subgroup_axioms_def by(auto)+

lemma trivial_subgroup:"subgroup {e} X f e"  using idmem rightid subgroupI1 by fastforce
lemma subgroup_inverse_equality[simp]:
  assumes A0:"subgroup H X f e" and "x \<in> H"
  shows "monoid.inv H f e x= inv x"
  by (metis A0 assms(2) subgroup.subgroup_inverse_equality)
end


lemma subgroupI2:
  fixes G::"'a set" and law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::"'a"
  assumes group:"group G (\<cdot>) e" and
          subset:"H \<subseteq> G" and 
          non_empty: "H \<noteq> {}" and
          prodinv:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> (monoid.inv G (\<cdot>) e b) \<in> H"
  shows "subgroup H G (\<cdot>) e"
  by (simp add: group group.subgroupI2 non_empty prodinv subset)

lemma subgroupI3:
  fixes G::"'a set" and law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::"'a"
  assumes group:"group G (\<cdot>) e" and
          subset:"H \<subseteq> G" and 
          non_empty: "H \<noteq> {}" and
          prodinv:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow>  (monoid.inv G (\<cdot>) e a) \<cdot> b \<in> H"
  shows "subgroup H G (\<cdot>) e"
  by (simp add: group group.subgroupI3 non_empty prodinv subset)


context group
begin
lemma subgroup_r_eqsol:"\<lbrakk>x\<in>H; y \<in> H; subgroup H X f e\<rbrakk> \<Longrightarrow> \<exists>h \<in> H. y = h \<cdot> x" by (metis inv_solve_right2 subgroup.sub_mem subgroupE1(3) subgroupE1(4))
lemma subgroup_l_eqsol:"\<lbrakk>x\<in>H; y \<in> H; subgroup H X f e\<rbrakk> \<Longrightarrow> \<exists>h \<in> H. y = x \<cdot> h"  by (metis invertible invertible_right_inverse2 subgroup.inv_cl subgroup.sub_mem subgroupE1(4)) 

lemma r_cosetabsorb2:"\<lbrakk>x\<in>H; subgroup H X f e\<rbrakk> \<Longrightarrow> y \<in> r_coset H x \<Longrightarrow>  y \<in> H" using subgroupE1(4) by blast
lemma l_cosetabsorb2:"\<lbrakk>x\<in>H; subgroup H X f e\<rbrakk> \<Longrightarrow> y \<in> l_coset x H \<Longrightarrow>  y \<in> H" using subgroupE1(4) by auto

lemma r_cosetabsorb3:"\<lbrakk>x\<in>H; subgroup H X f e\<rbrakk> \<Longrightarrow> y\<in>H \<Longrightarrow> y \<in> r_coset H x" using subgroup_r_eqsol by blast 
lemma l_cosetabsorb3:"\<lbrakk>x\<in>H; subgroup H X f e\<rbrakk> \<Longrightarrow> y\<in>H \<Longrightarrow> y \<in> l_coset x H" using subgroup_l_eqsol by blast 

lemma r_coset_absorb4:"\<lbrakk>x\<in>H; subgroup H X f e\<rbrakk> \<Longrightarrow>H = r_coset H x"  by(auto,simp add: r_cosetabsorb3,simp add:r_cosetabsorb2)
lemma l_coset_absorb4:"\<lbrakk>x\<in>H; subgroup H X f e\<rbrakk> \<Longrightarrow>H = l_coset x H"  by(auto,simp add: l_cosetabsorb3,simp add:l_cosetabsorb2)

lemma l_coset_absorb_iff:
  assumes A0:"subgroup H X f e" and A1:"a \<in> X"
  shows "l_coset a H = H \<longleftrightarrow> a \<in> H"
  by (metis A0 A1 l_coset_absorb1 l_coset_absorb4)

lemma r_coset_absorb_iff:
  assumes A0:"subgroup H X f e" and A1:"a \<in> X"
  shows "r_coset H a = H \<longleftrightarrow> a \<in> H"
  by (metis A0 A1 r_coset_absorb1 r_coset_absorb4)

lemma l_coset_eq1:
  assumes A0:"subgroup H X f e" and A1:"a \<in> X" and A2:"b \<in> X" and A3:"l_coset a H = l_coset b H" 
  shows "a \<in> l_coset b H"
  by (metis A0 A1 A3 l_coset_memI rightid subgroup.id_mem)

lemma l_coset_eq2:
  assumes A0:"subgroup H X f e" and A1:"a \<in> X" and A2:"b \<in> X" and A3:"a \<in> l_coset b H"
  shows "l_coset a H = l_coset b H" 
proof-
  obtain ha where A4:"ha \<in> H" and A5:"a = b \<cdot> ha" using A3 by blast
  then obtain A6:"inv ha \<in> H" and A7:"b = a \<cdot> inv ha"  by (metis A0 A1 A2 inv_solve_right1 subgroup.sub_mem subgroupE1(3))
  have "l_coset a H \<subseteq> l_coset b H" by (metis A0 A2 A4 A5 l_coset_absorb4 l_coset_assoc subgroup.sub_mem subsetI)
  also have "l_coset b H \<subseteq> l_coset a H"  by (metis A0 A2 A4 A5 closed group.l_coset_absorb4 inv_solve_left1 l_coset_rel1 subgroup.axioms(1) subgroup.subset subsetD subsetI) 
  finally show ?thesis by simp
qed

lemma l_coset_set_inv:
  assumes A0:"subgroup H X f e" and A1:"a \<in> X" 
  shows "set_inv (l_coset a H) = r_coset H (inv a)" and 
        "set_inv (r_coset H a) = l_coset (inv a) H"
proof-
  have B0:"\<And>x. x \<in> set_inv (l_coset a H) \<Longrightarrow> x \<in>  r_coset H (inv a)"
  proof-
    fix x assume x0:"x \<in>  set_inv (l_coset a H)"
    then obtain h where h0:"h \<in> H" and h1:"x = inv (a \<cdot> h)"
      unfolding set_inv_def by(auto)
    then obtain "x = inv h \<cdot> inv a" and "inv h \<in> H"
      by (meson A0 A1 group.subgroupE1(3) group_axioms invertible invprod(2) subgroup.sub_mem)
    then show "x \<in> r_coset H (inv a)"
      by blast
  qed
  have B1:"\<And>x.  x \<in>  r_coset H (inv a) \<Longrightarrow> x \<in> set_inv (l_coset a H)"
  proof-
    fix x assume x0:"x \<in> r_coset H (inv a)"
    then obtain h where h0:"h \<in> H" and h1:"x = h \<cdot> (inv a)"
      by auto
    then obtain h2:"inv h \<in> H"
      by (simp add: A0 subgroupE1(3))
    have h3:"inv x = (inv (inv a)) \<cdot> (inv h)"
      by (metis A0 A1 h0 h1 inverse_composition_commute invertible invertible_inverse_closed subgroup.sub_mem)
    also have "... = a \<cdot> inv h"
      using A1 double_inv by presburger
    finally obtain x3:"a \<cdot> inv h \<in>  l_coset a H" and x4:"inv x = a \<cdot> inv h"
      using h2 by blast
    then obtain x5:"inv (a \<cdot> inv h) = x"
      by (metis A0 A1 double_inv double_inv_prod h0 h1 idmem inv_ident m_closed rightid subgroup.sub_mem)
    then show "x \<in> set_inv (l_coset a H)"
      unfolding set_inv_def  using x3 by blast
  qed
  have B2:"\<And>x. x \<in> set_inv (r_coset H a) \<Longrightarrow> x \<in> l_coset (inv a) H"
  proof-
    fix x assume x0:"x \<in>  set_inv (r_coset H a)"
    then obtain h where h0:"h \<in> H" and h1:"x = inv (h \<cdot> a)"
      unfolding set_inv_def by(auto)
    then obtain "x = inv a \<cdot> inv h" and "inv h \<in> H"
      by (meson A0 A1 group.subgroupE1(3) group_axioms invertible invprod(2) subgroup.sub_mem)
    then show "x \<in> l_coset (inv a) H"
      by blast
  qed
  have B3:"\<And>x.  x \<in> l_coset (inv a) H \<Longrightarrow> x \<in> set_inv (r_coset H a)"
  proof-
    fix x assume x0:"x \<in> l_coset (inv a) H"
    then obtain h where h0:"h \<in> H" and h1:"x = (inv a) \<cdot> h" and h2:"inv h \<in> H"
      by (auto simp add: A0 subgroupE1(3))
    then obtain h3:"h \<in> X" and h4:"inv a \<in> X" and h5:"x \<in> X"
      by (metis A0 A1 group.double_inv_prod group_axioms idmem inv_ident m_closed rightid subgroup.sub_mem)
    obtain h6:"inv x = inv h \<cdot> a" and h7:"inv h \<cdot> a \<in> r_coset H a"
      using A1 h1 h3 h5 inv_solve_left1 inv_solve_right1  by (simp add: h2 m_closed r_coset_memI) 
    then show "x \<in> set_inv (r_coset H a)"
      unfolding set_inv_def by (metis UN_I double_inv h5 insertI1)
  qed
  show "set_inv (l_coset a H) = r_coset H (inv a)"
    using B0 B1 by blast 
  show "set_inv (r_coset H a) = l_coset (inv a) H"
    using B2 B3 by blast
qed

lemma elem_commute_imp:
  assumes A0:"subgroup H X f e" and A1:"x \<in> X" and A2:"l_coset x (r_coset H (inv x)) = H"
  shows "l_coset x H = r_coset H x"
proof-
  have B0:"l_coset x H \<subseteq> r_coset H x"
  proof
    fix y assume A3:"y \<in> l_coset x H" then obtain h where A4:"h \<in> H" and A5:"y = x\<cdot>h" by blast
    then obtain "x\<cdot>h \<cdot>inv x \<in>l_coset x (r_coset H (inv x))" using A0 A1 lr_coset_assoc subgroupE1(1) by auto
    then obtain B0:"x\<cdot>h \<cdot>inv x \<in> H"  using A2 by blast
    then obtain "(x\<cdot>h\<cdot>inv x) \<cdot> x = x \<cdot> h"  by (metis A0 A1 A4 closed in_mono inv_solve_right2 subgroupE1(1)) 
    then show "y \<in> r_coset H x"   by (metis A5 B0 r_coset_memI)
  qed
  also have B1:"r_coset H x \<subseteq> l_coset x H"
    by (metis A0 A1 A2 calculation double_inv_prod idmem inv_ident l_inv_simp lr_coset_assoc r_coset_assoc r_coset_sub rightid subgroupE1(1))
  then show ?thesis
    by (simp add: Orderings.order_eq_iff calculation)
qed

end

context subgroup
begin

lemma l_coset_equivs:
  assumes x0:"x \<in> G" and y0:"y \<in> G"
  shows "l_coset x H = l_coset y H \<longleftrightarrow> inv x \<cdot>y \<in> H" and "inv x \<cdot>y \<in> H \<longleftrightarrow> inv y \<cdot>x \<in> H"
proof-
  have B0:"inv x \<cdot> y \<in> G"
    by (simp add: m_closed x0 y0)
  have B1:"l_coset x H = l_coset y H \<Longrightarrow> inv x \<cdot> y \<in> H"
  proof-
    assume xy:"l_coset x H = l_coset y H"
    then obtain "l_coset (inv x \<cdot> y) H = H"
      by (simp add: inv_prod_l_coset2 subset x0 y0)
    then show "inv x \<cdot> y \<in> H"
      using B0 l_coset_absorb subgroup_is_subgroup1 by presburger
  qed
  also have B2:" inv x \<cdot> y \<in> H \<Longrightarrow> l_coset x H = l_coset y H"
    using l_coset_absorb4 l_coset_rel1 subgroup_is_subgroup1 subset x0 y0 by presburger
  then show "l_coset x H = l_coset y H \<longleftrightarrow> inv x \<cdot>y \<in> H"
    using calculation by blast
  have B3:"inv x \<cdot> y \<in> H \<Longrightarrow> inv y \<cdot>x \<in> H "
  proof-
    assume "inv x \<cdot> y \<in> H" then obtain "inv (inv x \<cdot> y) \<in> H" and "inv (inv x \<cdot> y) = inv y \<cdot> x"
      by (metis double_inv inv_cl invertible monoid.invertible_inverse_closed monoid.invprod(2) monoid_axioms x0 y0)
    then show "inv y \<cdot> x \<in> H" 
      by auto
  qed
  then show "inv x \<cdot>y \<in> H \<longleftrightarrow> inv y \<cdot>x \<in> H"
    by (metis calculation inv_prod_l_coset1 l_coset_absorb_iff sub_mem subgroup_is_subgroup1 subset x0 y0)
qed


end

section \<open>Quotient Group Locale\<close>
locale quotient_group=
  group X "(\<cdot>)" e + 
  quotient_monoid X "(\<cdot>)" R e for
  X::"'a set" and
  f::"'a \<Rightarrow> 'a \<Rightarrow>'a" (infixl "\<cdot>" 70) and
  R::"('a \<times> 'a) set" and
  e::"'a"
begin

definition "qinv t \<equiv>  (p (inv (pinv t)))"

lemma id_pair:"(e, e) \<in> R" using idmem by blast

lemma equivalentE1:"(x, y) \<in> R \<Longrightarrow> inv x \<cdot> y \<in> H"
proof-
  assume xy:"(x,y) \<in> R" then obtain x0:"x \<in> X" and y0:"y \<in> X" and x1:"inv x \<in> X" by (simp add: l_closed r_closed)
  then obtain "(inv x, inv x) \<in> R" by blast
  then obtain "(inv x \<cdot> x, inv x \<cdot> y) \<in> R"  using compatible xy by blast
  then show "inv x \<cdot> y \<in> H"
    by (simp add: H_def x0)
qed

lemma equivalentI1:"\<lbrakk>x \<in> X;y \<in> X; inv x \<cdot> y \<in> H\<rbrakk> \<Longrightarrow> (x, y) \<in> R "
proof-
  assume x0:"x \<in> X" and y0:"y \<in> X" and xy:"inv x \<cdot> y \<in> H"
  then obtain "(e, inv x \<cdot> y) \<in> R" and "(x,x)\<in>R"
    using H_def idmem by auto
  then obtain "(x \<cdot> e, x \<cdot> (inv x \<cdot> y)) \<in> R"
    using compatible by blast
  then show "(x, y) \<in> R"
    by (simp add: inv_right_cancel rightid x0 y0)
qed


lemma equivalent_iff:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> (inv x) \<cdot> y \<in> H"  by (meson equivalentE1 equivalentI1)
lemma h_memI1:"(e,x) \<in> R \<Longrightarrow> x \<in> H"  by (simp add: H_def)
lemma h_memI2:"(x,e) \<in> R \<Longrightarrow> x \<in> H"  using h_memI1 local.sym by blast
lemma h_ne_sub:"H \<noteq> {} \<and> H \<subseteq> X"  using H_def idmem by auto 
lemma h_id_mem:"e \<in> H"  using H_def idmem by blast
lemma h_inv_closed:"\<And>x. x \<in> H \<Longrightarrow> inv x \<in> H" by (simp add: equivalentI1 h_memI2 idmem p_mem_closed quotient_identity rightid)
lemma h_iprod_closed:"\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> inv x \<cdot> y \<in> H"  by (metis H_def equivalentE1 idmem p_D1 p_closed1 p_eq1) 

lemma h_subgroup:"subgroup H X (\<cdot>) e"  using h_iprod_closed h_ne_sub local.subgroupI3 by presburger
lemma quotient_rinv:"x \<in> X \<Longrightarrow> (p x)\<bullet>(p (inv x)) = p e" by (simp add: qlaw3)
lemma quotient_linv:"x \<in> X \<Longrightarrow> (p (inv x))\<bullet>(p x) = p e"  by (simp add: qlaw3) 
lemma qinv_closed:"t \<in> X/R \<Longrightarrow> qinv t \<in> X/R"  using invertible invertible_inverse_closed p_in_quotient1 qinv_def sec_closed by presburger
lemma quotient_rinv2:"t \<in> X/R \<Longrightarrow> t \<bullet> qinv t = H"  by (metis H_def psecE1 qinv_def quotient_rinv sec_closed) 
lemma quotient_linv2:"t \<in> X/R \<Longrightarrow> qinv t \<bullet> t = H " by (metis H_def qinv_def psecE1 quotient_linv sec_closed)
lemma quotient_clinv:"t \<in> X/R \<Longrightarrow> quotient.invertible t"  using quotient.invertibleI[of "t" "qinv t"] quotient_rinv2[of t] quotient_linv2[of t]  qinv_closed by presburger
lemma quotient_elem_inv:"x \<in> X \<Longrightarrow>  quotient.invertible (p x) "  using proj.cod quotient_clinv by presburger

lemma quotient_inv_comp:"x \<in> X \<Longrightarrow>  quotient.inv (p x) = p (inv x)"  using H_def quotient.inverse_equality quotient_linv quotient_rinv by force 
lemma quotient_inv_unique:"t \<in> X/R \<Longrightarrow> qinv t = quotient.inv t" by (metis qinv_closed quotient.inverse_equality quotient_linv2 quotient_rinv2)
lemma quotient_is_group:"group (X/R) (\<bullet>) H" apply(rule group.intro) apply (simp add: quotient.monoid_axioms)  by (simp add: group_axioms_def quotient_clinv)

end




context group
begin
lemma subgroup_r_coset_rel:
 assumes A0:"subgroup H X f e" and A1:"t \<in> r_cosets H"
 shows "\<And>x1 x2. \<lbrakk>x1 \<in> t; x2 \<in> t\<rbrakk> \<Longrightarrow> x1 \<cdot> (inv x2) \<in> H"
proof -
  fix x1 x2 assume A2: "x1 \<in> t" and A3: "x2 \<in> t"
  obtain g where A4:"g \<in>  X" and A5:"t = r_coset H g"  using A1 unfolding r_cosets_def by blast
  then obtain h1 h2 where A6:"h1 \<in> H" and A7:"x1 = h1\<cdot>g" and A8:"h2 \<in> H" and A9:"x2 = h2 \<cdot> g"  using A2 A3 unfolding r_coset_def by blast
  hence "x1 \<cdot> (inv x2) = (h1 \<cdot> g) \<cdot> ((inv g) \<cdot> (inv h2))"  by (metis A0 A4 invertible invprod(2) subgroup.sub_mem)
  also have " ... =  (h1\<cdot>(g\<cdot>inv g)\<cdot>inv h2)"
    by (meson A0 A4 A6 A8 assoc4 invertible invertible_inverse_closed subgroup.sub_mem)
  finally have "x1\<cdot>inv x2 = h1\<cdot>inv h2"
    by (metis A0 A4 A6 invertible invertible_right_inverse rightid subgroup.sub_mem)
  thus "x1 \<cdot> inv x2 \<in> H"
    using A0 A6 A8 subgroupE1(3) subgroupE1(4) by presburger 
qed

lemma subgroup_l_coset_rel:
 assumes A0:"subgroup H X f e" and A1:"t \<in> l_cosets H"
 shows "\<And>x1 x2. \<lbrakk>x1 \<in> t; x2 \<in> t\<rbrakk> \<Longrightarrow> inv x2 \<cdot> x1 \<in> H"
proof -
  fix x1 x2 assume A2: "x1 \<in> t" and A3: "x2 \<in> t"
  obtain g where A4:"g \<in>  X" and A5:"t = l_coset g H"  using A1 unfolding l_cosets_def by blast
  then obtain h1 h2 where A6:"h1 \<in> H" and A7:"x1 = g\<cdot>h1" and A8:"h2 \<in> H" and A9:"x2 = g\<cdot>h2"  using A2 A3 unfolding l_coset_def by blast
  hence "(inv x2) \<cdot> x1 = ((inv h2) \<cdot> (inv g)) \<cdot> (g \<cdot> h1)"  by (metis A0 A4 invertible invprod(2) subgroup.sub_mem) 
  also have " ... =  ((inv h2)\<cdot>(inv g\<cdot>g)\<cdot>h1)"   by (meson A0 A4 A6 A8 assoc4 invertible invertible_inverse_closed subgroup.sub_mem)
  finally have "inv x2\<cdot> x1 = inv h2\<cdot>h1"   by (metis A0 A4 A8 invertible invertible_inverse_closed invertible_left_inverse rightid subgroup.subset subsetD)
  thus "inv x2\<cdot>x1 \<in> H"  using A0 A6 A8 subgroupE1(3) subgroupE1(4) by presburger 
qed

end




section \<open>Set Products in Groups\<close>
context group
begin

end

  

lemma quotient_by_monoid_subgroup_eqr:
  fixes G::"'a set" and  H::"'a set" 
  fixes f (infixl "\<cdot>" 70) 
  assumes A0:"group G f e" and A1:"monoid_subgroup H G f e"
  defines "RL \<equiv> {(x, y) \<in> G \<times> G. (monoid.inv G f e x) \<cdot> y \<in> H}"
  defines "RR \<equiv> {(x, y) \<in> G \<times> G. y \<cdot> (monoid.inv G f e x) \<in> H}"
  shows "is_eqrel G RL" and "is_eqrel G RR"  
proof-
  let ?inv="monoid.inv G (\<cdot>) e"
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
  defines "RL \<equiv> {(x, y) \<in> G \<times> G. (monoid.inv G f e x) \<cdot> y \<in> H}"
  defines "RR \<equiv> {(x, y) \<in> G \<times> G. y \<cdot>(monoid.inv G f e x) \<in> H}"
  shows "\<And>a x y. a \<in> G \<Longrightarrow> (x, y) \<in> RL \<Longrightarrow>  (a\<cdot>x , a\<cdot>y) \<in> RL"  and "\<And>a x y. a \<in> G \<Longrightarrow> (x, y) \<in> RR \<Longrightarrow>  (x\<cdot>a , y\<cdot>a) \<in> RR"
proof-
  let ?inv="monoid.inv G (\<cdot>) e"
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
    also have "... = monoid.inv G (\<cdot>) e (a \<cdot> x) \<cdot> (a \<cdot> y)"   by (simp add: B6)
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


context monoid
begin

primrec pow_nat (infixr "**" 80) where 
 pow_0:"x ** 0=e " | pow_Suc:"x ** Suc n=x \<cdot> (x ** n)"


lemma power_one[simp]:"e ** n=e" 
proof(induct n)   
  case 0 then show ?case 
    by simp  
next   
  case (Suc n)
  then show ?case
    by (simp add: idmem rightid) 
qed

lemma power_on_right[simp]:"x\<in>X \<Longrightarrow> x ** 1=x" by (simp add: rightid) 
lemma power_Suc0_right[simp]:"x\<in>X \<Longrightarrow> x ** Suc 0=x" using power_on_right by auto 
lemma pow_closed[simp]:"x\<in>X \<Longrightarrow> x ** n\<in>X"
proof(induct n)   
  case 0 then show ?case
    by (simp add: idmem) 
next 
  case (Suc n)
  then obtain "x**Suc n=x \<cdot> x**n" and "x**n\<in>X"
    by simp
  then show ?case
    using Suc.prems closed by auto 
qed

lemma power_commutes:"x\<in>X \<Longrightarrow> (x**n) \<cdot> x=x \<cdot> (x**n)"
proof(induct n)
  case 0 then show ?case
    by (simp add: leftid rightid)
next
  case (Suc n) then show ?case
    by (simp add: commutes_assoc)
qed

lemma power_Suc2:"x\<in>X \<Longrightarrow> x**Suc n=x**n \<cdot> x" by (simp add: power_commutes)
lemma power_add: "x\<in>X \<Longrightarrow> x**(m + n)=x**m \<cdot> x**n"
proof(induct m) 
  case 0 then show ?case
    by (simp add: leftid) 
next 
  case (Suc m)  then show ?case
    using associate3 local.power_Suc2 by auto
qed

lemma power_mult: "x\<in>X \<Longrightarrow> x**(m * n)=(x**m)**n"  by (induct n) (simp_all add: power_add)

definition elem_exponents :: "'a \<Rightarrow> nat set" where "elem_exponents x \<equiv> {n::nat. 0<n \<and> x**n=e}"

definition elem_ord::"'a \<Rightarrow> nat" where "elem_ord x \<equiv> if elem_exponents x \<noteq> {} then (Least (\<lambda>n::nat. n\<in>elem_exponents x))  else 0"

lemma elem_ord_simp1:"elem_ord x \<noteq> 0 \<Longrightarrow> elem_ord x= Least (\<lambda>n::nat. n\<in>(elem_exponents x))"  using elem_ord_def by auto
lemma elem_ord_exp:"x**(elem_ord x)=e"
proof(cases "elem_ord x =0")
  case True then show ?thesis
    by auto
next 
  case False
  then have "elem_ord x=(Least (\<lambda>n::nat. n\<in>elem_exponents x))"
    using elem_ord_simp1 by auto
  also have "...\<in>(elem_exponents x)"
    by (metis Collect_empty_eq Collect_mem_eq False LeastI elem_ord_def) 
  then show ?thesis   
    by (simp add: calculation elem_exponents_def) 
qed

lemma order_divides_exponent:
  assumes A0:"x\<in>X" and A1:"elem_ord x \<noteq> 0" and A2:"m\<in>elem_exponents x" 
  shows "(elem_ord x) dvd m"
proof- 
  obtain n where nleast:"n =(Least (\<lambda>k::nat. k\<in>elem_exponents x))" and nmem:"n\<in>elem_exponents x"  
    by (meson LeastI assms) 
  obtain B0:"x**m=e" and B1:"0 < m" 
    using assms elem_exponents_def by auto 
  then obtain B2:"m\<in>elem_exponents x"  
    by (simp add: assms) 
  then obtain B3:"n \<le> m"
    by (simp add: Least_le nleast)   
  define q where "q = m div n"
  define r where "r = m mod n"
  then obtain B4:"m=q * n + r" and B5:"0 \<le> r" and B6:"r < n"  
    using A1 bot_nat_0.extremum gr0I mod_less_divisor nleast unfolding elem_ord_def q_def r_def by presburger 
  then have B7:"e=x**m"
    using B0 by force  
  also have "... =x**(q * n + r)"
    by (simp add: B4) 
  also have "...=(x**(q * n)) \<cdot> (x**r) "
    using A0 local.power_add by auto
  also have "... = (x**n)**q \<cdot> (x**r)"
    by (simp add: A0 local.power_mult mult.commute)
  also have "... = e**q \<cdot> (x**r)"
    using A1 elem_ord_exp elem_ord_simp1 nleast by presburger
  also have "...=(e) \<cdot> (x**r)"
    by auto 
  also have "...=x**r"
    by (simp add: A0 leftid)  
  finally have "r=0" 
  proof-  
    assume A3:"e=x**r"  
    show " r=(0::nat)"   
    proof(rule ccontr) 
      assume "r \<noteq> 0" then obtain "0<r" and "r < n"
        using B6 by blast 
      also have rmem:"r\<in>elem_exponents x" 
        unfolding elem_exponents_def using A3 calculation by auto
      show False      
        using not_less_Least[of r "(\<lambda>k. k\<in>elem_exponents x)"] nleast rmem calculation by blast 
    qed
  qed 
  then have "m=q * n"
    by (simp add: B4) 
  also have "...=q * (elem_ord x) "
    using A1 elem_ord_simp1 nleast by auto 
  finally show ?thesis
    by simp
qed

lemma elem_exp_memD1:
  "\<lbrakk>x\<in>X; elem_ord x \<noteq> 0; m\<in>elem_exponents x\<rbrakk> \<Longrightarrow> (\<exists>k. m =(elem_ord x) * k )"   
  using order_divides_exponent by blast 

lemma elem_exp_memD2:
  "\<lbrakk>x\<in>X; elem_ord x \<noteq> 0; m\<in>elem_exponents x\<rbrakk> \<Longrightarrow> (\<exists>k. k \<ge>1 \<and> m =(elem_ord x) * k )"
  by (metis Least_eq_0 bot_nat_0.extremum dvd_imp_le elem_exp_memD1 elem_ord_simp1 gr0I mult.right_neutral mult_left_le nle_le order_divides_exponent) 

lemma elem_exp_memI:
  "\<lbrakk>x\<in>X; elem_ord x \<noteq> 0;(\<exists>k. k \<ge> 1 \<and> m =(elem_ord x) * k)\<rbrakk> \<Longrightarrow> m\<in>elem_exponents x"
proof- 
  assume xmem:"x\<in>X" and nzo:" elem_ord x \<noteq> 0" and mul1:"\<exists>k. k \<ge> 1 \<and> m =(elem_ord x) * k " 
  then obtain k where geq1:"k \<ge> 1" and mul2:"m =(elem_ord x) * k" 
    by blast
  have "x**(elem_ord x)=e " 
    by (simp add: elem_ord_exp)
  then obtain "(x**(elem_ord x))**k=e" 
    by simp
  then obtain "x**m=e"  
    by (simp add: local.power_mult mul2 xmem)
  then show "m\<in>elem_exponents x"  
    using elem_exponents_def mul1 nzo by force
qed

lemma elem_exp_memI2:
  "\<lbrakk>x\<in>X; elem_ord x \<noteq> 0;m > 0; (elem_ord x dvd m)\<rbrakk> \<Longrightarrow> m\<in>elem_exponents x "
  using elem_exp_memI by auto

lemma elem_pow_eq_id:
  "\<lbrakk>a\<in>X; elem_ord a \<noteq> 0; k>0; m>0\<rbrakk> \<Longrightarrow> (a**k)**m=e \<longleftrightarrow> (elem_ord a) dvd (k * m)"
proof-
  assume amem:"a\<in>X" and nzo:"elem_ord a \<noteq> 0" and kgeqz:"k > 0" and mgeqz:"m>0"
  show "(a**k)**m=e \<longleftrightarrow> (elem_ord a) dvd (k * m)" 
  proof   
    assume "(a**k)**m=e"   
    then obtain "a**(k * m)=e"
      using amem local.power_mult by auto   
    then obtain "(k * m)\<in>elem_exponents a"
      unfolding elem_exponents_def by (simp add: kgeqz mgeqz)  
    then show "(elem_ord a) dvd (k * m)"  
      using amem nzo order_divides_exponent
      by blast 
  next
    assume "(elem_ord a) dvd (k * m)" 
    then show "(a**k)**m=e" 
      by (metis amem dvd_def elem_ord_exp local.power_mult monoid.power_one monoid_axioms)
  qed
qed

lemma id_exps:
  "elem_exponents e \<noteq> {}"
  using elem_exponents_def by auto

lemma elem_ord_id:
  "elem_ord e=1" 
  unfolding elem_ord_def
  apply(simp add:id_exps)
  apply(rule Least_equality)
   apply (simp add: elem_exponents_def)
  by (simp add: elem_exponents_def)  

lemma ord_pow1:
  "\<lbrakk>a\<in>X; elem_ord a \<noteq> 0; (1::nat) \<le> (k::nat)\<rbrakk> \<Longrightarrow> elem_ord (a**k)=(elem_ord a) div (gcd( elem_ord a) k) "
proof-
  let ?b="a**k" let ?n="elem_ord a" let ?j="?n div (gcd ?n k)" 
  assume amem:"a\<in>X" and nzo:"elem_ord a \<noteq> 0" and kgeq1:"1 \<le> k" 
  have B1:"\<And>m. m>0 \<Longrightarrow>  (?b**m =e) \<longleftrightarrow>  ?j dvd m" 
  proof- 
    fix m::nat assume mgtz:"m>0" 
    then have "(?b**m =e) \<longleftrightarrow> ?n dvd k*m" 
      using amem elem_pow_eq_id kgeq1 nzo by force 
    also have "... \<longleftrightarrow> ?j dvd ((k * m) div ((gcd ?n k)))" 
      by simp 
    also have "... \<longleftrightarrow> ?j dvd m" 
      by (simp add: div_dvd_iff_mult gcd_mult_distrib_nat mult.commute nzo)  
    finally  show "(?b**m =e) \<longleftrightarrow>  ?j dvd m"
      by blast 
  qed
  then have B2:"?j\<in>elem_exponents ?b"  
    by (simp add: div_greater_zero_iff elem_exponents_def nzo)
  have B3:"\<And>m. m\<in>elem_exponents ?b \<Longrightarrow> ?j dvd m"  
    using B1 elem_exponents_def by auto 
  then have B4:"\<And>m. m\<in>elem_exponents ?b \<Longrightarrow>  ?j \<le> m"
    using dvd_imp_le elem_exponents_def by blast
  have B5:"Least (\<lambda>i::nat. i\<in>elem_exponents ?b)=?j " 
    unfolding elem_ord_def   
    apply(rule Least_equality)   
    using B2 elem_ord_def apply force 
    using B4 elem_ord_def by force
  show "elem_ord ?b=?j"  
    by (metis B2 B5 elem_ord_def empty_iff)
qed

lemma pow_fin_ord:"\<lbrakk>a\<in>X; elem_ord a \<noteq> 0\<rbrakk> \<Longrightarrow> elem_ord (a**(k::nat)) \<noteq> 0 "
proof-
  assume amem:"a\<in>X" and ford:"elem_ord a \<noteq> 0" let ?b="a**(k::nat)"
  show "elem_ord ?b \<noteq> 0" 
  proof(cases "k=0") 
    case True then show ?thesis
      by (simp add: elem_ord_id)
  next   
    case False then show ?thesis  
      by (simp add: amem div_greater_zero_iff ford ord_pow1)
  qed
qed

lemma ord_pow2:"\<lbrakk>a\<in>X; elem_ord a \<noteq> 0;(k::nat)>0;(d::nat)>0; d dvd (elem_ord a)\<rbrakk> \<Longrightarrow> elem_ord (a**k)=d \<longleftrightarrow> (\<exists>r::nat. r > 0 \<and> gcd r d=1 \<and> k=r * (elem_ord a) div d)"
proof-
  assume amem:"a\<in>X" and ford:"elem_ord a \<noteq> 0" and knz:"(k::nat)>0" and dnz:"(d::nat)>0" and ddvd:"d dvd (elem_ord a)" 
  let ?b="a**k" let ?n="elem_ord a" let ?m="?n div d" 
  have "elem_ord ?b=d \<longleftrightarrow> d=?n div (gcd ?n k)"
    using amem ford knz ord_pow1 by auto
  also have "... \<longleftrightarrow> (gcd ?n k)=?m"  
    by (metis ddvd dnz dvd_mult_div_cancel gcd.commute gcd_dvd2 gcd_eq_0_iff gcd_pos_nat knz nonzero_mult_div_cancel_right)
  also have "... \<longleftrightarrow> gcd (d * ?m) k=?m" 
    by (simp add: ddvd)
  also have "... \<longleftrightarrow> (\<exists>r::nat. r > 0 \<and> gcd r d=1 \<and> k=r * ?m)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof  
    assume ?lhs then show ?rhs 
    proof-     
      have f1: "\<forall>n na. \<not> (n::nat) dvd na \<or> na div n * n=na"     
        using dvd_div_mult_self
        by blast    
      have f2: "gcd (elem_ord a) k=elem_ord a div d"  
        using \<open>(gcd (elem_ord (a::'a)) (k::nat)=elem_ord a div (d::nat))=(gcd (d * (elem_ord a div d)) k=elem_ord a div d)\<close> \<open>gcd ((d::nat) * (elem_ord (a::'a) div d)) (k::nat)=elem_ord a div d\<close> by blast 
      then have f3: "elem_ord a div d dvd elem_ord a \<and> elem_ord a div d dvd k \<and> (\<forall>n. \<not> n dvd elem_ord a \<or> \<not> n dvd k \<or> n dvd elem_ord a div d)"  
        by (metis (no_types) gcd_unique_nat)    
      have f4: "k \<noteq> 0"      
        using knz by force 
      have f5: "\<forall>n na. \<not> (n::nat) dvd na \<or> \<not> 0 < na \<or> n \<le> na"    
        by force  
      have f6: "\<forall>n na. \<not> (n::nat) dvd na \<or> n * (na div n)=na"    
        using dvd_mult_div_cancel by blast 
      have "Suc 0 \<le> d"      
        using dnz by presburger   
      then have f7: "1 \<le> d"  
        by simp    
      have f8: "d div d=1"  
        by (simp add: dnz)   
      have f9: "d div d dvd elem_ord a div d"   
        by (simp add: ddvd)  
      then have f10: "d div d * (elem_ord a div d div (d div d))=elem_ord a div d"   
        using f6 by blast   
      have "elem_ord a div d=elem_ord a div d div (d div d)"      
        using f8 by simp
      then show ?thesis    
        using f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 by (smt (z3) One_nat_def \<open>gcd ((d::nat) * (elem_ord (a::'a) div d)) (k::nat)=elem_ord a div d\<close> amem ddvd div_greater_zero_iff dnz dvd_div_eq_0_iff dvd_refl elem_ord_exp elem_ord_id ford gcd.commute gcd_mult_distrib_nat gcd_nat.absorb_iff2 gcd_pos_nat knz local.power_mult monoid.ord_pow1 monoid_axioms nat_mult_eq_cancel1 nonzero_mult_div_cancel_right)  
    qed   
  next 
    assume ?rhs  
    then obtain r::nat where "r > 0" and "gcd r d=1" and "k=r * ?m"
      by metis  
    then show ?lhs
      by (metis gcd.commute gcd_mult_distrib_nat mult.comm_neutral mult.commute)
  qed 
  finally show "elem_ord ?b =d \<longleftrightarrow>  (\<exists>r::nat. r > 0 \<and> gcd r d=1 \<and> k=r * ?n div d)"  
    by (simp add: ddvd div_mult_swap) 
qed


lemma commute_pow1:"x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow>x \<cdot> y=y \<cdot> x \<Longrightarrow> x**(n::nat) \<cdot> y=y \<cdot> x**n"
proof- 
  assume xmem:"x\<in>X" and ymem:"y\<in>X" and comm:"x \<cdot> y=y \<cdot> x " 
  let ?xn="x**n"  show "?xn \<cdot> y=y \<cdot> ?xn" 
  proof(induct n)
    case 0 then show ?case
      by (simp add: leftid rightid ymem)
  next   
    case (Suc n) 
    then obtain "x**n \<cdot> y=y \<cdot> x **n"  
      by simp 
    let ?n1="Suc n"  
    have "x**?n1 \<cdot> y=x**n \<cdot> (x \<cdot> y)"
      using associative local.power_Suc2 pow_closed xmem ymem by presburger 
    also have "...=x**n \<cdot> (y \<cdot> x)" 
      by (simp add: comm) 
    also have "...=(x**n \<cdot> y) \<cdot> x"
      by (simp add: associative xmem ymem) 
    also have "...=(y \<cdot> x **n) \<cdot> x"  
      by (simp add: Suc)
    also have "...=y \<cdot> x**?n1"
      using associative local.power_Suc2 pow_closed xmem ymem by presburger  
    finally show ?case
      by auto 
  qed
qed    

lemma commute_pow2:"x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow>x \<cdot> y=y \<cdot> x \<Longrightarrow> x**(n::nat) \<cdot> y**(m::nat)=y**m \<cdot> x**n"
proof- 
  assume xmem:"x\<in>X" and ymem:"y\<in>X" and comm:"x \<cdot> y=y \<cdot> x " 
  let ?xn="x**n" let ?ym="y**m" 
  show "?xn \<cdot> ?ym=?ym \<cdot> ?xn"
  proof(induct m)
    case 0 then show ?case
      by (metis commute_pow1 idmem pow_0 xmem) 
  next 
    case (Suc m) then show ?case   
      by (metis comm commute_pow1 pow_closed xmem ymem)
  qed
qed

lemma commute_pow3:"x\<in>X \<Longrightarrow> y\<in>X\<Longrightarrow>x \<cdot> y=y \<cdot> x \<Longrightarrow> (x \<cdot> y)**(n::nat)=x**n \<cdot> y**n"
proof-
  assume xmem:"x\<in>X" and ymem:"y\<in>X" and comm:"x \<cdot> y=y \<cdot> x "
  let ?a="x**n" let ?b="y**n" let ?c="x \<cdot> y" show "(x \<cdot> y)**n=(x**n) \<cdot> (y**n)"
  proof(induct n) 
    case 0 then show ?case
      by (simp add: idmem leftid) 
  next  
    case (Suc n)  
    then obtain "(x \<cdot> y) ** n=x ** n \<cdot> y ** n" 
      by blast  
    let ?m="Suc n" 
    have "(x \<cdot> y) ** (Suc n)=(x \<cdot> y)**n \<cdot> (x \<cdot> y)"
      using closed local.power_Suc2 xmem ymem by blast   
    also have "...=(x ** n \<cdot> y ** n) \<cdot> (x \<cdot> y)"
      by (simp add: Suc)  
    also have "...=x**n \<cdot>( y**n \<cdot> x) \<cdot> y"
      by (simp add: assoc4 xmem ymem)  
    also have "...=x**n \<cdot>(x \<cdot> y**n) \<cdot> y" 
      using comm commute_pow1 xmem ymem by auto 
    also have "...=x**(Suc n) \<cdot> y** (Suc n)"
      using assoc4 local.power_Suc2 pow_closed xmem ymem by presburger
    finally show ?case 
      by simp
  qed
qed
lemma commute_invertible:"\<lbrakk>x\<in>X; y\<in>X; invertible x; invertible y; x \<cdot> y=y \<cdot> x\<rbrakk> \<Longrightarrow> inv x \<cdot> inv y=inv y \<cdot> inv x"  by (metis inverse_composition_commute) 

lemma fin_prod_ord:
  assumes amem:"a\<in>X" and bmem:"b\<in>X" and commute:"a \<cdot> b=b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0" 
  shows "elem_ord (a \<cdot> b) \<noteq> 0"
proof- 
  let ?m="lcm (elem_ord a) (elem_ord b)" 
  have "(a \<cdot> b)**?m=a**?m \<cdot> b**?m"
    using amem bmem commute commute_pow3 by blast 
  also have "...=e"  
    by (metis amem bmem dvdE dvd_lcm1 dvd_lcm2 elem_ord_exp local.power_mult local.power_one pow_closed rightid)
  then obtain "?m\<in>elem_exponents (a \<cdot> b)" 
    using aford bford calculation elem_exponents_def by fastforce 
  then show ?thesis
    by (metis (no_types, lifting) LeastI_ex elem_exponents_def elem_ord_def empty_iff mem_Collect_eq order_less_irrefl) 
qed

lemma commute_ords: 
  assumes amem:"a\<in>X" and bmem:"b\<in>X" and commute:"a \<cdot> b=b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0"
  shows "(lcm (elem_ord a) (elem_ord b)) div (gcd (elem_ord a) (elem_ord b)) dvd elem_ord (a \<cdot> b)" and  
        "elem_ord (a \<cdot> b) dvd (lcm (elem_ord a) (elem_ord b))"
proof- 
  let ?\<alpha>="elem_ord a" let ?\<beta>="elem_ord b"  
  have B0:"elem_ord (a \<cdot> b) \<noteq> 0" 
    by (simp add: aford amem bford bmem commute fin_prod_ord) 
  have B1:"(a \<cdot> b)**?\<beta>=a ** ?\<beta>"
    using amem bmem commute commute_pow3 elem_ord_exp pow_closed rightid by presburger 
  then have B2:"elem_ord ((a \<cdot> b)**?\<beta>)=elem_ord (a ** ?\<beta>)"
    by simp
  also have B3:"...=?\<alpha> div (gcd ?\<alpha> ?\<beta>)"
    using aford amem bford ord_pow1 by auto
  also have B4:"elem_ord ((a \<cdot> b)**?\<beta>) dvd (elem_ord (a \<cdot> b))" 
    by (metis B0 One_nat_def amem bford bmem m_closed dvd_div_mult_self dvd_mult2 dvd_refl gcd_Suc_0 gcd_dvd1 gcd_le1_nat ord_pow1)  
  then have B5:"?\<alpha> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))"  
    by (simp add: calculation) 
  have B6:"(a \<cdot> b)**?\<alpha>=b ** ?\<alpha>"
    using amem bmem commute monoid.commute_pow3 monoid.elem_ord_exp monoid.leftid monoid_axioms by fastforce 
  then have B7:"elem_ord ((a \<cdot> b)**?\<alpha>)=elem_ord (b ** ?\<alpha>)"
    by simp 
  have B8:"...=?\<beta> div (gcd ?\<alpha> ?\<beta>)" 
    by (metis One_nat_def Suc_leI aford bford bmem bot_nat_0.not_eq_extremum gcd.commute ord_pow1)  
  have B9:"elem_ord ((a \<cdot> b)**?\<alpha>) dvd (elem_ord (a \<cdot> b))" 
    by (metis B0 One_nat_def aford amem bmem m_closed dvd_div_mult_self dvd_mult2 dvd_refl gcd_Suc_0 gcd_dvd1 gcd_le1_nat ord_pow1)  
  then have B10:"?\<beta> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))" 
    by (simp add: B6 B8) 
  have B11:"gcd (?\<beta> div (gcd ?\<alpha> ?\<beta>)) (?\<alpha> div (gcd ?\<alpha> ?\<beta>))=1" 
  proof -  
    have "gcd (elem_ord a) (elem_ord b) * 1=gcd (elem_ord a) (elem_ord b) * gcd (elem_ord a div gcd (elem_ord a) (elem_ord b)) (elem_ord b div gcd (elem_ord a) (elem_ord b))"  
      by (metis (no_types) dvd_mult_div_cancel gcd_dvd1 gcd_dvd2 gcd_mult_distrib_nat mult.right_neutral)  
    then show ?thesis    
      by (metis (no_types) aford gcd.commute gcd_eq_0_iff mult_left_cancel)
  qed 
  have B12:"coprime (?\<alpha> div (gcd ?\<alpha> ?\<beta>)) (?\<beta> div (gcd ?\<alpha> ?\<beta>))" 
    using aford div_gcd_coprime by blast
  have B13:"((?\<alpha>*?\<beta>) div ((gcd ?\<alpha> ?\<beta>)*(gcd ?\<alpha> ?\<beta>))) dvd  (elem_ord (a \<cdot> b))" 
    by (metis B10 B12 B5 div_mult_div_if_dvd divides_mult gcd_dvd1 gcd_dvd2)
  have B14:"(?\<alpha>*?\<beta>) div ((gcd ?\<alpha> ?\<beta>)*(gcd ?\<alpha> ?\<beta>))=(lcm ?\<alpha> ?\<beta>) div (gcd ?\<alpha> ?\<beta>)" 
    using div_mult2_eq lcm_nat_def by presburger
  show "(lcm (elem_ord a) (elem_ord b)) div (gcd (elem_ord a) (elem_ord b)) dvd elem_ord (a \<cdot> b)" 
    by (metis B13 B14)  
  show "elem_ord (a \<cdot> b) dvd (lcm (elem_ord a) (elem_ord b))"
    by (metis B0 B6 B8 aford amem bford bmem bot_nat_0.not_eq_extremum m_closed div_greater_zero_iff div_mult_swap elem_ord_exp elem_pow_eq_id gcd_le2_nat gcd_nat.cobounded2 gcd_pos_nat lcm_nat_def)
qed



definition set_exponents where "set_exponents A \<equiv> {n::nat. 0<n \<and> (\<forall>a. a\<in>A \<longrightarrow> a**n=e)}"

definition pow_int (infixl "^" 75) where "pow_int x (z::int) \<equiv> if z < 0 then inv (x**(nat(-z))) else x**(nat z)"
lemma int_pow_int: "x^(int n)=x ** n" by (simp add: pow_int_def)

lemma pow_nat: assumes "i\<ge>0" shows "x**nat i=x^i"
proof (cases i rule: int_cases) case (nonneg n) then show ?thesis   by (simp add: int_pow_int)
next case (neg n) then show ?thesis   using assms by linarith
qed

lemma int_pow_0[simp]: "x^(0::int)=e" by (metis int_ops(1) monoid.int_pow_int monoid.pow_0 monoid_axioms)
lemma int_pow_def2: "a^z=(if z < 0 then inv (a**(nat(-z))) else a**(nat z))" by (simp add: pow_int_def)
lemma int_pow_one[simp]: "e^(z::int)=e"  by (simp add: int_pow_def2)

end

context group
begin
notation pow_int (infixl "^" 75) 


lemma int_pow_closed[intro, simp]:
"x \<in> X \<Longrightarrow> x^(i::int) \<in> X" 
  by (simp add: int_pow_def2)

lemma int_pow_1 [simp]:
  "x \<in> X \<Longrightarrow> x^(1::int) = x"  
  by (metis int_ops(2) int_pow_int power_on_right)

lemma int_pow_neg:
  "x \<in> X \<Longrightarrow> x^(-i::int) = inv (x^i)" 
  by (simp add: int_pow_def2)

lemma int_pow_neg_int: 
  "x \<in> X \<Longrightarrow>x^(-(int n)) = inv (x**n)" 
  by (simp add: int_pow_neg int_pow_int)

lemma inv_solve_left: 
  "\<lbrakk> a \<in> X; b \<in>X; c \<in>X \<rbrakk> \<Longrightarrow> a = inv b \<cdot> c \<longleftrightarrow> c = b \<cdot> a"
  by (metis inv_left_cancel inv_right_cancel invertible)

lemma nat_pow_inv:
  assumes "x \<in>X" shows "(inv x) ** (i :: nat) = inv (x ** i)"
proof (induction i)
  case 0 thus ?case by simp
next
  case (Suc i)
  have "(inv x) ** Suc i = ((inv x) ** i) \<cdot> inv x" using assms local.power_Suc2 by blast
  also have " ... = (inv (x ** i)) \<cdot> inv x"   by (simp add: Suc.IH Suc.prems)
  also have " ... = inv (x \<cdot> (x ** i))"  using assms inverse_composition_commute invertible pow_closed by presburger
  also have " ... = inv (x ** (Suc i))"   by simp
  finally show ?case  by blast
qed

lemma nat_pow_mult:
  "x \<in>X \<Longrightarrow> x ** (n::nat) \<cdot> x ** m = x ** (n + m)" 
  by (simp add: local.power_add)

lemma int_pow_mult:
  assumes A0:"x \<in>X" shows "x^(i + j::int) = (x^i) \<cdot> (x^j)"
proof -
  have [simp]: "-i - j = -j - i" by simp
  show ?thesis
  apply(auto simp add:assms int_pow_def2 inv_solve_left inv_solve_right1 nat_add_distrib[symmetric] power_add)
    apply (metis add_uminus_conv_diff assms less_imp_le local.power_add nat_add_distrib neg_0_le_iff_le)
    apply (smt (verit, best) assms local.power_add nat_add_distrib)
    apply (metis add_minus_cancel assms less_imp_le local.power_add nat_add_distrib neg_0_le_iff_le not_less)
    apply (smt (verit) assms local.power_add nat_add_distrib)
    apply (smt (verit, best) assms local.power_add nat_add_distrib)
    by (simp add: assms local.power_add nat_add_distrib)
qed

lemma int_pow_inv:"x \<in>X \<Longrightarrow> (inv x)^ (i :: int) = inv (x^i)"  by (metis int_pow_def2 nat_pow_inv)
lemma nat_pow_pow:"x \<in> X \<Longrightarrow> (x ** n) ** m = x** (n * m::nat)"  by (induct m) (simp, simp add: nat_pow_mult add.commute)
lemma int_pow_pow:
  assumes "x \<in> X"
  shows "(x^(n :: int))^(m :: int) = x^(n * m :: int)"
proof (cases)
  assume n_ge: "n \<ge> 0" thus ?thesis
  proof (cases)
    assume m_ge: "m \<ge> 0" thus ?thesis
      by (metis assms monoid.pow_nat monoid.power_mult monoid_axioms mult_nonneg_nonneg n_ge nat_mult_distrib)
  next
    assume m_lt: "\<not> m \<ge> 0" 
    with n_ge show ?thesis
      apply (simp add: int_pow_def2 mult_less_0_iff)
      by (metis assms minus_mult_commute minus_mult_left monoid.power_mult monoid_axioms nat_mult_distrib)
  qed
next
  assume n_lt: "\<not> n \<ge> 0" thus ?thesis
  proof (cases)
    assume m_ge: "m \<ge> 0" 
    have "inv x ** (nat m * nat (- n)) = inv x ** nat (- (m * n))"
      by (metis (full_types) m_ge mult_minus_right nat_mult_distrib)
    with m_ge n_lt show ?thesis
      by (simp add: int_pow_def2 mult_less_0_iff assms mult.commute nat_pow_inv nat_pow_pow)
  next
    assume m_lt: "\<not> m \<ge> 0" thus ?thesis
      using n_lt by (auto simp: int_pow_def2 mult_less_0_iff assms nat_mult_distrib_neg nat_pow_inv nat_pow_pow)
  qed
qed

lemma int_pow_diff:"x \<in> X \<Longrightarrow> x^(n - m :: int) =  x^n \<cdot> inv (x^m)" by(simp only: diff_conv_add_uminus int_pow_mult int_pow_neg)

lemma inj_on_multc:"c \<in> X \<Longrightarrow>inj_on (\<lambda>x. x \<cdot> c) X" by(simp add: inj_on_def)
lemma inj_on_cmult:"c \<in>X \<Longrightarrow> inj_on (\<lambda>x. c \<cdot> x) X" by(simp add: inj_on_def)

lemma inv_mult_group: "\<lbrakk> x \<in> X; y \<in>X\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv y \<cdot> inv x" using inverse_composition_commute by blast

lemma int_pow_mult_distrib:
  assumes eq: "x \<cdot> y = y \<cdot> x" and xy: "x \<in>X" "y \<in> X"
  shows "(x \<cdot> y)^(i::int) = (x^i) \<cdot> (y^i)"
proof (cases i rule: int_cases)
  case (nonneg n)
  then show ?thesis
    using commute_pow3 eq int_pow_int xy(1) xy(2) by presburger
next
  case (neg n)
  then show ?thesis
    unfolding neg
    apply (simp add: xy int_pow_neg_int del: of_nat_Suc)
    by (metis closed commute_pow3 eq int_pow_neg_int inv_mult_group pow_Suc pow_closed xy)
qed

lemma pow_eq_div2:
  fixes m n :: nat
  assumes x_car: "x \<in> X"
  assumes pow_eq: "x ** m = x ** n"
  shows "x ** (m - n) = e"
proof (cases "m < n")
  case False
  have "e \<cdot> x ** m = x ** m"  
    by (simp add: leftid x_car) 
  also have "\<dots> = x ** (m - n) \<cdot> x ** n" 
    using False by (simp add: nat_pow_mult x_car)
  also have "\<dots> = x ** (m - n) \<cdot> x ** m"  
    by (simp add: pow_eq)
  finally show ?thesis 
    by (simp add: idmem x_car)
qed simp



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


context subgroup
begin

lemma assoc_cancel:"a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> (b \<cdot> inv a) \<cdot> (a \<cdot> h) = b \<cdot> h"  using remove_id1 by blast 

lemma lcoset_absorb:"g \<in> G \<Longrightarrow> g \<in> l_coset g H" by (metis id_mem l_coset_memI rightid) 
lemma rcoset_absorb:"g \<in> G \<Longrightarrow> g \<in> r_coset H g" by (metis id_mem r_coset_memI leftid) 
lemma l_coset_sub:"g \<in> G \<Longrightarrow> l_coset g H \<subseteq> G" by (simp add: l_coset_singleton_prod set_prod_closed subset) 
lemma r_coset_sub:"g \<in> G \<Longrightarrow> r_coset H g \<subseteq> G" by (simp add: r_coset_singleton_prod set_prod_closed subset) 
lemma l_coset_sub_mem:"g \<in> G \<Longrightarrow> b \<in> l_coset g H \<Longrightarrow> b \<in>  G" using l_coset_sub by blast
lemma r_coset_sub_mem:"g \<in> G \<Longrightarrow> b \<in> r_coset H g \<Longrightarrow> b \<in>  G" using r_coset_sub by blast

lemma coset_absorb_iff:
  assumes "a \<in> G"
  shows "l_coset a H = H \<longleftrightarrow> a \<in> H" and  "r_coset H a = H \<longleftrightarrow> a \<in> H"
proof-
  show  "l_coset a H = H \<longleftrightarrow> a \<in> H"
    using assms l_coset_absorb4 lcoset_absorb subgroup_axioms by auto
  show  "r_coset H a = H \<longleftrightarrow> a \<in> H"
    using assms r_coset_absorb4 rcoset_absorb subgroup_axioms by auto
qed

lemma coset_assoc:
  assumes A0:"a \<in> G" "b \<in> G"
  shows "l_coset (a \<cdot> b) H = l_coset a (l_coset b H)" and "r_coset H  (a \<cdot> b) = r_coset (r_coset H a) b"
proof-
  show "l_coset (a \<cdot> b) H = l_coset a (l_coset b H)"
    by (simp add: assms(1) assms(2) l_coset_assoc subset)
  show "r_coset H  (a \<cdot> b) = r_coset (r_coset H a) b"
    by (simp add: assms(1) assms(2) r_coset_assoc subset)
qed

lemma lcoset_mem:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> (f (inv x) y \<in> H)  \<longleftrightarrow> (y \<in> (l_coset x H))" by (metis coset_absorb_iff(1) inv_solve_left1 l_coset_memE l_coset_rel1 lcoset_absorb sub_mem subset)
lemma rcoset_mem:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> (f y (inv x) \<in> H)  \<longleftrightarrow> (y \<in> (r_coset H x))"  by (metis coset_absorb_iff(2) inv_solve_right2 r_coset_memE r_coset_rel1 rcoset_absorb sub_mem subset)
lemma l_coset_bij:"g \<in> G \<Longrightarrow> bij_betw (\<lambda>x. g\<cdot>x) H (l_coset g H)" by(auto simp add:bij_betw_def, auto intro: inj_onI)
lemma r_coset_bij:"g \<in> G \<Longrightarrow> bij_betw (\<lambda>x. x\<cdot>g) H (r_coset H g)" by(auto simp add:bij_betw_def, auto intro: inj_onI)
lemma l_coset_inj:
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "inj_on (\<lambda>x. inv (a \<cdot> inv b) \<cdot> x)  (l_coset a H)" and
        "inj_on (\<lambda>x. inv (a \<cdot> inv b) \<cdot> x)  (l_coset b H)" and
        "inj_on (\<lambda>x. (b \<cdot> inv a) \<cdot> x)  (l_coset a H)" and
        "inj_on (\<lambda>x. (b \<cdot> inv a) \<cdot> x)  (l_coset b H)"
proof-
  let ?c="inv (a \<cdot> inv b)"
  obtain B0:"?c\<in>G" using A0 A1 double_inv_prod by blast
  show P0:"inj_on (\<lambda>x. inv (a \<cdot> inv b) \<cdot> x)  (l_coset a H)"
  proof(rule inj_onI)
    fix x y assume A2:"x \<in> l_coset a H" and A3:" y \<in>l_coset a H" and  A4:"?c \<cdot> x = ?c \<cdot> y"
    then show "x = y" using left_cancellation[of ?c x y]  A0 B0 l_coset_sub_mem by blast
  qed
  show P1:"inj_on (\<lambda>x. inv (a \<cdot> inv b) \<cdot> x)  (l_coset b H)"
  proof(rule inj_onI)
    fix x y assume A2:"x \<in> l_coset b H" and A3:" y \<in>l_coset b H" and  A4:"?c \<cdot> x = ?c \<cdot> y"
    then show "x = y" using left_cancellation[of ?c x y] A1 B0 l_coset_sub_mem by presburger 
  qed
  have B1:"inv (a \<cdot> inv b) = (b \<cdot> inv a)"  by (simp add: A0 A1 invprod)
  show P2:"inj_on (\<lambda>x. (b \<cdot> inv a) \<cdot> x)  (l_coset a H)" using B1 P0 by presburger 
  show P2:"inj_on (\<lambda>x. (b \<cdot> inv a) \<cdot> x)  (l_coset b H)" using B1 P1 by presburger 
qed

lemma r_coset_inj:
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "inj_on (\<lambda>x. x \<cdot> (inv b \<cdot> a)) (r_coset H a)" and
        "inj_on (\<lambda>x. x \<cdot> (inv b \<cdot> a)) (r_coset H b)" and
        "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv a)) (r_coset H a)" and
        "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv a)) (r_coset H b)" and
        "inj_on (\<lambda>x. x \<cdot> (inv a \<cdot> b)) (r_coset H a)"       
proof -
  let ?c = "inv b \<cdot> a"
  have B0:"?c \<in> G"  by (simp add: A0 A1 magma.closed magma_axioms) 
  show "inj_on (\<lambda>x. x \<cdot> (inv b \<cdot> a)) (r_coset H a)"
  proof (rule inj_onI)
    fix x y assume "x \<in> r_coset H a" and "y \<in> r_coset H a" and "x \<cdot> ?c = y \<cdot> ?c"
    then show "x = y" using  A0 B0 r_coset_sub_mem right_cancellation[of ?c x y] by blast
  qed
  show "inj_on (\<lambda>x. x \<cdot> (inv b \<cdot> a)) (r_coset H b)"
  proof (rule inj_onI)
    fix x y assume "x \<in> r_coset H b" and "y \<in> r_coset H b" and "x \<cdot> ?c = y \<cdot> ?c"
    then show "x = y" using  A1 B0 r_coset_sub_mem right_cancellation[of ?c x y] by blast
  qed
  have B3:"inv (a \<cdot> inv b) = (b \<cdot> inv a)"  by (simp add: A0 A1 invprod(2))
  have B4:"(b \<cdot> inv a) \<in> G"    by (simp add: A0 A1 magma.closed magma_axioms)
  show "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv a)) (r_coset H a)"  by (meson A0 B4 inj_onI r_coset_sub_mem right_cancellation) 
  show "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv a)) (r_coset H b)" by (meson A1 B4 inj_onI r_coset_sub_mem right_cancellation)    
  show "inj_on (\<lambda>x. x \<cdot> (inv a \<cdot> b)) (r_coset H a)"   by(auto simp add:inj_on_def,metis A0 A1 invertible invertible_inverse_closed magma.closed magma_axioms r_coset_sub_mem right_cancellation)
qed    
 
lemma coset_bij1: 
  assumes A0:"a \<in> G"
  shows "bij_betw (\<lambda>x. inv x) (l_coset a H) (r_coset H (inv a))"
proof(auto simp add:bij_betw_def)
  show "inj_on inv (l_coset a H)"  by (metis A0 inj_onI invertible invertible_inverse_inverse l_coset_sub_mem)
  show "\<And>x. x \<in> (l_coset a H) \<Longrightarrow> inv x \<in> (r_coset H (inv a))" using assms monoid.invprod(2) monoid_axioms by fastforce
  show "\<And>x. x \<in> r_coset H( inv a) \<Longrightarrow> x \<in> inv ` (l_coset a H)"   by (metis assms imageI inv_cl invertible invertible_inverse_closed invertible_inverse_inverse invprod(2) lcoset_mem r_coset_sub_mem rcoset_mem)
qed

lemma coset_bij2: 
  assumes A0:"a \<in> G" and A1:"b \<in> G"
  shows "bij_betw (\<lambda>x. b \<cdot> inv a \<cdot> x) (l_coset a H) (l_coset b H)" 
proof-
  show "bij_betw (\<lambda>x. b \<cdot> inv a \<cdot> x) (l_coset a H) (l_coset b H)"
  proof(auto simp add:bij_betw_def)
    show "inj_on (\<lambda>x. b \<cdot> inv a \<cdot> x)  (l_coset a H)"  by (simp add: A0 A1 l_coset_inj(3))
    show "\<And>x. x \<in> (l_coset a H) \<Longrightarrow> b \<cdot> inv a \<cdot> x \<in> (l_coset b H)"
    proof-
      fix x assume "x \<in> (l_coset a H) " then obtain h where "h \<in> H" and "x = a \<cdot> h" by auto
      then have "(b \<cdot> inv a) \<cdot> x = (b \<cdot> inv a) \<cdot> (a \<cdot> h)" by blast
      also have "... = b \<cdot> h"   using A0 A1 \<open>(h::'a) \<in> (H::'a set)\<close> remove_id1 by blast
      also have "... \<in> l_coset b H" using \<open>(h::'a) \<in> (H::'a set)\<close> by auto
      finally show "b \<cdot> inv a \<cdot> x \<in> (l_coset b H)" by blast
    qed
    show "\<And>x. x \<in> l_coset b H \<Longrightarrow> x \<in> (\<lambda>x. b \<cdot> inv a \<cdot> x) ` (l_coset a H)"
    proof-
      fix x assume B0:"x \<in> (l_coset b H) " then obtain h where B1:"h \<in> H" and B2:"x = b \<cdot> h" by auto
      then have "b \<cdot> h = b \<cdot> (inv a \<cdot> a) \<cdot> h"  by (simp add: A0 A1 rightid)
      also have "... = (b \<cdot> inv a) \<cdot> (a \<cdot> h)"using A0 A1 B1 calculation remove_id1 sub_mem by presburger
      also have "... \<in> (\<lambda>x. b \<cdot> inv a \<cdot> x) ` (l_coset a H)" using B1 by blast
      finally show "x \<in> (\<lambda>x. b \<cdot> inv a \<cdot> x) ` (l_coset a H)"  using B2 by fastforce
    qed
  qed
qed

lemma coset_eq_iff:
  assumes A0:"a \<in>G" and A1:"b \<in> G"
  shows "l_coset a H = l_coset b H \<longleftrightarrow>  a \<in> l_coset b H" and
        "l_coset a H = l_coset b H \<longleftrightarrow> inv a \<cdot> b \<in> H" and
        "r_coset H a = r_coset H b \<longleftrightarrow> b \<in> r_coset H a" and
        "r_coset H a = r_coset H b \<longleftrightarrow> b\<cdot> inv a  \<in> H"
proof-
  show P0:"l_coset a H = l_coset b H \<longleftrightarrow>  a \<in> l_coset b H"
    by (metis A0 A1 coset_absorb_iff(1) coset_assoc(1) l_coset_memE lcoset_absorb sub_mem) 
  show P1: "l_coset a H = l_coset b H \<longleftrightarrow> inv a \<cdot> b \<in> H"
    by (metis A0 A1 coset_absorb_iff(1) coset_assoc(1) l_coset_memE lcoset_absorb lcoset_mem sub_mem) 
  show P2:"r_coset H a = r_coset H b \<longleftrightarrow> b \<in> r_coset H a"
    by (metis A0 A1 coset_absorb_iff(2) coset_assoc(2) r_coset_memE rcoset_absorb sub_mem) 
  show P3:"r_coset H a = r_coset H b \<longleftrightarrow> b\<cdot> inv a  \<in> H"
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


definition l_sub_eq where "l_sub_eq \<equiv> {(x, y) \<in> G \<times> G. (inv x)\<cdot>y \<in> H}" 
definition r_sub_eq where "r_sub_eq \<equiv> {(x, y) \<in> G \<times> G. y\<cdot>(inv x) \<in> H}" 

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
  shows "l_coset a H = l_coset b H \<longleftrightarrow> (inv a) \<cdot> b \<in> H" and
        "l_coset a H = l_coset b H \<longleftrightarrow> (inv b) \<cdot> a \<in> H" and
        "r_coset H a = r_coset H b \<longleftrightarrow> b \<cdot> (inv a) \<in> H" and
        "r_coset H a = r_coset H b \<longleftrightarrow> a \<cdot> (inv b)\<in> H"
proof-
   show P0:"l_coset a H = l_coset b H \<longleftrightarrow> (inv a) \<cdot> b \<in> H"
     using A0 A1 coset_eq_iff(2) by presburger 
   show P1:"l_coset a H = l_coset b H \<longleftrightarrow> (inv b) \<cdot> a \<in> H"
     using A0 A1 coset_eq_iff(2) by blast 
   show P2:"r_coset H a = r_coset H b \<longleftrightarrow> b \<cdot> (inv a) \<in> H"
     by (simp add: A0 A1 coset_eq_iff(3) rcoset_mem) 
   show P3:"r_coset H a = r_coset H b \<longleftrightarrow> a \<cdot> (inv b)\<in> H"
     using A0 A1 coset_eq_iff(4) by blast
qed*)

lemma r_cosets_memD:"t \<in>r_cosets H \<Longrightarrow> \<exists>g \<in> G. t = r_coset H g" unfolding r_cosets_def by blast
lemma l_cosets_memD:"t \<in>l_cosets H \<Longrightarrow> \<exists>g \<in> G. t = l_coset g H" unfolding l_cosets_def by blast
lemma r_cosets_memD2:"t \<in>r_cosets H \<Longrightarrow> g \<in> G \<Longrightarrow> t = r_coset H g \<Longrightarrow> g \<in> t"  using rcoset_absorb by auto 
lemma l_cosets_memD2:"t \<in>l_cosets H \<Longrightarrow> g \<in> G \<Longrightarrow> t = l_coset g H \<Longrightarrow> g \<in> t"  using lcoset_absorb by auto 

lemma r_cosets_memD3:"t \<in>r_cosets H \<Longrightarrow> t \<subseteq> G" using r_coset_sub r_cosets_memD by blast 
lemma l_cosets_memD3:"t \<in>l_cosets H \<Longrightarrow> t \<subseteq> G" using l_coset_sub l_cosets_memD by blast 
lemma r_cosets_memI1:"g \<in> G\<Longrightarrow> r_coset H g \<in> r_cosets H" unfolding r_cosets_def by(auto)
lemma l_cosets_memI1:"g \<in> G\<Longrightarrow> l_coset g H \<in> l_cosets H" unfolding l_cosets_def by(auto)
lemma r_cosets_ne:"t \<in> r_cosets H \<Longrightarrow> t \<noteq> {}"  using r_cosets_memD rcoset_absorb by auto
lemma l_cosets_ne:"t \<in> l_cosets H \<Longrightarrow> t \<noteq> {}"  using l_cosets_memD lcoset_absorb by auto

lemma r_cosets_disj:"t \<in> r_cosets H \<Longrightarrow> s \<in> r_cosets H \<Longrightarrow> t \<inter> s \<noteq> {} \<Longrightarrow> t = s"  by (metis r_coset_eq_or_disjoint r_cosets_memD)
lemma l_cosets_disj:"t \<in> l_cosets H \<Longrightarrow> s \<in> l_cosets H\<Longrightarrow> t \<inter> s \<noteq> {} \<Longrightarrow> t = s"  by (metis l_coset_eq_or_disjoint l_cosets_memD)
lemma r_cosets_card:"t \<in> r_cosets H\<Longrightarrow> card t = card H" using r_coset_card3 r_cosets_memD by blast
lemma l_cosets_card:"t \<in> l_cosets H \<Longrightarrow> card t = card H" using l_coset_card3 l_cosets_memD by blast
lemma r_cosets_un:"\<Union>(r_cosets H) = G" apply(rule order_antisym) using r_cosets_memD3 apply blast  using r_cosets_memD2 r_cosets_memI1 by blast
lemma l_cosets_un:"\<Union>(l_cosets H) = G" apply(rule order_antisym) using l_cosets_memD3 apply blast  using l_cosets_memD2 l_cosets_memI1 by blast

lemma lagrange_l:
  "(card H) * (card (r_cosets H)) = card G"
  by (metis (no_types, lifting) card_eq_0_iff card_partition finite_Union finite_UnionD mult.commute mult_0_right r_cosets_card r_cosets_disj r_cosets_un)

lemma lagrange_r:
  "(card H) * (card (l_cosets H)) = card G"
  by (metis card.infinite card_partition finite_Union finite_UnionD l_cosets_card l_cosets_disj l_cosets_un mult_is_0)

end


section \<open>Normal Subgroups\<close>

locale normal_subgroup=subgroup H G "(\<cdot>)" e for H and G and f (infixl "\<cdot>" 70) and e+
      assumes normal:"g \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> g \<cdot> h \<cdot> inv g \<in>  H"
begin
lemma conj_closed:"g \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> inv g \<cdot> h \<cdot> g \<in> H"  by (metis invertible invertible_inverse_inverse monoid.invertible_inverse_closed monoid_axioms normal)
lemma l_coset_eq_r_coset:"\<And>g. g \<in> G \<Longrightarrow> l_coset g H = r_coset H g"
proof-
  fix g assume A0:"g \<in> G"
  show "l_coset g H = r_coset H g"
  proof
    show "l_coset g H \<subseteq> r_coset H g"
    proof
      fix x assume A1:"x \<in> l_coset g H"
      then obtain h where A2:"h \<in> H" and A3:"x = g \<cdot> h" by blast
      then have B0:"x \<cdot> (inv g) = g \<cdot> h \<cdot> (inv g)" by blast
      also have B1:"... \<in> H"  by (simp add: A0 A2 normal)
      then obtain B2:"x \<cdot> (inv g) \<in> H"  using calculation by presburger
      have "(x \<cdot> (inv g)) \<cdot> g = x" by (metis A0 A1 A3 B1 inv_solve_right2 l_coset_sub_mem sub_mem)
      then show "x\<in> r_coset H g"  using A0 A1 B2 l_coset_sub_mem rcoset_mem by blast
    qed
    show "r_coset H g \<subseteq> l_coset g H"
    proof
      fix x assume A1:"x \<in> r_coset H g"
      then obtain h where A2:"h \<in> H" and A3:"x = h \<cdot> g" by blast
      then have B0:"(inv g) \<cdot> x =  (inv g) \<cdot> h \<cdot> g"   by (simp add: A0 associative) 
      also have B1:"... \<in> H"   by (simp add: A0 A2 conj_closed)
      then obtain B2:"(inv g) \<cdot> x \<in> H"  using calculation by presburger
      have "(g \<cdot> (inv g)) \<cdot> x = x"   using A0 A1 invertible invertible_right_inverse leftid r_coset_sub_mem by presburger
      then show "x\<in> l_coset g H"  using A0 A1 B2 lcoset_mem r_coset_sub_mem by blast  
    qed
  qed
qed

end

context subgroup begin
lemma l_coset_eq_r_coset_normal:
  assumes [simp]: "\<And>g. g \<in> G \<Longrightarrow> l_coset g  H = r_coset H g"
  shows "normal_subgroup H G (\<cdot>) e"
proof
  fix g h
  assume[simp]: "g \<in> G" "h \<in> H"
  have "h \<cdot> g \<in> l_coset g  H" by auto
  then obtain k where "h \<cdot> g = g \<cdot> k" and "k \<in> H" by blast
  then show "g \<cdot> h \<cdot> inv g \<in> H" by (metis \<open>(g::'a) \<in> (G::'a set)\<close> \<open>(h::'a) \<in> (H::'a set)\<close> assms magma.closed magma.l_coset_memI magma_axioms sub_mem subgroup.rcoset_mem subgroup_axioms) 
qed

end

context group
begin


lemma l_coset_cancel:"A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> x \<in> l_coset b A \<Longrightarrow> inv b \<cdot> x \<in> A"  using monoid.invertible_left_inverse2 monoid_axioms by fastforce
lemma r_coset_cancel:"A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> x \<in> r_coset A b \<Longrightarrow> x \<cdot> inv b \<in> A"  by (metis IntD2 closed inf.orderE inv_solve_right2 r_coset_memE)  
lemma l_coset_eq_r_cosetE:"A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> l_coset b A = r_coset A b \<Longrightarrow>  a \<in> A \<Longrightarrow> b \<cdot> a \<cdot> (inv b) \<in> A" using r_coset_cancel by blast

lemma l_coset_sub_r_cosetI:
  assumes A0:"A \<subseteq> X" and A1:"b \<in> X" and A2:"(\<And>a.  a \<in> A \<Longrightarrow> b \<cdot> a \<cdot> (inv b) \<in> A)"
  shows "l_coset b A \<subseteq> r_coset A b"
proof
    fix x assume "x \<in> l_coset b A" then obtain a where "a \<in> A" and "x = b \<cdot> a" by blast
    then obtain "b \<cdot> a \<cdot> (inv b) \<in> A" and "x = b \<cdot> a \<cdot> (inv b) \<cdot> b"   using A0 A1 A2 associative closed rightid by auto
    then show "x \<in> r_coset A b" by blast
qed

lemma r_coset_sub_l_cosetI:
  assumes A0:"A \<subseteq> X" and A1:"b \<in> X" and A2:"(\<And>a.  a \<in> A \<Longrightarrow> (inv b) \<cdot> a \<cdot> b \<in> A)"
  shows "r_coset A b \<subseteq> l_coset b A"
proof
    fix x assume "x \<in> r_coset A b" then obtain a where "a \<in> A" and "x = a \<cdot> b" by blast
    then obtain "(inv b) \<cdot> a \<cdot> b \<in> A" and "x = b \<cdot> ((inv b) \<cdot> a \<cdot> b)"  using A0 A1 A2 associative closed inv_right_cancel by auto 
    then show "x \<in> l_coset b A" by blast 
qed

definition normalizer where "normalizer A \<equiv> {b \<in> X. l_coset b A = r_coset A b}" 

 
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
  shows "d =  (f x)\<star>(f (dom.inv x))" and "d = (f (dom.inv x))\<star>(f x)"
proof-
  have "d = f e" by (simp add: map_id)
  also have "... =  f (x \<cdot> (dom.inv x))" by(simp add:A0)
  also have "... = (f x)\<star>(f (dom.inv x))"  using A0 cmp by blast
  finally show "d =  (f x)\<star>(f (dom.inv x))" by blast
  have "d = f e" by (simp add: map_id)
  also have "... =  f ((dom.inv x)\<cdot> x)" by(simp add:A0)
  also have "... = (f (dom.inv x))\<star>(f x)"  using A0 cmp by blast
  finally show "d =  (f (dom.inv x))\<star>(f x)" by blast
qed

lemma map_inv:"x \<in> X \<Longrightarrow> cod.inv (f x) = f (dom.inv x)"  using cod.inverse_equality map_inv_id by auto
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
lemma ker_inc:"a \<in> Ker \<Longrightarrow> dom.inv a \<in> Ker"  by (metis Ker_closed Ker_image Ker_memI1 cod.inv_ident dom.invertible dom.invertible_inverse_closed map_inv)
lemma Ker_memI2:assumes A0:"x \<in> X" and A1:"k \<in> Ker" shows "(dom.inv x) \<cdot> k \<cdot> x \<in> Ker" by (metis (full_types) A0 A1 Ker_closed Ker_image Ker_memI1 cmp dom.closed dom.idmem dom.invertible dom.invertible_inverse_closed dom.rightid map_id map_inv_id(2))
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

lemma conj_closed:"\<And>g k. \<lbrakk>g\<in>X;k\<in>Ker\<rbrakk>\<Longrightarrow>g \<cdot> k \<cdot> dom.inv g\<in>Ker"  by (metis Ker_memI2 dom.double_inv dom.invertible dom.invertible_inverse_closed)

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
      


context group
begin
inductive_set group_generated::"'a set \<Rightarrow> 'a set" for A where
  idm:"e \<in> group_generated A"
 |iso:"a \<in> A \<Longrightarrow> a \<in> group_generated A"
 |inv:"a \<in> A \<Longrightarrow> inv a \<in> group_generated A"
 |opc:"a \<in> group_generated A \<Longrightarrow> b \<in> group_generated A \<Longrightarrow> a\<cdot>b \<in> group_generated A"

lemma group_generate: "a \<in> group_generated (X \<inter> A) \<Longrightarrow> a \<in> X"
  apply (induction rule: group_generated.induct)
  apply (simp add: idmem)
  apply simp
  apply simp
  by (simp add: closed) 


definition cl_group:: "'a set \<Rightarrow> 'a set"  where "cl_group S = group_generated (X \<inter> S)"

lemma inverse_in_cl: "a \<in> cl_group H \<Longrightarrow> inv a \<in> cl_group H"
  unfolding cl_group_def
apply(induction rule: group_generated.induct)
  apply (simp add: group_generated.idm)
  using group_generated.inv apply force
  using group_generated.iso apply force
  by (simp add: group_generate group_generated.opc invprod(2))

lemma cl_monoid: "monoid (cl_group H) (\<cdot>) e"
  unfolding cl_group_def monoid_def semigroup_def magma_def semigroup_axioms_def monoid_axioms_def
  apply(auto)
  using group_generated.opc apply blast
  apply (simp add: associative group_generate)
  apply (simp add: group_generated.idm)
  apply (simp add: group_generate leftid)
  by (simp add: group_generate rightid)

  
lemma cl_sub: "cl_group H \<subseteq> X" using cl_group_def group_generate by blast 

lemma cl_subgroup: "subgroup (cl_group H) X (\<cdot>) e"
  apply(rule subgroupI1)
  apply (simp add: cl_sub)
  using cl_group_def group_generated.idm apply blast
  apply (simp add: cl_group_def group_generated.opc)
  by (simp add: inverse_in_cl)



lemma cl_group_ub:
  assumes A0:"A \<subseteq> B" and A1:"subgroup B X (\<cdot>) e" 
  shows "cl_group A \<subseteq> B"
proof
  fix x assume "x \<in> cl_group A"
  then show "x \<in> B"
    unfolding cl_group_def
    apply(induction rule: group_generated.induct)
    apply (meson A1 subgroup.id_mem)
    using A0 apply blast
    apply (metis A0 A1 Int_iff group.subgroupE1(3) group_axioms inf.absorb_iff2)
    by (simp add: A1 subgroupE1(4))
qed

lemma cl_group_iso:
  assumes A0:"A \<subseteq> B"  shows "cl_group A \<subseteq> cl_group B"
proof
  fix x assume "x \<in> cl_group A"
  then show "x \<in> cl_group B" unfolding cl_group_def
   apply(induction rule: group_generated.induct)
    apply (simp add: group_generated.idm)
    using assms group_generated.iso apply auto[1]
    using assms group_generated.inv apply auto[1]
    using group_generated.opc by blast
qed

lemma cl_group_extensive:
   assumes A0:"A \<subseteq> X" shows "A \<subseteq>cl_group A"
proof
  fix x assume "x \<in> A" then show "x \<in>cl_group A"
  unfolding cl_group_def
  using assms group_generated.iso by auto
qed

lemma cl_group_idempotent:
  assumes A0:"A \<subseteq> X" shows "cl_group A = cl_group (cl_group A)"
  by (simp add: cl_sub cl_subgroup group.cl_group_extensive group.cl_group_ub group_axioms subset_antisym)

lemma cl_group_moore1:
  assumes A0:"A \<subseteq> X" 
  shows "cl_group A = \<Inter>{C. subgroup C X (\<cdot>) e \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    by (metis (no_types, lifting) CollectD Inf_greatest cl_group_ub)
next
  show "?RHS \<subseteq> ?LHS"
    by (simp add: Inter_lower assms cl_group_extensive cl_subgroup)
qed

lemma generate_is_subgroup:  assumes "H \<subseteq> X" shows "subgroup (cl_group H) X f e" using cl_subgroup by simp

lemma subgroup_imp_group:
  "subgroup H X (\<cdot>) e \<Longrightarrow>  group H (\<cdot>) e"
  by (erule subgroup.subgroup_is_group) (rule group_axioms)

lemma subgroup_pow_equality[simp]:
  assumes A0:"subgroup H X f e" and "x \<in> H"
  shows "monoid.pow_int H f e x n= x^n"
  by (smt (verit) A0 group_def assms(2) group.nat_pow_inv group_axioms monoid.pow_int_def subgroup.sub_mem subgroup_imp_group subgroup_inverse_equality)


lemma subgroup_int_pow_closed:
  assumes "subgroup H X (\<cdot>) e" "h \<in> H" shows "h^(k :: int) \<in> H"
  using group.int_pow_closed[OF subgroup_imp_group[OF assms(1)]] assms(2)
  unfolding subgroup_pow_equality[OF assms]
  using \<open>\<And>n::int. monoid.pow_int (H::'a set) (\<cdot>) e (h::'a) n = pow_int h n\<close> by fastforce 


lemma generate_pow:
  assumes "a \<in>X" shows "cl_group {a} = {a^(k :: int) | k. k \<in> UNIV }" (is "?LHS = ?RHS")
proof
  show "?RHS \<subseteq> ?LHS"
  proof
    fix x assume "x \<in> ?RHS"
    then obtain k::"int" where "x = pow_int a k" by blast
    then show "x \<in> ?LHS"
      by (metis IntI assms cl_group_def cl_subgroup group.subgroup_int_pow_closed group_axioms group_generated.iso singletonI)
  qed
next
  show "?LHS \<subseteq> ?RHS"
  proof
    fix h assume "h \<in> cl_group {a}" hence "\<exists>k :: int. h = pow_int a k"
    unfolding cl_group_def
    proof(induction rule: group_generated.induct)
      case idm
      then show ?case  by (metis int_pow_0) 
    next
      case (iso a)
      then show ?case  by (metis IntD2 assms int_pow_1 singletonD) 
    next
      case (inv a)
      then show ?case  by (metis IntD2 assms int_pow_1 int_pow_neg singletonD) 
    next
      case (opc a b)
      then show ?case  by (metis assms int_pow_mult) 
    qed
    then show "h \<in> ?RHS"
      by blast
  qed
qed

lemma generate_id: "cl_group {e} = {e}"by (meson cl_subgroup group.cl_group_ub group.trivial_subgroup subgroup.subset subgroup_def subgroup_imp_group subset_antisym)
lemma generate_empty: "cl_group {} = {e}" by (metis cl_group_iso cl_subgroup empty_subsetI generate_id group.subgroupE1(2) group_axioms subset_singletonD)


definition cyclic_group where "cyclic_group G \<equiv> (\<exists>x \<in> X. cl_group {x} = G)"
lemma cyclic_group_eq: assumes A0:"G \<subseteq> X" shows "cyclic_group G \<longleftrightarrow> (\<exists>g \<in> X. G =  { pow_int g (k :: int) | k. k \<in> UNIV })"   using cyclic_group_def generate_pow by auto
lemma cylic_subgroup_pow:
  assumes A0:"x \<in> X"
  shows "cl_group {x} = cl_group {inv x}"
proof-
  have "cl_group {x} = { pow_int x (k :: int) | k. k \<in> UNIV }" by (simp add: assms generate_pow)
  also have "... = { pow_int x (-(k :: int)) | k. k \<in> UNIV }" by (metis UNIV_I add.inverse_inverse)
  also have "... = {pow_int (inv x) (k :: int)|k. k \<in> UNIV}" using assms int_pow_inv int_pow_neg by presburger
  also have "... = cl_group {inv x}"  using assms generate_pow invertible invertible_inverse_closed by presburger
  finally show ?thesis by auto
qed



end

locale cyclic_group=group G "(\<cdot>)" e for G and f (infixl "\<cdot>" 70) and e+
  assumes cyclic:"\<exists>g \<in> G. cl_group {g} = G"
begin

(*turbo scuffed*)
lemma cyclic_subgroup:
  assumes A0:"cyclic_group G" and A1:"subgroup H G (\<cdot>) e"
  shows "cyclic_group H"
proof-
  obtain g where A2:"g \<in> G" and A3:"G = cl_group {g}" using A0 cyclic_group_def by auto
  have B0:"H \<subseteq> G"  by (simp add: A1 subgroupE1(1)) 
  show ?thesis
  proof(cases "H={e}")
    case True
    then show ?thesis  using generate_id idmem local.cyclic_group_def by auto
  next
    case False
    define M where "M \<equiv> {n::nat. n >0 \<and> monoid.pow_nat f e g n \<in> H}"
    have B0:"M \<noteq> {}"
    proof-
      obtain h where A4:"h \<in> H" and A4b:"h \<noteq> e"  using A1 False subgroup.id_mem by fastforce 
      obtain A5:"inv h \<in> H" and A6:"h \<in> G"   by (meson A1 A4 subgroup.inv_cl subgroup.sub_mem)  
      obtain k::"int" where A7:"h = monoid.pow_int G f e g k"  using A2 A3 A6 generate_pow by fastforce 
      show ?thesis
      proof(cases "k < 0")
        case True
        then have "inv h = monoid.pow_int G f e g (-k)" using A2 A7 int_pow_neg by presburger
        also have "... \<in> H"  using A5 calculation by auto  
        then have "nat (-k) \<in> M" unfolding M_def using True int_pow_def2 by force
        then show ?thesis by auto
      next
        case False
        then obtain A7:"nat k \<in> M" unfolding M_def using A4 A7 int_pow_def2 A4b by force
        then show ?thesis by auto
      qed
    qed
    define n where "n \<equiv> Least (\<lambda>n::nat. n \<in> M)"
    define h where "h \<equiv> pow_nat g n"
    have B3:"h \<in> G"  by (simp add: A2 h_def)  
    have B5:"n > 0" unfolding n_def M_def using B0   by (metis (no_types, lifting) LeastI M_def ex_in_conv mem_Collect_eq) 
    have B1:"h \<in> H" unfolding h_def n_def M_def using B0  by (metis (mono_tags, lifting) Collect_empty_eq LeastI M_def mem_Collect_eq) 
    have B2:"cl_group {h} \<subseteq> H"  by (simp add: A1 B1 cl_group_ub)
    have B4:"H \<subseteq> cl_group {h}"
    proof
      fix x assume A8:"x \<in> H"
      then obtain A9:"x \<in> G"  by (meson A1 subgroup.sub_mem) 
      then obtain k::"int" where A10:"x = pow_int g k"  using A2 A3 generate_pow by fastforce
      show "x \<in> cl_group {h}"
      proof(cases "k > 0")
        case True
        define m where "m \<equiv> nat k"
        define q where "q \<equiv> m div n"
        define r where "r \<equiv> m mod n"
        then obtain B6:"m = n * q + r" and "0 \<le> r" and "r < n"   by (metis (no_types, lifting) B0 CollectD LeastI_ex M_def bot_nat_0.extremum ex_in_conv mod_less_divisor mult_div_mod_eq n_def q_def r_def)
        have "x = pow_int g k"  by (simp add: A10)
        also have "... = pow_nat g m" using True int_pow_def2 m_def by auto
        also have "... = pow_nat g (n * q + r)"  by (simp add: B6)
        also have "... = pow_nat g (n * q) \<cdot> (pow_nat g r)" by (simp add: A2 nat_pow_mult)
        finally have B7:"x = pow_nat (pow_nat g n) q \<cdot> (pow_nat g r)"  using A2 nat_pow_pow by auto
        then obtain B8:"pow_int (pow_nat g n) (-(int q)) \<cdot> x = (pow_nat g r)"  by (metis A2 A9 group.int_pow_neg group_axioms int_pow_closed int_pow_int inv_solve_left)
        then have "inv (pow_nat (pow_nat g n) q) \<cdot> x = (pow_nat g r)"  by (simp add: A2 int_pow_neg_int)
        also have "... \<in> H"  by (metis A1 A8 B1 B8 h_def subgroup.closed subgroup_int_pow_closed)
        then have "r = 0"  by (metis CollectI M_def \<open>\<And>thesis::bool. (\<lbrakk>(m::nat) = (n::nat) * (q::nat) + (r::nat); (0::nat) \<le> r; r < n\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> gr0I n_def not_less_Least)
        then have "n dvd m"  by (simp add: mod_eq_0_iff_dvd r_def)
        then have "x \<in> cl_group {h}"
          by (metis A10 A2 B3 B6 \<open>(r::nat) = (0::nat)\<close> \<open>pow_int (g::'a) (k::int) = pow_nat g (m::nat)\<close> add.right_neutral cl_group_extensive cl_subgroup group.subgroup_int_pow_closed group_axioms h_def insert_subset int_pow_int local.power_mult subgroup.subset trivial_subgroup)
        then show ?thesis by auto
      next
        case False
        have B9:"(-k) \<ge> 0"  using False by auto
        define m where "m \<equiv> nat (-k)"
        define q where "q \<equiv> m div n"
        define r where "r \<equiv> m mod n"
        then obtain B6:"m = n * q + r" and "0 \<le> r" and "r < n"   by (metis (no_types, lifting) B0 CollectD LeastI_ex M_def bot_nat_0.extremum ex_in_conv mod_less_divisor mult_div_mod_eq n_def q_def r_def)
        have "inv x = pow_int g (-k)" using A10 A2 int_pow_neg by presburger
        also have "... = pow_nat g m"   using B9 m_def pow_nat by presburger
        also have "... = pow_nat g (n * q + r)"  by (simp add: B6)
        also have "... = pow_nat g (n * q) \<cdot> (pow_nat g r)" by (simp add: A2 nat_pow_mult)
        finally have B7:"(inv x) = pow_nat (pow_nat g n) q \<cdot> (pow_nat g r)"   using A2 local.power_mult by presburger 
        then obtain B8:"pow_int (pow_nat g n) (-(int q)) \<cdot> (inv x) = (pow_nat g r)"    by (metis A2 closed int_pow_closed int_pow_int int_pow_neg inv_solve_left) 
        then have "inv (pow_nat (pow_nat g n) q) \<cdot> (inv x) = (pow_nat g r)"  by (simp add: A2 int_pow_neg_int)
        also have "... \<in> H"  by (metis A1 A8 B1 B8 group.subgroupE1(3) group_axioms h_def subgroupE1(4) subgroup_int_pow_closed)
        then have "r = 0"  using M_def \<open>\<And>thesis::bool. (\<lbrakk>(m::nat) = (n::nat) * (q::nat) + (r::nat); (0::nat) \<le> r; r < n\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> n_def not_less_Least by auto 
        then have "n dvd m"  by (simp add: mod_eq_0_iff_dvd r_def)
        then have "inv x \<in> cl_group {h}" by (metis B3 B7 \<open>(r::nat) = (0::nat)\<close> cl_group_extensive cl_monoid empty_subsetI h_def insert_subset monoid.pow_closed pow_0 pow_closed rightid)
        then obtain "x \<in> cl_group {h}" using A10 A2 inverse_in_cl by fastforce
        then show ?thesis by auto
      qed
    qed
    then show ?thesis  using B2 B3 local.cyclic_group_def by blast
  qed
qed

end

context group
begin

lemma centralizer_eq:
  assumes A0:"A \<subseteq> X"
  shows "centralizer A = {b \<in> X. \<forall>a \<in> A. b \<cdot> a \<cdot> (inv b) = a}" 
  unfolding centralizer_def commutes_def apply(auto)
  using assms associative rightid apply auto[1]
  by (metis assms closed inv_solve_right2 subset_iff)


end

context group
begin

definition rconj where "rconj g x \<equiv> x \<cdot> g \<cdot> inv x"
definition conjugacy_class where "conjugacy_class g \<equiv> {x \<cdot> g \<cdot> inv x|x. x\<in>X}"

lemma rconj_pow:assumes A0:"g\<in>X" and A1:"x\<in>X" shows "(rconj g x)** n=x \<cdot> g **n \<cdot> inv x"
proof(induct n) 
  case 0 then show ?case
    by (simp add: A1 rightid)
next
  case (Suc n) then show ?case 
    unfolding rconj_def
    by (simp add: A0 A1 associative inv_solve_left2 m_closed)
qed

lemma rconj_pow_int:
  assumes A0:"g\<in>X" and A1:"x\<in>X" 
  shows "(rconj g x)^ n=x \<cdot> g ^n \<cdot> inv x"
proof(cases "n<0")
  case True
  then have "(rconj g x)^n=inv ((rconj g x)**(nat(-n)))" 
    by (meson int_pow_def2) 
  also have "...=inv (x \<cdot> g**(nat(-n)) \<cdot> inv x)" 
    using A0 A1 rconj_pow by presburger
  also have "...= x \<cdot> inv (g**(nat(-n))) \<cdot> inv x"
    by (simp add: A0 A1 associative inv_mult_group m_closed) 
  also have "...=x \<cdot> g^n \<cdot> inv x"
    using True int_pow_def2 by presburger 
  finally show ?thesis  
    by blast 
next
  case False then show ?thesis 
    using A0 A1 int_pow_def2 rconj_pow by presburger 
qed

lemma conj_class_ord_lt: 
  assumes A0:"g\<in>X" and A1:"h\<in>conjugacy_class g" 
  shows "\<And>n. g^n=e \<Longrightarrow> h^n=e" and
        "\<And>n. h^n=e \<Longrightarrow> g^n=e" and      
        "\<And>n. g**n=e \<Longrightarrow> h**n=e" and 
        "\<And>n. h**n=e \<Longrightarrow> g**n=e"
proof- 
  obtain x where A2:"x\<in>X" and A3:"h=x \<cdot> g \<cdot> inv x"
    using A1 conjugacy_class_def by auto
  have B0:"h=rconj g x" 
    by (simp add: A3 rconj_def) 
  show B1:"\<And>n. g^n=e \<Longrightarrow> h^n=e"
    by (simp add: A0 A2 B0 rconj_pow_int rightid) 
  show B2:"\<And>n. h^n=e \<Longrightarrow> g^n=e" 
  proof-   
    fix n assume A4:"h^n=e" then obtain " x \<cdot> g ^n \<cdot> inv x=e"
      by (simp add: A0 A2 B0 rconj_pow_int)  
    then obtain "inv x \<cdot> x \<cdot> g^n \<cdot> inv x \<cdot> x=inv x \<cdot>e \<cdot> x"
      by (metis A0 A2 associative int_pow_closed invertible m_closed monoid.invertible_inverse_closed monoid_axioms)
    then show "g^n=e"
      by (simp add: A0 A2 associative leftid rightid)
  qed 
  show B3:"\<And>n. g**n=e \<Longrightarrow> h**n=e"  
    by (metis B1 int_pow_int)   
  show B4: "\<And>n. h**n=e \<Longrightarrow> g**n=e"
    by (metis B2 int_pow_int) 
qed

lemma conj_class_ord:
  assumes A0:"g\<in>X" and A1:"h\<in>conjugacy_class g" 
  shows "elem_ord g=elem_ord h"
proof-
  have B0:"elem_exponents g \<subseteq> elem_exponents h" 
    unfolding elem_exponents_def   using A0 A1 conj_class_ord_lt(3) by force
  also have B1:"elem_exponents h \<subseteq> elem_exponents g" 
    unfolding elem_exponents_def using A0 A1 conj_class_ord_lt(4) by blast 
  finally show ?thesis 
    using elem_ord_def by auto
qed
(*converse is false viz. abelian groups*)
lemma subgroupI:
  fixes H 
  assumes subset:"H \<subseteq> X" and
          m_closed:"\<And>x y. \<lbrakk>x\<in>H;y\<in>H\<rbrakk> \<Longrightarrow> x\<cdot>y\<in>H" and
          one_closed:"e\<in>H" and
          m_inv_closed:"\<And>x. x \<in> H \<Longrightarrow> monoid.inv X (\<cdot>) e x \<in> H"
  shows "subgroup H X (\<cdot>) e"
  apply(rule subgroup.intro)
  apply (simp add: group_axioms)
  by (simp add: m_closed m_inv_closed one_closed subgroup_axioms_def subset)


lemma top_subgroup:"subgroup X X (\<cdot>) e" using cl_group_extensive generate_is_subgroup subgroupE1(1) by fastforce 

definition elem_commutator ("C'[_,_']")  where "C[a,b] \<equiv> a \<cdot> b \<cdot> inv a \<cdot> inv b"

lemma commutesI1:"\<lbrakk>a\<in>X; b\<in>X; C[a,b]=e\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a" unfolding elem_commutator_def  by (metis (full_types) double_inv inv_solve_right1 l_inv_ex local.inv_equality m_closed) 
lemma commutesI2:"\<lbrakk>a\<in>X; b\<in>X; e=C[a,b]\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a" by (metis commutesI1) 
lemma commutesD1:"\<lbrakk>a\<in>X; b\<in>X; a\<cdot>b=b\<cdot>a\<rbrakk> \<Longrightarrow>C[a,b]=e" unfolding elem_commutator_def  by (metis inv_solve_right1 m_closed r_inv_simp) 
lemma commutesD2:"\<lbrakk>a\<in>X; b\<in>X; a\<cdot>b=b\<cdot>a\<rbrakk> \<Longrightarrow>e=C[a,b]" unfolding elem_commutator_def  using commutesD1 elem_commutator_def by force 
lemma commutes_iff1:"\<lbrakk>a\<in>X; b\<in>X\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a \<longleftrightarrow> C[a,b]=e"  using commutesD1 commutesI1 by blast
lemma commutes_iff2:"\<lbrakk>a\<in>X; b\<in>X\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a \<longleftrightarrow> e=C[a,b]"  using commutesD2 commutesI2 by blast
lemma commutes_inv:"\<lbrakk>a\<in>X; b\<in>X\<rbrakk> \<Longrightarrow> C[b,a]=inv C[a,b]" unfolding elem_commutator_def  by (simp add: associative group.inv_mult_group group_axioms m_closed) 


definition derived where "derived A \<equiv> cl_group  {C[a,b]|a b. a\<in>A \<and> b\<in>A}"


lemma commutators_sub: 
  assumes "K \<subseteq> H" "subgroup H X (\<cdot>) e" 
  shows "{C[a,b]|a b. a\<in>K \<and> b\<in>K} \<subseteq> H"  
  unfolding elem_commutator_def using assms subgroupE1 by (auto simp add: subset_iff)

lemma derived_sub: 
  assumes "K \<subseteq> H" "subgroup H X (\<cdot>) e" 
  shows "derived K \<subseteq> H" 
  unfolding derived_def by(rule cl_group_ub, auto simp add: assms commutators_sub)

lemma commutators_sub3: "H \<subseteq> X \<Longrightarrow> {C[a,b]|a b. a\<in>H \<and> b\<in>H} \<subseteq> X"  unfolding elem_commutator_def by(auto simp add:m_closed subset_iff)
lemma derived_sub3:"H \<subseteq> X \<Longrightarrow> derived H \<subseteq> X" by (simp add: derived_sub top_subgroup)  

lemma exp_of_derived_sub: assumes "H \<subseteq> X" shows "(derived ^^ n) H \<subseteq> X" using assms derived_sub3 by (induct n) (auto)
lemma derived_is_subgroup:"H \<subseteq> X \<Longrightarrow> subgroup (derived H) X (\<cdot>) e"  unfolding derived_def  by (simp add: cl_subgroup) 


end

context group_homomorphism
begin
lemma id_to_id:"f e = d"
  using map_id by auto 

lemma inv_to_inv:
  assumes A0:"g \<in> X"
  shows "f (dom.inv g) = cod.inv (f g)"
  by (simp add: assms map_inv) 

lemma pos_pow_to_pow:
  assumes A0:"g \<in> X"
  shows " f (dom.pow_int g (int n)) = cod.pow_int (f g) (int n)"
proof(induct n)
  case 0
  then show ?case
    by (simp add: id_to_id) 
next
  case (Suc n)
  then show ?case
    by (metis assms cod.int_pow_int dom.int_pow_int group_homomorphism.map_ord1 group_homomorphism_axioms)
qed

lemma pow_to_pow:
  assumes A0:"g \<in> X"
  shows " f (dom.pow_int g  n) = cod.pow_int (f g)  n"
proof(induct n)
  case (nonneg n)
  then show ?case
    using assms pos_pow_to_pow by blast 
next
  case (neg n)
  then show ?case
  proof-
    have "f (dom.pow_int g (- int (Suc n))) = f (dom.inv (dom.pow_int g (int (Suc n))))"
      using assms dom.int_pow_neg by presburger
    also have "... = cod.inv (f (dom.pow_int g (int (Suc n))))"
      using assms inv_to_inv by blast
    also have "... =   cod.inv (cod.pow_int (f g) (int (Suc n)))"
      using assms pos_pow_to_pow by presburger
    also have "... =  cod.pow_int (f g) (- int (Suc n))"
      using assms cod cod.int_pow_neg by presburger
    finally show ?thesis 
      by auto
  qed
qed

lemma kernel_conj_closed:
  assumes A0:"g \<in> X" and A1:"h \<in> Ker"
  shows "g \<cdot> h \<cdot> dom.inv g \<in> Ker"
proof-
  obtain B0:"f h = d"  
    by (simp add: A1 Ker_image) 
  have "f (g \<cdot> h \<cdot> dom.inv g) = (f g) \<star> (f h) \<star> (f (dom.inv g))"
    by (simp add: A0 A1 cmp dom.m_closed)
  also have "... = (f g) \<star> d \<star> (cod.inv (f g))"
    using A0 B0 inv_to_inv by presburger
  also have "... = d"
    by (simp add: A0 cod.rightid)
  finally show ?thesis
    using A0 A1 conj_closed by blast
qed
end


context group
begin


lemma subgroup_units:
  assumes A0:"subgroup H X (\<cdot>) e" 
  shows "H \<subseteq> Units"
  by (meson assms invertible mem_UnitsI subgroup.sub_mem subsetI)

lemma subgroup_inv_eq:
  assumes A0:"subgroup H X (\<cdot>) e" and A1:"x \<in> H"
  shows "monoid.inv H (\<cdot>) e x = inv x"
  by (simp add: A0 A1)


end

lemma quotient_groups_theorem1:
  fixes G::"'a set" and law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::"'a" and R::"'a rel"
  assumes A0:"group G (\<cdot>) e" and A1:"equivalence_relation G R" and A2:"l_cong G (\<cdot>) R"
  defines "p \<equiv> equivalence_relation.p G R" 
  defines "H \<equiv> p e"
  shows "subgroup H G (\<cdot>) e" and 
        "\<And>x y. (x,y) \<in> R \<Longrightarrow> (monoid.inv G (\<cdot>) e x) \<cdot> y \<in> H" and
        "\<And>x y. \<lbrakk>x \<in> G; y \<in>G; (monoid.inv G (\<cdot>) e x) \<cdot> y \<in> H\<rbrakk> \<Longrightarrow> (x,y) \<in> R"
proof-
  obtain B0:"H \<subseteq> G" and B1:"H \<noteq> {}"
    by (metis A0 A1 H_def p_def bex_empty equivalence_relation.p_closed2 equivalence_relation.p_self group.top_subgroup subgroup.id_mem)
  have B2:"\<And>a. a \<in> H \<Longrightarrow> (e, a) \<in> R"
    by (metis A0 A1 Algebrah8.group_def H_def p_def equivalence_relation.p_D1 monoid.idmem)
  have B3:"\<And>x y. (x,y) \<in> R \<Longrightarrow> (monoid.inv G (\<cdot>) e x) \<cdot> y \<in> H"
  proof-
    fix a b assume arb:"(a,b)\<in>R"
    then obtain a2:"a \<in> G" and b2:"b \<in> G"
      by (meson A1 equivalence_relation.l_closed equivalence_relation.r_closed)
    have a3:"monoid.inv G (\<cdot>) e a \<in> G"
      by (simp add: A0 a2 group.top_subgroup subgroup.inv_cl)
    then have "(monoid.inv G (\<cdot>) e a \<cdot> a, monoid.inv G (\<cdot>) e a \<cdot> b) \<in> R"
      by (meson A2 arb l_congD1)
    then have "(e, monoid.inv G (\<cdot>) e a \<cdot> b) \<in> R"
      by (simp add: A0 a2 group.l_inv_simp)
    then show " monoid.inv G (\<cdot>) e a \<cdot> b \<in> H"
      by (simp add: A1 H_def equivalence_relation.p_I1 p_def)
  qed
  have B4:"\<And>a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> monoid.inv G (\<cdot>) e a \<cdot> b \<in> H"
  proof-
    fix a b assume a1:"a \<in> H" and b1:"b \<in> H"
    then obtain arb:"(a,b)\<in>R" and a2:"a \<in> G" and b2:"b \<in> G"
      by (metis A1 B0 B2 H_def equivalence_relation.p_D1 equivalence_relation.p_eq1 in_mono p_def)
    then show " monoid.inv G (\<cdot>) e a \<cdot> b \<in> H"
      by (simp add: B3)
  qed
  show "subgroup H G (\<cdot>) e"
    by(auto intro!: A0 subgroupI3 B0 B1 B4)
  show "\<And>x y. (x,y) \<in> R \<Longrightarrow> (monoid.inv G (\<cdot>) e x) \<cdot> y \<in> H"
    using B3 by auto
  show "\<And>x y. \<lbrakk>x \<in> G; y \<in>G; (monoid.inv G (\<cdot>) e x) \<cdot> y \<in> H\<rbrakk> \<Longrightarrow> (x,y) \<in> R"
    using A0 A2 group.axioms(1) B2 group.invertible group.l_inv_simp l_congD1 monoid.inv_right_cancel by fastforce
qed


lemma quotient_groups_theorem2:
  fixes G::"'a set" and law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::"'a" and H::"'a set"
  assumes A0:"group G (\<cdot>) e" and A1:"subgroup H G (\<cdot>) e"
  defines "R \<equiv> {(x, y) \<in> G\<times>G. monoid.inv G (\<cdot>) e x \<cdot> y \<in> H}"
  shows "equivalence_relation G R" and "l_cong G (\<cdot>) R"
proof-
  let ?inv="monoid.inv G (\<cdot>) e"
  show "equivalence_relation G R"
    unfolding R_def
    apply(unfold_locales)
    apply blast
    using A0 A1 group.l_inv_simp subgroup.id_mem apply fastforce
    using A1 subgroup.l_coset_equivs(2) apply fastforce
    using A1 subgroup.l_sub_eq_def[of H G law e] subgroup.l_sub_eq_trans[of H G law e] by(auto simp add:trans_def)
  show "l_cong G (\<cdot>) R"
  proof(rule l_congI1)
    fix z x y assume z0:"z \<in> G" and xy0:"(x,y) \<in> R" 
    then obtain x0:"x \<in> G" and y0:"y \<in> G" and xy1:"?inv x \<cdot> y \<in> H" and zx0:"z \<cdot> x \<in> G" and zy0:"z \<cdot> y \<in> G"
      using R_def using A0 group_def monoid.m_closed by fastforce
    then obtain "?inv x \<cdot> y = ?inv (z \<cdot> x) \<cdot> (z \<cdot> y)"
      by (simp add: A0 group.axioms(1) group.inv_mult_group group.invertible group.remove_id1 monoid.invertible_inverse_closed z0)
    then show "(z \<cdot> x, z \<cdot> y)\<in>R"
      unfolding R_def using zx0 zy0 xy1 by force
  qed
qed
   
context subgroup
begin

definition subgroup_eqr ("R") where "subgroup_eqr \<equiv> {(x, y) \<in> G\<times>G. inv x \<cdot> y \<in> H}"

lemma subgroup_eqr_is_eqr:"equivalence_relation G R" using equivalence_relation_def l_sub_eqr subgroup.l_sub_eq_def subgroup_eqr_def subgroup_is_subgroup1 by fastforce 
lemma subgroup_eqr_is_cong: "l_cong G (\<cdot>) R"  using group_axioms quotient_groups_theorem2(2) subgroup_eqr_def subgroup_is_subgroup1 by fastforce 
lemma subgroup_eqrI1:"\<lbrakk>x \<in> G;y \<in> G; h \<in> H; inv x \<cdot> y \<in> H\<rbrakk> \<Longrightarrow> (x, y) \<in>R" by(simp add: subgroup_eqr_def)
lemma subgroup_eqrD1:"(x, y) \<in>R \<Longrightarrow> x \<in> G \<and> y \<in> G" by(simp add: subgroup_eqr_def)
lemma subgroup_eqrD2:"(x, y) \<in>R \<Longrightarrow>  inv x \<cdot> y \<in> H" by(simp add: subgroup_eqr_def)
lemma subgroup_eqrD3:"(x, y) \<in>R \<Longrightarrow>  z \<in> G \<Longrightarrow> (z \<cdot> x, z \<cdot> y)\<in>R" 
proof-
  fix z x y assume z0:"z \<in> G" and xy0:"(x,y) \<in> R" 
  then obtain x0:"x \<in> G" and y0:"y \<in> G" and xy1:"inv x \<cdot> y \<in> H" and zx0:"z \<cdot> x \<in> G" and zy0:"z \<cdot> y \<in> G"
    using m_closed subgroup_eqrD1 subgroup_eqrD2 by presburger
  then obtain "inv x \<cdot> y = inv (z \<cdot> x) \<cdot> (z \<cdot> y)"
    by (simp add: inv_mult_group remove_id1 z0)
  then show "(z \<cdot> x, z \<cdot> y)\<in>R"
    unfolding subgroup_eqr_def using zx0 zy0 xy1 by force
qed

lemma subgroup_eqrD4:"x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> (x,y) \<in>R \<Longrightarrow> y \<in> l_coset x H" using lcoset_mem subgroup_eqrD2 by auto
lemma subgroup_eqrI2:"x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow>  y \<in> l_coset x H \<Longrightarrow> (x,y) \<in>R "  by (metis lcoset_mem subgroup_eqrI1) 
lemma subgroup_eqr_iff:"x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow>  y \<in> l_coset x H \<longleftrightarrow> (x,y) \<in>R "  using subgroup_eqrD4 subgroup_eqrI2 by blast


end



end

