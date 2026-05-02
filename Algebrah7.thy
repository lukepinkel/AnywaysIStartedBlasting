theory Algebrah7
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


lemma rinv_into_f: "f`A = B \<Longrightarrow> y \<in> f`A \<Longrightarrow> f (rinv f A B y) = y"  by (simp add: rinv_def) (fast intro: someI2)
lemma rinv_inv: "f ` A = B \<Longrightarrow> compose B f (rinv f A B) = Id B" unfolding compose_def Id_def using restrict_ext[of B] rinv_into_f[of f A B]  by auto
lemma rinv_restrict:"f`A = B \<Longrightarrow> restrict (rinv f A B) B = rinv f A B"  by (simp add: rinv_def)
lemma rinv_is_rinv:"f ` A = B \<Longrightarrow> is_right_inv B f (rinv f A B)"  by (simp add: is_right_inv_def rinv_inv)
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


lemma is_left_invI1[intro]:"(\<And>x. x \<in> X \<Longrightarrow> r (f x) = x) \<Longrightarrow> is_left_inv X f r" unfolding is_left_inv_def compose_def by auto
lemma is_left_invI2[intro]:"(\<And>x. x \<in> X \<Longrightarrow> x = r (f x)) \<Longrightarrow> is_left_inv X f r"   by (simp add: is_left_invI1)
lemma is_left_invE1:"is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> r (f x) = x"   by (metis compose_eq id1 is_left_inv_def) 
lemma is_left_invE2:"is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> x = r (f x)"   by (simp add: is_left_invE1) 
lemma is_left_inv_id:"is_left_inv X f r \<Longrightarrow> compose X r f = Id X"  using maps_on_equalityI[of "compose X r f" X "Id X"]  by (simp add: Id_def compose_eq is_left_invE1)
lemma linv_cancel:"is_left_inv X f r \<Longrightarrow> x1 \<in>X \<Longrightarrow>  x2 \<in> X \<Longrightarrow> f x1 = f x2 \<Longrightarrow> x1 =x2"  by (metis (no_types) is_left_invE1)
lemma ex_linv_implies_inj:"\<exists>s. is_left_inv X f r \<Longrightarrow> inj_on f X" by (simp add: inj_on_def linv_cancel)
lemma is_linv_implies_inj:"is_left_inv X f r \<Longrightarrow> inj_on f X"by (simp add: inj_on_def linv_cancel)
lemma inj_implies_ex_linv:"inj_on f X \<Longrightarrow> \<exists>r. is_left_inv X f r" unfolding is_left_inv_def  by (metis is_left_invI1 is_left_inv_id the_inv_into_f_f)


lemma left_inv_target: "is_left_inv X f r \<Longrightarrow> r`(f`X) = X "  unfolding is_left_inv_def  by (metis image_ident image_restrict_eq surj_compose)
lemma right_inv_target: "is_right_inv Y f s \<Longrightarrow> f`(s`Y) = Y"  unfolding is_right_inv_def by (metis image_ident image_restrict_eq surj_compose)
lemma rinv_l: "is_left_inv X f r \<Longrightarrow> is_right_inv X r f"  by (simp add: is_left_inv_id is_right_inv_def)
lemma linv_r:"is_right_inv (Y::'b set) f s \<Longrightarrow> is_left_inv Y s f"  by (simp add: is_left_inv_def is_right_inv_def) 
lemma rinv_surj:"is_left_inv X f r \<Longrightarrow> surj r (f`X) X" using ex_rinv_imp_surj rinv_l  by (simp add: surj_def left_inv_target) 
lemma linv_inj: "is_right_inv (Y::'b set) f s \<Longrightarrow> inj_on s Y"  using is_linv_implies_inj linv_r by blast

lemma bij_betw_rinv: "bij_betw f A B \<Longrightarrow> y \<in> B \<Longrightarrow> f (rinv f A B y) = y"  by (simp add: bij_betw_imp_surj_on rinv_into_f)

lemma bij_betw_linv: "bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow> (rinv f A B) (f x)= x" by(simp add:  bij_betw_def,force)



locale set_morphism=
  fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"
  assumes dom[intro]:"x \<notin> A \<longrightarrow> f x = undefined" and  
          cod[intro,simp]:"x \<in> A \<Longrightarrow> f x \<in> B"
begin
lemma mem_maps_to:"f \<in> maps_to A B" by (simp add: maps_to_memI)
lemma mem_maps_on:"f \<in> maps_on A" by (simp add: dom maps_on_memI) 
lemma mem_hom:"f \<in> hom A B" by (simp add: hom_memI2 mem_maps_on mem_maps_to)
end
locale sur_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes sur[intro]:"f `A = B"
locale inj_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes inj[intro, simp]:"inj_on f A"
locale iso_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" assumes iso[intro, simp]:"bij_betw f A B"
locale set_epimorphism =set_morphism + sur_locale
locale set_monomorphism=set_morphism + inj_locale
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
  assume A0:"bij_betw f A B"
  then have "?INV ?inv"
    by (metis (mono_tags, lifting) bij_betw_linv bij_betw_rinv compose_def restrict_ext) 
  also have "?inv \<in> hom B A"
    by (metis (mono_tags, lifting) A0 bij_betw_imp_surj_on hom_memI2 restrict_maps_on rinv_def rinv_map_to) 
  then show "\<exists>g \<in> hom B A. ?INV g"  using calculation by auto
next
  assume "\<exists>g \<in> hom B A. ?INV g"
  then obtain g where "f \<in> maps_to A B" "g \<in> maps_to B A" and "\<And>x. x\<in>A\<Longrightarrow>g(f x) = x" and "\<And>y. y\<in>B \<Longrightarrow> f(g y) = y" 
    by (metis mem_maps_to compose_eq hom_memD2 id1)
  then show "bij_betw f A B" by (rule bijI) 
qed
end

locale set_partition=
  fixes X::"'a set" and P::"'a set set"
  assumes subset: "P \<subseteq> Pow X" and 
          nenm:"{} \<notin> P" and 
          uneq:"\<Union>P = X" and
          disj:"\<lbrakk>A \<in> P; B \<in> P; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"

locale equivalence_relation=
  fixes X :: "'a set" and R :: "('a \<times> 'a) set"
  assumes sub[intro, simp]:"R \<subseteq> X \<times> X" and
          ref[intro, simp]: "a \<in> X \<Longrightarrow> (a, a) \<in> R" and 
          sym[sym]: "(a, b) \<in> R \<Longrightarrow> (b, a) \<in> R" and
          trn[trans]: "\<lbrakk>(a, b) \<in> R; (b, c) \<in> R \<rbrakk> \<Longrightarrow> (a, c) \<in> R"
begin
lemma l_closed[intro]:"(a, b) \<in> R \<Longrightarrow> a \<in> X"using sub by blast
lemma r_closed[intro]:"(a, b) \<in> R \<Longrightarrow> b \<in> X"using sub by blast
(*definition "p \<equiv> (\<lambda>x \<in> X. THE t. t \<in> (X/R) \<and>  x \<in> t)" *)
definition "p \<equiv> (\<lambda>x \<in> X. {y \<in> X. (x, y) \<in> R})"
definition "P \<equiv> p`X"
lemma p_def2:"p = (\<lambda>x \<in> X. R``{x})" using p_def by fastforce
lemma p_closed1[dest]:"x \<in> X \<Longrightarrow> y \<in> p x \<Longrightarrow> y \<in> X" unfolding p_def by auto
lemma p_closed2[intro, simp]:"a \<in> X \<Longrightarrow> p a \<subseteq> X" unfolding p_def by auto
lemma p_undefined [intro, simp]: "a \<notin> X \<Longrightarrow> p a = undefined" unfolding p_def by simp
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

definition "p_alt \<equiv> (\<lambda>x \<in> X. THE t. t \<in> (X/R) \<and>  x \<in> t)"

lemma p1_closed[intro,simp]:
  assumes[intro]:"x \<in> X" shows "p_alt x \<in> (X/R)"
proof-
  obtain t where "x \<in> t" "t \<in> (X/R)"
    using elem_ex5 by blast
  then show ?thesis
    apply (auto simp: p_alt_def)
    apply (rule theI2)
      apply (auto dest: elem_un2)
    done
qed

lemma p1_und[intro,simp]:"x \<notin> X \<Longrightarrow> p_alt x = undefined" unfolding p_alt_def by simp

lemma p1_ide:
  assumes A0:"t \<in> (X/R)" and A1:"x \<in> t" 
  shows "p_alt x = t"
proof-
  obtain "x \<in> X"
    using A0 A1 by auto
  then have "p_alt x = (\<lambda>x. (THE t::'a set. t \<in> X / R \<and> x \<in> t)) x"
    unfolding p_alt_def using restrict_apply1[of x X] by auto
  also have "... = t"
    apply(rule the_equality)
    apply (simp add: A0 A1)
    using A0 A1 elem_un2 by blast
  then show ?thesis
    by (simp add: calculation)
qed


lemma p_def3:"p = p_alt"
proof
  fix x show "p x = p_alt x" 
  proof(cases "x \<in> X")
    case True
    then show ?thesis  using p1_ide by blast
  next
    case False
    then show ?thesis
      by simp 
  qed
qed

lemma q_partition1:"set_partition X P"  unfolding P_def
  apply(rule set_partition.intro)
  apply blast
  using elem_ex5 apply blast
  apply blast
  by (simp add: elem_ex2 elem_un1)


lemma q_partition2:"set_partition X (X/R)" using elem_ex2 local.P_def q_partition1 by auto
lemma proj_epi:"set_epimorphism p X (X/R)"  by (simp add: elem_ex2 set_epimorphism_def set_morphism_def sur_locale.intro)

end

context set_partition
begin

definition "R = {(a, b) \<in> X \<times> X . \<exists>t \<in> P. a \<in> t \<and> b \<in> t}"
lemma pt_ex:"a \<in> X \<Longrightarrow> \<exists>t. a \<in> t \<and> t \<in> P" using uneq by auto
lemma pt_un:"\<lbrakk>t\<in>P;s\<in>P;x\<in>t;x\<in>s \<rbrakk>\<Longrightarrow> t = s" using disj by blast
lemma pt_cl[intro]: "\<lbrakk>t\<in>P; x\<in>t \<rbrakk> \<Longrightarrow> x \<in> X" using uneq by blast
lemma elem_ex:"t\<in>P \<Longrightarrow> \<exists>x \<in> X. x \<in> t" by (metis pt_cl ex_in_conv nenm)

definition "p = (\<lambda>x\<in>X. THE t. t\<in>P \<and> x \<in> t)"
lemma p_cl[intro, simp]:assumes [intro]:"x \<in> X" shows "p x \<in> P"
proof-
  obtain t where "x \<in> t" "t \<in> P"
    using pt_ex by blast
  then show ?thesis
    apply (auto simp: p_def)
    apply (rule theI2)
      apply (auto dest: pt_un)
    done
qed
  
lemma p3_und[intro, simp]:"a \<notin> X \<Longrightarrow> p a = undefined"  unfolding p_def by simp
lemma p3_ide: "\<lbrakk>t \<in> P; x \<in> t \<rbrakk> \<Longrightarrow> p x = t"
  apply (simp add: p_def pt_cl)
  apply (rule the_equality)
   apply (auto dest: pt_un)
  done

lemma eqr_is_eqr:"equivalence_relation X R"
  unfolding R_def
  apply(unfold_locales)
  apply blast
  using uneq apply blast
  apply blast
  using disj by auto


interpretation equivalence:equivalence_relation X R by (simp add: eqr_is_eqr)


lemma p_eq1:assumes A0:"x \<in> X" shows "equivalence.p x = p x"
proof-
  obtain t where block: "t \<in> P \<and> x \<in> t" 
    using A0 pt_ex by blast
  show ?thesis
    apply (simp add: p_def equivalence.p_def)
    apply (rule theI2)
      apply (rule block)
     apply (metis block pt_un)
    apply (auto dest: pt_un simp: R_def)
    done
qed

lemma p_eq2:"equivalence.p = p"  using equivalence.p_def2 p_def p_eq1 by fastforce
lemma qoutient_eq_pt:"equivalence.P= P" by (auto simp add: equivalence.P_def p_eq2 image_iff) (metis elem_ex p3_ide)

end

context equivalence_relation
begin
interpretation partition:set_partition X P by (simp add: elem_ex2 q_partition1)
lemma p_eq3:assumes A0:"x \<in> X" shows "partition.p x = p x"  using P_def assms partition.p3_ide by auto
lemma p_eq4:"partition.p = p"  using p_def2 p_eq3 partition.p_def by fastforce 
lemma eqr_eq:"partition.R = R"  unfolding partition.R_def unfolding P_def by(auto) (metis p1_ide p_D1 p_def3 p_in_quotient1)

end

sublocale set_partition \<subseteq> eqr:equivalence_relation X R
  rewrites "equivalence_relation.P X R = P" and "equivalence_relation.p X R = p"
  apply (simp add: eqr_is_eqr)
  apply (simp add: qoutient_eq_pt)
  by (simp add: p_eq2)

sublocale equivalence_relation \<subseteq> prt:set_partition X P
 rewrites "set_partition.R X P = R" and "set_partition.p X P = p"
  apply (simp add: q_partition1)
  apply (simp add: eqr_eq)
  by (simp add: p_eq4)

context equivalence_relation
begin
lemma rep_ex[dest]:"t \<in> X/R \<Longrightarrow> \<exists>x \<in> X. x \<in> t \<and> p x = t"  using elem_ex4 by blast
lemma projE:"t \<in> X/R \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> Q (p x)) \<Longrightarrow> Q t"  by blast
end

sublocale equivalence_relation \<subseteq> canonical_map:set_epimorphism p X "X/R"  by (simp add: elem_ex2 set_epimorphism_def set_morphism.intro sur_locale.intro)

locale kernel_pair_notation=fixes X::"'a set"
begin
definition kernel_pair_object ("Ker'(_')") where "kernel_pair_object f \<equiv> {(x, y). x \<in> X \<and> y \<in> X \<and> f x = f y} "
end

locale kernel_pair=set_morphism f X Y for f and X and Y
begin
sublocale kernel_pair_notation  X.
sublocale equivalence_relation where X=X and R="Ker(f)" unfolding kernel_pair_object_def by(unfold_locales;auto)
definition "h \<equiv> (\<lambda>t \<in> X/Ker(f). THE y. \<exists>x \<in> t. y = f x)"
lemma h_eq:"\<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> p x = p y \<longleftrightarrow> f x = f y"  unfolding p_equivalence unfolding kernel_pair_object_def by simp
lemma induced_simp [simp]:assumes [intro, simp]:"x \<in> X" shows "h (p x) = f x"
proof -
  have "(THE y. \<exists>z\<in>p x. y = f z) = f x"
    apply (rule the_equality)
    apply(auto simp: h_eq[symmetric] prt.pt_cl prt.p3_ide)
    by (meson assms h_eq p_closed1 prt.p3_ide prt.p_cl) 
  then show ?thesis unfolding h_def by simp
qed

interpretation quotient_map: set_morphism h "X/Ker(f)" Y
proof(unfold_locales, rule)
  fix t
  assume t0:"t \<in> X/Ker(f)"
  obtain x where a: "x \<in> X" "x\<in>t"  using elem_ex5 t0 by blast 
  have "(THE y. \<exists>x\<in>t. y = f x) \<in> Y"
    apply (rule theI2)
    using a t0 apply(auto)
    by (metis P_def elem_ex2 h_eq p_mem_closed prt.p3_ide)
  then show "h t \<in> Y" unfolding h_def using t0 by simp
qed (simp add: h_def)

sublocale quotient_map: set_monomorphism h "X/Ker(f)" Y
proof
  show "inj_on h (X / Ker(f))" unfolding inj_on_def  by (metis h_eq induced_simp rep_ex)
qed

lemma factorization1:"x\<in>X \<Longrightarrow> compose X h p a = f a" by (simp add: compose_def dom)
lemma factorization2[simp]:"compose X h p = f"  by (rule ext) (simp add: compose_def dom)
lemma factorization3:
  assumes A0:"g \<in> hom (X/Ker(f)) Y"  and A1:"compose X g p = f"
  shows "g = h" 
proof
  fix t
  show "g t = h t"
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

  qed (simp add: h_def hom10[OF A0])
qed


end

print_locale! set_partition


end