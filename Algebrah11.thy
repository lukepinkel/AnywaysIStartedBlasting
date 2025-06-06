theory Algebrah11
  imports Main
begin

declare [[show_consts, show_results, show_types]]
declare [[show_abbrevs=true, trace_locales=true]]
print_options
hide_const map dom
hide_const partition
hide_const monoid
hide_const group
hide_const inverse
no_notation power (infixr "^" 80)
hide_const power
no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)

section \<open>Set Morphisms\<close>
definition Pi::"'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "Pi A B = {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B x}"

definition maps_to::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  
  where "maps_to A B \<equiv> {f. (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)}"

definition maps_on::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "maps_on A \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined)}"

definition set_morphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "set_morphisms A B \<equiv> {f. ((\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B))}"

definition surjectives::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "surjectives A B \<equiv> {f. f`A = B}"

definition injectives::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "injectives A \<equiv> {f. inj_on f A}"

definition bijectives::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "bijectives A B \<equiv> {f. bij_betw f A B}"

definition set_epimorphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set "
  where "set_epimorphisms A B \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B) \<and> f`A = B}"

definition set_monomorphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "set_monomorphisms A B \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B) \<and> (\<forall>x1 \<in> A. \<forall>x2 \<in> A. f x1 = f x2 \<longrightarrow> x1 = x2)}"

definition set_isomorphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  
  where "set_isomorphisms A B \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B) \<and> (\<forall>x1 \<in> A. \<forall>x2 \<in> A. f x1 = f x2 \<longrightarrow> x1 = x2) \<and> (f`A=B)}"

definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b" where
  "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"

syntax "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
translations "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"

definition compose::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where
 "compose A g f = (\<lambda>x\<in>A. g (f x))"

abbreviation Id where "Id X \<equiv> (\<lambda>x \<in> X. x)"

definition surj::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set   \<Rightarrow> 'b set \<Rightarrow> bool" 
  where"surj f X Y \<equiv> f`X=Y"

definition rinv::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'a"
  where"rinv f X Y \<equiv> (\<lambda>y \<in> Y. SOME x.  x \<in> X \<and> f x = y)"

definition is_right_inv::"'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" 
  where "is_right_inv Y f s \<equiv> compose Y f s = Id Y"

definition is_left_inv ::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" 
  where "is_left_inv X f r \<equiv> compose X r f = Id X"

definition is_eqrel::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" 
  where "is_eqrel X R \<equiv> refl_on X R \<and> sym R \<and> trans R"

definition quotient::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set" (infixl "'/" 75) 
  where "quotient X R \<equiv> (\<Union>x \<in> X. {R``{x}})"

definition eqr_comp::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  where "eqr_comp X R f \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. (x, y) \<in> R \<longrightarrow> f x = f y)"

definition ker_pair::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set" 
  where "ker_pair X f \<equiv> {(x, y) \<in> X \<times> X. f x = f y}"

definition qproj::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "qproj X R  \<equiv> (\<lambda>x \<in> X. {y \<in> X. (x, y) \<in> R})"

definition qsect::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a" 
  where "qsect X R  \<equiv> rinv (qproj X R) X (X/R)"

definition qmap::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "qmap X R f \<equiv> compose (X/R) f (qsect X R)"


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

lemma maps_to_comp: "f \<in> maps_to A B \<Longrightarrow> g \<in> maps_to B C \<Longrightarrow> compose A g f \<in> maps_to A C"
  by (simp add: maps_to_def compose_def restrict_def)

lemma compose_assoc:"f \<in> maps_to A B \<Longrightarrow>compose A h (compose A g f) = compose A (compose B h g) f 
"by (simp add: fun_eq_iff maps_to_def compose_def restrict_def)

lemma compose_eq: "x \<in> A \<Longrightarrow> compose A g f x = g (f x)" by (simp add: compose_def restrict_def)

lemma surj_compose: "f ` A = B \<Longrightarrow> g ` B = C \<Longrightarrow> compose A g f ` A = C" 
  by (auto simp add: image_def compose_eq)

lemma restrict_cong: "I = J \<Longrightarrow> (\<And>i. i \<in> J =simp=> f i = g i) \<Longrightarrow> restrict f I = restrict g J" 
  by (auto simp: restrict_def fun_eq_iff simp_implies_def)

lemma restrictI1[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> Pi A B"
  by (simp add: Pi_def restrict_def)

lemma restrictI2[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> maps_to A B" 
  by (simp add: maps_to_def restrict_def)

lemma restrict_apply[simp]: "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"
  by (simp add: restrict_def)

lemma restrict_apply1: "x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x" 
  by simp

lemma restrict_ext: "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
  by (simp add: fun_eq_iff maps_to_def restrict_def)

lemma restrict_UNIV: "restrict f UNIV = f"
  by (simp add: restrict_def)

lemma inj_on_restrict_eq [simp]: "inj_on (restrict f A) A \<longleftrightarrow> inj_on f A" 
  by (simp add: inj_on_def restrict_def)

lemma inj_on_restrict_iff: "A \<subseteq> B \<Longrightarrow> inj_on (restrict f B) A \<longleftrightarrow> inj_on f A" 
  by (metis inj_on_cong restrict_def subset_iff)

lemma id_compose1: "f \<in> maps_to A B \<Longrightarrow> f \<in> maps_on A \<Longrightarrow> compose A (Id B) f = f" 
  by (auto simp add: fun_eq_iff compose_def maps_on_def maps_to_def)

lemma id_compose2: 
  "f \<in> maps_to A B \<Longrightarrow> f \<in> maps_on A \<Longrightarrow> compose A f (Id A) = f"
  by (auto simp add: fun_eq_iff compose_def maps_on_def maps_to_def)

lemma image_restrict_eq [simp]: 
  "(restrict f A) ` A = f ` A" 
  by (auto simp add: restrict_def)

lemma restrict_restrict[simp]: 
  "restrict (restrict f A) B = restrict f (A \<inter> B)"  
  unfolding restrict_def by (simp add: fun_eq_iff)

lemma bijI:"f \<in> maps_to A B \<Longrightarrow> g \<in> maps_to B A \<Longrightarrow> 
            (\<And>x. x\<in>A \<Longrightarrow> g (f x) = x) \<Longrightarrow> (\<And>y. y\<in>B \<Longrightarrow> f (g y) = y) \<Longrightarrow> bij_betw f A B" 
  by (metis bij_betw_byWitness maps_to_im)

lemma bijD1: "bij_betw f A B \<Longrightarrow> f \<in> maps_to A B" 
  by (auto simp add: bij_betw_def)

lemma inj_compose:"bij_betw f A B \<Longrightarrow> inj_on g B \<Longrightarrow> inj_on (compose A g f) A"
  by (auto simp add: bij_betw_def inj_on_def compose_eq)

lemma bij_compose:"bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (compose A g f) A C" 
  by (simp add: inj_compose bij_betw_def surj_compose)

lemma bij_restrict_eq [simp]: "bij_betw (restrict f A) A B = bij_betw f A B"
  by (simp add: bij_betw_def)

lemma im_restrict_sub:"A \<subseteq> X \<Longrightarrow> f`A \<subseteq> A \<Longrightarrow> g`A \<subseteq> A \<Longrightarrow> (compose X f g)`A \<subseteq> A"
  by (simp add: compose_eq subset_eq)
           
lemma im_restrict_sub2:"A \<in> Pow X \<Longrightarrow> f`A \<subseteq> A \<Longrightarrow> g`A \<subseteq> A \<Longrightarrow> (compose X f g)`A \<subseteq> A"
  by (simp add: compose_eq subset_eq)
           
lemma im_restrict_eq:"A \<subseteq> X \<Longrightarrow> f`A = A \<Longrightarrow> g`A = A \<Longrightarrow> (compose X f g)`A = A"
  apply(auto simp add:compose_def)
  apply fastforce
  by (metis image_image inf.absorb_iff2 inf_commute)
lemma im_restrict_eq2:"A \<in> Pow X \<Longrightarrow> f`A = A \<Longrightarrow> g`A = A \<Longrightarrow> (compose X f g)`A = A"
  by (simp add: im_restrict_eq)


section \<open>Extensionality\<close>
lemma maps_on_memI[intro]:
  "(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> maps_on A" 
  by (simp add: maps_on_def)

lemma maps_on_memD:
  "f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" 
  by (simp add: maps_on_def)

lemma maps_on_empty[simp]:
  "maps_on {} = {\<lambda>x. undefined}" 
  unfolding maps_on_def by auto

lemma maps_on_arb: 
  "f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" 
  by (simp add: maps_on_def)

lemma restrict_maps_on [simp]: 
  "restrict f A \<in> maps_on A"
  by (simp add: restrict_def maps_on_def)

lemma compose_maps_on [simp]: 
  "compose A f g \<in> maps_on A"  
  by (simp add: compose_def)

lemma maps_on_equalityI:
  "f \<in> maps_on A \<Longrightarrow> g \<in> maps_on A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g" 
  by (force simp add: fun_eq_iff maps_on_def)

lemma maps_on_restrict:
  "f \<in> maps_on A \<Longrightarrow> restrict f A = f" 
  by (rule maps_on_equalityI[OF restrict_maps_on]) auto

lemma maps_on_subset: 
  "f \<in> maps_on A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f \<in> maps_on B"
  unfolding maps_on_def by auto

lemma maps_on_Int[simp]:
  "maps_on I \<inter> maps_on I' = maps_on (I \<inter> I')"  
  unfolding maps_on_def by auto

lemma maps_on_UNIV[simp]: 
  "maps_on UNIV = UNIV" 
  by (auto simp: maps_on_def)

lemma restrict_maps_on_sub[intro]:
  "A \<subseteq> B \<Longrightarrow> restrict f A \<in> maps_on B" 
  unfolding restrict_def maps_on_def by auto

lemma maps_on_insert_cancel[intro, simp]:
 "a \<in> maps_on I \<Longrightarrow> a \<in> maps_on (insert i I)"  
  unfolding maps_on_def by auto

lemma hom_memI1:
  "(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> set_morphisms A B" 
  unfolding set_morphisms_def by fast

lemma hom_memI2:
  "f \<in> maps_on A \<Longrightarrow> f \<in>maps_to A B \<Longrightarrow> f \<in> set_morphisms A B"
  by(rule hom_memI1,auto elim: maps_on_memD)

lemma hom_memD1:
  "f \<in> set_morphisms A B \<Longrightarrow> f \<in> maps_on A" 
  unfolding set_morphisms_def maps_on_def by(auto)

lemma hom_memD2:
  "f \<in> set_morphisms A B \<Longrightarrow> f \<in> maps_to A B"
  unfolding set_morphisms_def maps_to_def by(auto)

lemma id1[simp]:
  "Id X x = (if x \<in> X then x else undefined)"
  by (simp add:Id_def)

lemma id2[simp]:
  "x \<in> X \<Longrightarrow> Id X x = x"
  by simp

lemma hom1:
  "set_morphisms {} Y = {\<lambda>x. undefined}" 
    by(auto simp add:set_morphisms_def) 

lemma hom2:
  "f \<in> set_morphisms A B \<Longrightarrow> g \<in> set_morphisms B C \<Longrightarrow> compose A g f \<in> set_morphisms A C" 
  by(auto simp add:set_morphisms_def compose_def)

lemma hom3:
  "f \<in> set_morphisms A B \<Longrightarrow> compose A h (compose A g f) = compose A (compose B h g) f" 
  by(auto simp add:set_morphisms_def fun_eq_iff compose_def)

lemma fun_eqI:
  "f \<in> set_morphisms A Y \<Longrightarrow> g \<in> set_morphisms A Z \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g" 
  by (meson hom_memD1 maps_on_equalityI) 

lemma hom5:
  "f \<in> set_morphisms A B \<Longrightarrow> compose A (Id B) f = f"
  by(auto simp add:fun_eq_iff compose_def set_morphisms_def)

lemma hom6:"f \<in> set_morphisms A B  \<Longrightarrow> compose A f (Id A) = f" 
  by(auto simp add:fun_eq_iff compose_def set_morphisms_def)

lemma hom7:"(Id A) \<in> set_morphisms A A" 
  unfolding set_morphisms_def by(auto)

lemma hom8:
  "A \<subseteq> B \<Longrightarrow> (Id A) \<in> set_morphisms A B"  
  using set_morphisms_def by fastforce 

lemma hom9:
  "f \<in> set_morphisms A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B"
  unfolding set_morphisms_def by simp

lemma hom10:
  "f \<in> set_morphisms A B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined"
  unfolding set_morphisms_def by simp

lemma hom11:
  "f \<in> set_morphisms A B \<Longrightarrow> g \<in> set_morphisms A C \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = g x"
  unfolding set_morphisms_def by(auto)

lemma set_morphisms_eq_maps_to_inter_maps_on: 
  "set_morphisms A B = maps_to A B \<inter> maps_on A"
  unfolding set_morphisms_def maps_to_def maps_on_def by auto

lemma set_epimorphisms_eq_set_morphisms_inter_surjectives:
  "set_epimorphisms A B = set_morphisms A B \<inter> surjectives A B"
  unfolding set_epimorphisms_def set_morphisms_def surjectives_def by auto

lemma set_epimorphisms_eq_maps_to_inter_maps_on_inter_surjectives:
  "set_epimorphisms A B = maps_to A B \<inter> maps_on A \<inter> surjectives A B"
  by (simp add: set_epimorphisms_eq_set_morphisms_inter_surjectives set_morphisms_eq_maps_to_inter_maps_on)

lemma set_monomorphisms_eq_set_morphisms_inter_injs:
  "set_monomorphisms A B = set_morphisms A B \<inter> injectives A"
  unfolding set_monomorphisms_def set_morphisms_def injectives_def inj_on_def by auto


lemma set_isomorphisms_eq_set_morphisms_inter_bijs:
  "set_isomorphisms A B = set_morphisms A B \<inter> bijectives A B"
  unfolding set_isomorphisms_def set_morphisms_def bijectives_def bij_betw_def inj_on_def by(auto)

lemma set_monomorphisms_memI:
  "f \<in> set_morphisms A B \<Longrightarrow> inj_on f A \<Longrightarrow> f \<in> set_monomorphisms A B "
  by (simp add: inj_on_def set_monomorphisms_def set_morphisms_def)

lemma set_epimorphisms_memI:
  "f \<in> set_morphisms A B \<Longrightarrow> f`A=B \<Longrightarrow> f \<in> set_epimorphisms A B "
  by (simp add:set_epimorphisms_def set_morphisms_def)          

lemma set_epimorphisms_memE1:
  "f \<in> set_epimorphisms A B \<Longrightarrow> f \<in> set_morphisms A B"
  by (simp add: set_epimorphisms_eq_set_morphisms_inter_surjectives)

lemma set_monomorphisms_memE1:
  "f \<in> set_monomorphisms A B \<Longrightarrow> f \<in> set_morphisms A B"
  by (simp add: set_monomorphisms_eq_set_morphisms_inter_injs)

lemma set_epimorphisms_memE2:
  "f \<in> set_epimorphisms A B \<Longrightarrow> f`A=B"
  by (simp add: set_epimorphisms_def)

lemma set_monomorphisms_memE2:
  "f \<in> set_monomorphisms A B \<Longrightarrow> inj_on f A"
  unfolding set_monomorphisms_def using inj_on_def by auto

lemma set_epimorphisms_memE3:
  "f \<in> set_epimorphisms A B \<Longrightarrow> f \<in> surjectives A B"
  by (simp add: set_epimorphisms_eq_set_morphisms_inter_surjectives)

lemma set_monomorphisms_memE3:
  "f \<in> set_monomorphisms A B \<Longrightarrow> f \<in> injectives A"
  by (simp add: set_monomorphisms_eq_set_morphisms_inter_injs)

lemma set_monomorphisms_memI2:
  "f \<in> set_morphisms A B \<Longrightarrow> f \<in> injectives A \<Longrightarrow> f \<in> set_monomorphisms A B "
  by (simp add: set_monomorphisms_eq_set_morphisms_inter_injs)

lemma set_epimorphisms_memI2:
  "f \<in> set_morphisms A B \<Longrightarrow> f \<in> surjectives A B \<Longrightarrow> f \<in> set_epimorphisms A B "
  by (simp add: set_epimorphisms_eq_set_morphisms_inter_surjectives)

lemma set_monomorphisms_eq_maps_to_inter_maps_on_inter_injs:
  "set_monomorphisms A B = maps_to A B \<inter> maps_on A \<inter> injectives A"
  unfolding set_monomorphisms_def maps_to_def maps_on_def injectives_def inj_on_def by auto

lemma set_isomorphisms_eq_epi_inter_mono:
  "set_isomorphisms A B =  set_epimorphisms A B \<inter> set_monomorphisms A B"
  unfolding set_isomorphisms_def set_epimorphisms_def set_monomorphisms_def by auto

lemma set_isomorphism_memI1:
  "f \<in> set_monomorphisms A B \<Longrightarrow> f \<in> set_epimorphisms A B \<Longrightarrow> f \<in> set_isomorphisms A B"
  by (simp add: set_isomorphisms_eq_epi_inter_mono)

lemma set_isomorphism_memE1:
  " f \<in> set_isomorphisms A B \<Longrightarrow> f \<in> set_monomorphisms A B \<and> f \<in> set_epimorphisms A B "
  by (simp add: set_isomorphisms_eq_epi_inter_mono)

lemma set_isomorphismE2:
  " f \<in> set_isomorphisms A B \<Longrightarrow>bij_betw f A B "
  unfolding bij_betw_def using set_epimorphisms_memE2 set_isomorphism_memE1 set_monomorphisms_memE2 by blast

lemma set_isomorphismE3:
  " f \<in> set_isomorphisms A B \<Longrightarrow> f \<in> bijectives A B "
  by (simp add: bijectives_def set_isomorphismE2)

lemma set_isomorphism_memI2:
  "f \<in> set_morphisms A B \<Longrightarrow> bij_betw f A B \<Longrightarrow> f \<in> set_isomorphisms A B "
  by (simp add: bij_betw_imp_inj_on bij_betw_imp_surj_on set_epimorphisms_memI set_isomorphism_memI1 set_monomorphisms_memI)


lemma set_isomorphism_mem3:
  "f \<in> set_morphisms A B \<Longrightarrow> f \<in> bijectives A B \<Longrightarrow> f \<in> set_isomorphisms A B "
  by (simp add: bijectives_def set_isomorphism_memI2)

lemma ker_pair_subI:"(\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> g x = g y \<Longrightarrow> f x = f y) \<Longrightarrow> ker_pair X g \<subseteq> ker_pair X f"
  unfolding ker_pair_def  by auto

lemma is_right_invI0:
  "compose Y f s = Id Y \<Longrightarrow> is_right_inv Y f s"
  by (simp add: is_right_inv_def)

lemma is_right_invI1:
  "(\<And>y. y \<in> Y \<Longrightarrow> f (s y) = y) \<Longrightarrow> is_right_inv Y f s" 
  unfolding is_right_inv_def compose_def using restrict_ext[of Y] by auto

lemma is_right_invI2:
  "(\<And>y. y \<in> Y \<Longrightarrow> y = f (s y)) \<Longrightarrow> is_right_inv Y f s"
  by (simp add: is_right_invI1)

lemma is_right_invE1:
  "is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> f (s y) = y"  
  by (metis compose_eq id1 is_right_inv_def)

lemma is_right_invE2:
  "is_right_inv Y f s \<Longrightarrow> y \<in> Y \<Longrightarrow> y = f (s y) "
  by (simp add: is_right_invE1) 

lemma is_right_inv_E3:
  "is_right_inv Y f s \<Longrightarrow> compose Y f s = Id Y"
  by (simp add: is_right_inv_def)

lemma ex_rinv_imp_surj:
  "\<exists>s. is_right_inv Y f s \<Longrightarrow> f`(vimage f Y) = Y"  
  using is_right_invE2 by fastforce

lemma is_rinv_imp_surj: 
  "is_right_inv Y f s \<Longrightarrow> f`(vimage f Y)=Y" 
  using ex_rinv_imp_surj by blast

lemma is_left_invI0:
  "compose X r f= Id X \<Longrightarrow> is_left_inv X f r"
  by (simp add: is_left_inv_def)

lemma is_left_invI1:
  "(\<And>x. x \<in> X \<Longrightarrow> r (f x) = x) \<Longrightarrow> is_left_inv X f r" 
  unfolding is_left_inv_def compose_def by auto

lemma is_left_invI2:
  "(\<And>x. x \<in> X \<Longrightarrow> x = r (f x)) \<Longrightarrow> is_left_inv X f r" 
  by (simp add: is_left_invI1)

lemma is_left_invE1:
  "is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> r (f x) = x"
  by (metis compose_eq id1 is_left_inv_def) 

lemma is_left_invE2:
  "is_left_inv X f r \<Longrightarrow> x \<in> X \<Longrightarrow> x = r (f x)" 
  by (simp add: is_left_invE1) 

lemma is_left_inv_E3:
  "is_left_inv X f r \<Longrightarrow> compose X r f = Id X"
  by (simp add: is_left_inv_def)

lemma linv_cancel:
  "is_left_inv X f r \<Longrightarrow> x1 \<in>X \<Longrightarrow>  x2 \<in> X \<Longrightarrow> f x1 = f x2 \<Longrightarrow> x1 =x2" 
proof-
  assume A0:"is_left_inv X f r" and A1:"x1 \<in> X" and A2:"x2 \<in> X" and A3:"f x1 = f x2"
  then obtain "x1 = r ( f x1)" and "x2 = r ( f x2)"
    using A1 A0 A2 is_left_invE2[of X f r x1] is_left_invE2[of X f r x2] by blast
  then show "x1 = x2"
    using A3 by force
qed

lemma ex_linv_implies_inj:
  "\<exists>s. is_left_inv X f r \<Longrightarrow> inj_on f X" 
  by (simp add: inj_on_def linv_cancel)

lemma is_linv_implies_inj:
  "is_left_inv X f r \<Longrightarrow> inj_on f X"
  by (simp add: inj_on_def linv_cancel)

lemma inj_implies_ex_linv:
  "inj_on f X \<Longrightarrow> \<exists>r. is_left_inv X f r"
  by (metis is_left_invI1 the_inv_into_f_f)

lemma rinv_simp:
  "y \<in> Y \<Longrightarrow> (rinv f X Y) y = (\<lambda>y. SOME x. x \<in> X \<and> f x = y) y" 
  by (simp add: rinv_def)

lemma rinv_closed:
  "y \<in> f`X \<inter> Y \<Longrightarrow> rinv f X Y y \<in> X" 
  by(simp add:rinv_def,fast intro: someI2)

lemma rinv_undef:
  "y \<notin> Y \<Longrightarrow> rinv f X Y y = undefined" 
  by(simp add:rinv_def)

lemma rinv_map_to: "f ` A = B \<Longrightarrow> (rinv f A B) \<in> maps_to B A"  
  by (unfold rinv_def) (fast intro: someI2)

lemma id_surj:"(Id A)`A = A" 
  by force

lemma rinv_comp_to:
  "f ` A = B \<Longrightarrow> compose B f (rinv f A B) \<in> maps_to B B" 
  apply(rule maps_to_memI)
  using compose_eq[ of _ B f "rinv f A B"] rinv_closed[of _ f A B] by blast

lemma rinv_into_into:"f \<in> set_morphisms A B \<Longrightarrow> y \<in> f ` A \<Longrightarrow> rinv f A B y \<in> A"
  apply(auto simp add: rinv_def)
   apply(fast intro:someI2)
  by (simp add: hom9)

lemma rinv_identity[simp]:
  "rinv (Id A) A A= Id A"  
  by (force simp add: rinv_def)
lemma rinv_into_f_f[simp]: 
  "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> (rinv f A (f`(A))) (f x) = x"  
  by (simp add: rinv_def inj_on_def) (blast intro: someI2)

lemma f_inv_into_f:
  "y \<in> f`A \<Longrightarrow> f (rinv f A (f`A) y) = y"
  by (simp add: rinv_def) (fast intro: someI2)
lemma rinv_into_f_eq: 
  "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> f x = y \<Longrightarrow> rinv f A (f`A) y = x"
  by (erule subst) (fast intro: rinv_into_f_f)

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

lemma inj_on_rinv_into: 
  "B \<subseteq> f`A \<Longrightarrow> inj_on (rinv f A (f`A)) B"  
  by (blast intro: inj_onI dest: rinv_into_injective injD)

lemma bij_betw_rinv_into:
  "bij_betw f A B \<Longrightarrow> bij_betw (rinv f A B) B A" 
  by (auto simp add: bij_betw_def inj_on_rinv_into image_iff)

lemma rinv_into_f:
  "f`A = B \<Longrightarrow> y \<in> f`A \<Longrightarrow> f (rinv f A B y) = y" 
  by (simp add: rinv_def) (fast intro: someI2)

lemma into_rinv_f:"\<lbrakk>f \<in> maps_to A B; inj_on f A; x \<in> A\<rbrakk> \<Longrightarrow> (rinv f A B) (f x) = x"
proof -
  assume A0: "inj_on f A" and A1: "x \<in> A" and A2: "f \<in> maps_to A B"
  then obtain "rinv f A (f ` A) (f x) = x" and  "f x \<in> B"
    by auto
  then show ?thesis
    by (simp add: A1 rinv_simp)
qed

lemma into_rinv_f2:
  "bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow> rinv f A B (f x) = x" 
  by (simp add: bijD1 bij_betw_imp_inj_on into_rinv_f)

lemma rinv_inv:
  "f ` A = B \<Longrightarrow> compose B f (rinv f A B) = Id B"
  by (simp add: is_left_invI2 is_left_inv_E3 rinv_into_f)

lemma inv_rinv: 
  "f \<in> maps_to A B \<Longrightarrow> inj_on f A \<Longrightarrow> compose A (rinv f A B) f= Id A"
  by (simp add: into_rinv_f is_left_invI2 is_left_inv_E3) 

lemma inv_rinv2:"bij_betw f A B \<Longrightarrow> compose A (rinv f A B) f= Id A"  
  by (simp add: bijD1 bij_betw_imp_inj_on inv_rinv)

lemma inv_rinv3:"bij_betw f A B \<Longrightarrow> compose B f (rinv f A B)= Id B"
  by (simp add: bij_betw_imp_surj_on rinv_inv)  

lemma rinv_restrict:
  "f`A = B \<Longrightarrow> restrict (rinv f A B) B = rinv f A B" 
  by (simp add: rinv_def)

lemma rinv_is_rinv:
  "f ` A = B \<Longrightarrow> is_right_inv B f (rinv f A B)"
  by (simp add: is_right_inv_def rinv_inv)

lemma rinv_is_linv:
  "f \<in> maps_to A B \<Longrightarrow> inj_on f A \<Longrightarrow> is_left_inv A f (rinv f A B)"
  by (simp add: is_left_inv_def inv_rinv)


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

lemma rinv_in_maps_on:
  "rinv f A B \<in> maps_on B"
  by (simp add: rinv_def)

lemma rinv_inv_set_morphisms:
  "f`A=B \<Longrightarrow> rinv f A B \<in> set_morphisms B A"
  by (simp add: hom_memI2 rinv_in_maps_on rinv_map_to)


lemma inj_implies_factors_concrete:
  fixes X::"'a set" and Y::"'b set" and Z::"'c set" and f::"'a \<Rightarrow> 'b" and g::"'c \<Rightarrow> 'b"
  assumes A0:"f \<in> set_morphisms X Y" and A1:"g \<in> set_morphisms Z Y" and A2:"inj_on g Z" and A3:"(f`X) \<subseteq> (g`Z)"
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = g (rinv g Z Y (f x))" and 
        "compose X (rinv g Z Y) f \<in> set_morphisms X Z" and 
        "compose X g (compose X (rinv g Z Y) f) \<in> set_morphisms X Y" and
        "\<And>x. x \<in> X \<Longrightarrow> f x = compose X g (compose X (rinv g Z Y) f) x" and
        "f = compose X g (compose X (rinv g Z Y) f)" and
       "\<And>h. \<lbrakk>h \<in> set_morphisms X Z; f = compose X g h\<rbrakk> \<Longrightarrow> h =compose X (rinv g Z Y) f"
proof-
  show P0:"\<And>x. x \<in> X \<Longrightarrow> f x = g (rinv g Z Y (f x))"
  proof-
    let ?r="rinv g Z Y"
    fix x assume A4:"x \<in> X" then obtain B0:"f x \<in> Y" 
      using A0 A4 hom9[of f X Y] by blast 
    let ?z="?r (f x)"
    obtain B1:"?z \<in> Z"
      by (meson A1 A3 A4 imageI in_mono rinv_into_into)
    then show B2:"f x = g ?z"
      using A1 A2 A3 A4 hom_memD2 into_rinv_f by fastforce
  qed
  show P1:"compose X (rinv g Z Y) f \<in> set_morphisms X Z"
    unfolding set_morphisms_def apply(auto)
    apply (meson compose_maps_on maps_on_memD)
    by (metis A1 A3 compose_eq image_subset_iff rinv_into_into)
  show P2:"compose X g (compose X (rinv g Z Y) f) \<in> set_morphisms X Y"
    using A1 P1 hom2 by blast
  show P3:"\<And>x. x \<in> X \<Longrightarrow> f x = compose X g (compose X (rinv g Z Y) f) x"
    by (metis P0 compose_eq)
  show P3:"f = compose X g (compose X (rinv g Z Y) f)"
    using A0 P2 P3 fun_eqI by blast
  show P4:"\<And>h. \<lbrakk>h \<in> set_morphisms X Z; f = compose X g h\<rbrakk> \<Longrightarrow> h =compose X (rinv g Z Y) f"
    by (simp add: A1 A2 hom3 hom5 hom_memD2 inv_rinv)
qed


lemma surj_implies_factors_concrete:
  fixes X::"'a set" and Y::"'b set" and Z::"'c set" and f::"'a \<Rightarrow> 'b" and g::"'a \<Rightarrow> 'c"
  assumes A0:"f \<in> set_morphisms X Y" and A1:"g \<in> set_morphisms X Z" and A2:"g`X=Z" and A3:"ker_pair X g \<subseteq> ker_pair X f"
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = f (rinv g X Z (g x))" and
        "compose Z f (rinv g X Z) \<in> set_morphisms Z Y" and
        "\<And>x. x \<in> X \<Longrightarrow> f x = compose X (compose Z f (rinv g X Z)) g x"
        "f = compose X (compose Z f (rinv g X Z)) g" and
        "\<And>h. \<lbrakk>h \<in> set_morphisms Z Y; f = compose X h g\<rbrakk> \<Longrightarrow> h = compose Z f (rinv g X Z)"
proof-
  have P0:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X; g x = g y\<rbrakk> \<Longrightarrow> f x = f y"
    using A3 unfolding ker_pair_def by blast
  show P1:"\<And>x. x \<in> X \<Longrightarrow> f x = f (rinv g X Z (g x))" 
  proof-
    let ?s="rinv g X Z"
    fix x assume A4:"x \<in> X" then obtain B1:"g x \<in> Z" 
      using A2 by blast 
    let ?x="?s (g x)"
    obtain B2:"?x\<in> X"
      by (simp add: rinv_closed A2 B1)
    then obtain B3:"g x = g ?x"
      by (simp add: B1 rinv_into_f A2)
    then show "f x = f ?x" 
      using B2 A4 P0[of x ?x] by blast
  qed
  show P2:"compose Z f (rinv g X Z) \<in> set_morphisms Z Y"
    using A0 A2 hom2 rinv_inv_set_morphisms by blast
  show P3: "\<And>x. x \<in> X \<Longrightarrow> f x = compose X (compose Z f (rinv g X Z)) g x"
    by (metis A1 P1 compose_eq hom9)
  show P4:"f = compose X (compose Z f (rinv g X Z)) g"
    using A0 A1 P2 P3 fun_eqI hom2 by blast
  show P5:"\<And>h. \<lbrakk>h \<in> set_morphisms Z Y; f = compose X h g\<rbrakk> \<Longrightarrow> h = compose Z f (rinv g X Z)"
    by (metis A2 compose_assoc hom6 rinv_inv rinv_map_to)
qed


lemma surj_implies_factors:
  assumes surj:"g`X=Y" and compat:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X; g x = g y\<rbrakk> \<Longrightarrow> f x = f y"
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = f (rinv g X Y (g x))" and
        "\<And>x. x \<in> X \<Longrightarrow> f x = compose Y f (rinv g X Y) (g x)"
proof-
  show P0: "\<And>x. x \<in> X \<Longrightarrow> f x = f (rinv g X Y (g x))"
  proof-
    let ?s="rinv g X Y"
    fix x assume A0:"x \<in> X" then obtain B0:"g x \<in> Y" 
      using surj by blast 
    let ?y="?s (g x)"
    obtain B1:"?y \<in> X"
      by (simp add: rinv_closed surj B0)
    then obtain B2:"g x = g ?y"
      by (simp add: B0 rinv_into_f surj)
    then show "f x = f ?y" 
        using compat A0 B1 by blast
  qed
  show P1:"\<And>x. x \<in> X \<Longrightarrow> f x = compose Y f (rinv g X Y) (g x)"
    by (metis P0 compose_eq image_eqI surj)
qed


lemma rinv_unique_on1:
  assumes A0:"f`A=B" and A1:"is_right_inv B f s" and A2:"s`B=(rinv f A B)`B" and A3:"s \<in> set_morphisms B A"
  shows "s=rinv f A B"
  using A3
proof(rule fun_eqI)
  show B0:"rinv f A B \<in> set_morphisms B A"
    by (simp add: A0 rinv_inv_set_morphisms)
  have B1:"\<And>y. y \<in> B \<Longrightarrow> f (s y) = y"
    by (metis A1 is_right_invE2) 
  show B2:"\<And>y. y \<in> B \<Longrightarrow> s y = rinv f A B y"
    using A0 A2 B1 rinv_unique_on[of f A B s]  by presburger 
qed

lemma surj_implies_ex_rinv:
  "surj f (vimage f Y) Y \<Longrightarrow> \<exists>s. is_right_inv Y f s"
proof-
  assume onto:"surj f (vimage f Y) Y"
  have "\<exists>s. \<forall>y \<in> Y. y = f (s y)"
  proof(rule bchoice[of Y "\<lambda>a b. a = f b"])
    show "\<forall>y::'b\<in>Y. \<exists>x. y = f x"
    using onto unfolding surj_def by fastforce
  qed
  then show "\<exists>s. is_right_inv Y f s"
    by (metis is_right_invI1)
qed

lemma left_inv_target: "is_left_inv X f r \<Longrightarrow> r`(f`X) = X "
  by (metis image_ident image_restrict_eq is_left_inv_def surj_compose)  

lemma right_inv_target: 
  "is_right_inv Y f s \<Longrightarrow> f`(s`Y) = Y"
  by (simp add: is_left_inv_def is_right_inv_def left_inv_target)

lemma rinv_l:
  "is_left_inv X f r \<Longrightarrow> is_right_inv X r f"
  by (simp add: is_left_inv_def is_right_inv_def)  

lemma linv_r:
  "is_right_inv (Y::'b set) f s \<Longrightarrow> is_left_inv Y s f" 
  by (simp add: is_left_inv_def is_right_inv_def) 

lemma rinv_surj:
  "is_left_inv X f r \<Longrightarrow> surj r (f`X) X"
  by (simp add: surj_def left_inv_target)

lemma rinv_inj:
 "is_right_inv (Y::'b set) f s \<Longrightarrow> inj_on s Y"  
  using is_linv_implies_inj linv_r by blast

lemma bij_betw_rinv:
  "bij_betw f A B \<Longrightarrow> y \<in> B \<Longrightarrow> f (rinv f A B y) = y"  
  by (simp add: bij_betw_imp_surj_on rinv_into_f)

lemma bij_betw_linv:
  "bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow> (rinv f A B) (f x)= x" 
  by(simp add:  bij_betw_def,force)

lemma bij_betw_hom_rev:"bij_betw f A B \<Longrightarrow> rinv f A B \<in> set_morphisms B A"
  by(rule hom_memI2,simp add: rinv_def,simp add:bijD1 bij_betw_rinv_into)

section \<open>Set Morphism Locales\<close>

locale set_morphism=
  fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"
  assumes dom[intro]:"x \<notin> A \<longrightarrow> f x = undefined" and  
          cod[intro,simp]:"x \<in> A \<Longrightarrow> f x \<in> B"
begin
lemma mem_maps_to:
 "f \<in> maps_to A B" 
  by (simp add: maps_to_memI)

lemma mem_maps_on:
  "f \<in> maps_on A" 
  by (simp add: dom maps_on_memI) 

lemma mem_hom:
  "f \<in> set_morphisms A B" 
  by (simp add: hom_memI2 mem_maps_on mem_maps_to)
end

lemma set_morphismI1:
  "f \<in> set_morphisms A B \<Longrightarrow> set_morphism f A B"
  unfolding set_morphisms_def by(auto intro!: set_morphism.intro)

lemma set_morphismD1:
  "set_morphism f A B \<Longrightarrow> f \<in> set_morphisms A B" 
  by (simp add: set_morphism.mem_hom) 

lemma set_morphism_iff:
  "f \<in> set_morphisms A B \<longleftrightarrow> set_morphism f A B"  
  using set_morphismD1 set_morphismI1 by blast

locale sur_locale=fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set"
  assumes sur[intro]:"f `A = B"

locale inj_locale=
  fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" 
  assumes inj[intro, simp]:"inj_on f A"

locale iso_locale=
  fixes f::"'a \<Rightarrow> 'b" and A::"'a set" and B::"'b set" 
  assumes iso[intro, simp]:"bij_betw f A B"

locale set_epimorphism = 
  set_morphism f A B + sur_locale f A B for f and A and B
begin

sublocale set_morphism f A B  by (simp add: set_morphism_axioms)
definition right_inverse ("s") where "right_inverse \<equiv> rinv f A B"

lemma set_epimorphism_mem:"f \<in> set_epimorphisms A B"
  by (simp add: dom set_epimorphisms_def sur)

lemma right_inv_is_set_morphism:
  "s \<in> set_morphisms B A"
  by (simp add: right_inverse_def rinv_inv_set_morphisms sur)

lemma right_inverse_inv:
  "is_right_inv B f s"  
  by (simp add: right_inverse_def rinv_is_rinv sur)

lemma right_inverse_inj:
  "s \<in> injectives B"
  using injectives_def right_inverse_inv rinv_inj by fastforce

lemma right_inv_is_set_mono:
  "s \<in> set_monomorphisms B A"
  by (simp add: right_inv_is_set_morphism right_inverse_inj set_monomorphisms_memI2)

lemma right_inverse_comp1:
  "compose B f s = Id B"  
  by (simp add: right_inverse_def rinv_inv sur)

lemma right_inverse_comp2:
  "y \<in> B \<Longrightarrow> compose B f s y = y"
  by (simp add: right_inverse_comp1)

lemma right_inverse_comp3:
  "y \<in> B \<Longrightarrow> f (s y) = y"  
  by (simp add: right_inverse_def rinv_into_f sur)

end


lemma set_epimorphismI1:
  "f \<in> set_epimorphisms A B \<Longrightarrow> set_epimorphism f A B"
  by (simp add: set_epimorphism.intro set_epimorphisms_memE1 set_epimorphisms_memE2 set_morphismI1 sur_locale.intro)

lemma set_epiI1:"f \<in> set_morphisms A B \<Longrightarrow> f`A=B \<Longrightarrow> set_epimorphism f A B"
  by (simp add: set_epimorphism_def set_morphismI1 sur_locale.intro) 

lemma set_epimorphismD1:
  "set_epimorphism f A B \<Longrightarrow> f \<in> set_epimorphisms A B"
  by (simp add: set_epimorphism.set_epimorphism_mem) 

lemma set_epimorphism_iff:
  "f \<in> set_epimorphisms A B \<longleftrightarrow> set_epimorphism f A B"
  using set_epimorphismD1 set_epimorphismI1 by blast  


locale set_monomorphism=set_morphism f A B+ inj_locale f A B for f and A and B
begin

sublocale set_morphism f A B  by (simp add: set_morphism_axioms)

definition left_inverse ("r") where "left_inverse \<equiv> rinv f A B"

lemma set_monomorphism_mem:"f \<in> set_monomorphisms A B"
  by (simp add: mem_hom set_monomorphisms_memI)

lemma injectives_mem:"f \<in> injectives A"
  by (simp add: injectives_def)

lemma left_inverse_comp1:
  "compose A r f = Id A"
  by (simp add: inv_rinv left_inverse_def mem_maps_to) 

lemma 
  left_inverse_comp2:
  "x \<in> A \<Longrightarrow> compose A r f x = x" 
  by (simp add: left_inverse_comp1) 

lemma left_inverse_comp3:
  "x \<in> A \<Longrightarrow> r (f  x) = x" 
  by (simp add: into_rinv_f left_inverse_def mem_maps_to)

lemma left_inverse_inv:
  "is_left_inv A f r" 
  by (simp add: is_left_inv_def left_inverse_comp1) 

end


lemma set_monoI1:"f \<in> set_morphisms A B \<Longrightarrow> inj_on f A \<Longrightarrow> set_monomorphism f A B"
  by (simp add: inj_locale.intro set_monomorphism_def set_morphism_iff)

lemma set_monoI2:"f \<in> set_morphisms A B \<Longrightarrow>f \<in> injectives A \<Longrightarrow> set_monomorphism f A B"
  by (simp add: injectives_def set_monoI1)

lemma set_monomorphismI1:
  "f \<in> set_monomorphisms A B \<Longrightarrow> set_monomorphism f A B"
  by (simp add: set_monoI2 set_monomorphisms_eq_set_morphisms_inter_injs)

lemma set_monomorphismD1:
  "set_monomorphism f A B \<Longrightarrow> f \<in> set_monomorphisms A B"
  by (simp add: set_monomorphism.set_monomorphism_mem)

lemma set_monomorphism_iff:
  "f \<in> set_monomorphisms A B \<longleftrightarrow> set_monomorphism f A B"
  using set_monomorphismD1 set_monomorphismI1 by blast


locale set_isomorphism =set_morphism + iso_locale
begin
sublocale set_morphism f A B  by (simp add: set_morphism_axioms)
sublocale epi:set_epimorphism  by unfold_locales (simp add:bij_betw_imp_surj_on)
sublocale mono:set_monomorphism   using bij_betw_def by unfold_locales fast
sublocale inv:set_morphism "rinv f A B" B A  using bij_betw_hom_rev set_morphism_iff by blast 
sublocale iso:iso_locale "rinv f A B" B A  by (simp add: bij_betw_rinv_into iso_locale.intro)

lemma set_iso_mem:
  "f \<in> set_isomorphisms A B"
  by (simp add: mem_hom set_isomorphism_memI2)

end

lemma set_isoI1:"f \<in> set_morphisms A B \<Longrightarrow> bij_betw f A B \<Longrightarrow> set_isomorphism f A B"
  by (simp add: iso_locale.intro set_isomorphism_def set_morphismI1)

lemma set_isomorphismI1:
  "set_isomorphism f A B \<Longrightarrow> f \<in> set_isomorphisms A B"
  by (simp add: set_isomorphism.set_iso_mem)

lemma set_isomorphismD1:
  "set_isomorphism f A B \<Longrightarrow> f \<in> set_isomorphisms A B"
  by (simp add: set_isomorphismI1)

lemma set_isomorphism_iff:
  "f \<in> set_isomorphisms A B \<longleftrightarrow> set_isomorphism f A B"
  using set_isoI1 set_isomorphismE2 set_isomorphismI1 set_isomorphism_memE1 set_monomorphisms_memE1 by blast


lemma bij_bewt_has_lr_inv:
  "bij_betw f A B \<Longrightarrow> (\<exists>g \<in> set_morphisms B A. is_left_inv A f g \<and> is_right_inv B f g)"
  by (metis bij_betw_hom_rev bij_betw_imp_surj_on inv_rinv2 is_left_invI0 rinv_is_rinv)



context set_morphism
begin

lemma bij_bewt_has_inverse:
  "bij_betw f A B \<Longrightarrow> (\<exists>g \<in> set_morphisms B A. compose A g f = Id A \<and> compose B f g = Id B)"
  using bij_bewt_has_lr_inv is_left_inv_E3 is_right_inv_def by fastforce

lemma has_inverse_bij_bewt:
  "(\<exists>g \<in> set_morphisms B A. is_left_inv A f g \<and> is_right_inv B f g) \<Longrightarrow> bij_betw f A B"
  using bijI hom_memD2 is_left_invE1 is_right_invE1 mem_maps_to by fastforce

lemma bij_betw_iff_has_inverse:
  "bij_betw f A B \<longleftrightarrow> (\<exists>g \<in> set_morphisms B A. compose A g f = Id A \<and> compose B f g = Id B)" 
  (is "_ \<longleftrightarrow> (\<exists>g \<in> set_morphisms B A. ?INV g)")
  using bij_bewt_has_inverse has_inverse_bij_bewt is_left_invI0 is_right_inv_def by blast


end


section Equivalence

locale equivalence_relation=
  fixes X :: "'a set" and R :: "('a \<times> 'a) set"
  assumes sub[intro, simp]:"R \<subseteq> X \<times> X" and
          ref[intro, simp]: "a \<in> X \<Longrightarrow> (a, a) \<in> R" and 
          sym[sym]: "(a, b) \<in> R \<Longrightarrow> (b, a) \<in> R" and
          trn[trans]: "\<lbrakk>(a, b) \<in> R; (b, c) \<in> R \<rbrakk> \<Longrightarrow> (a, c) \<in> R"
begin
abbreviation "p \<equiv> qproj X R"
abbreviation "pinv \<equiv> qsect X R"

lemma l_closed[intro]:
  "(a, b) \<in> R \<Longrightarrow> a \<in> X" 
  using sub by blast

lemma r_closed[intro]:
  "(a, b) \<in> R \<Longrightarrow> b \<in> X" 
  using sub by blast

lemma qproj_def2:
  "p = (\<lambda>x \<in> X. R``{x})" 
  unfolding qproj_def by fastforce

lemma p_closed1[dest]:
  "x \<in> X \<Longrightarrow> y \<in> p x \<Longrightarrow> y \<in> X" 
  unfolding qproj_def by auto

lemma p_closed2[intro, simp]:
  "a \<in> X \<Longrightarrow> p a \<subseteq> X" 
  unfolding qproj_def by auto

lemma p_undefined[intro, simp]:
  "a \<notin> X \<Longrightarrow> p a = undefined" 
  unfolding qproj_def by simp

lemma p_I1[intro, simp]:
  "(a, b) \<in> R \<Longrightarrow> b \<in> p a"  
  unfolding qproj_def by (simp add: l_closed r_closed)

lemma p_revI [intro, simp]:
  "(a, b) \<in> R \<Longrightarrow> a \<in> p a"  
  by (blast intro: sym)

lemma p_D1[dest]:
  "\<lbrakk>a \<in> X; b \<in> p a\<rbrakk> \<Longrightarrow> (a, b) \<in> R" 
  unfolding qproj_def by simp
lemma p_self [intro, simp]:
  "a \<in> X \<Longrightarrow> a \<in> p a"  
    unfolding qproj_def by simp
lemma p_un [simp]:
  "(\<Union>a\<in>X. p a) = X" 
    by blast
lemma p_subset1:
  "(a, b) \<in> R \<Longrightarrow> p a \<subseteq> p b"
  by (meson l_closed local.sym p_D1 p_I1 subsetI trn) 

lemma p_eq1:
  "(a, b) \<in> R \<Longrightarrow> p a = p b"  
  by (auto intro!: p_subset1 intro: sym)

lemma p_equivalence:
  "\<lbrakk>a \<in> X;b \<in> X\<rbrakk> \<Longrightarrow> p a = p b \<longleftrightarrow> (a, b) \<in> R"  
  by (metis p_D1 p_eq1 p_self)

lemma p_meet_eq1:
  "\<lbrakk>a \<in> X; b \<in> X; p a \<inter> p b \<noteq> {}\<rbrakk> \<Longrightarrow> p a = p b" 
  by (metis disjoint_iff p_D1 p_eq1)

lemma p_in_quotient1[intro, simp]:
  "a \<in> X \<Longrightarrow> p a \<in> (X/R)" 
  unfolding quotient_def by blast

lemma elem_ex1:
  "x \<in> X \<Longrightarrow> \<exists>t. x \<in> t \<and> t \<in> (X/R)"  
  using p_self by blast

lemma elem_ex2:
  "p`X = (X/R)" 
  by (simp add: quotient_def UNION_singleton_eq_range qproj_def2)

lemma elem_ex3:
  "t \<in> (X/R) \<Longrightarrow> t \<in> p`X" 
  by (simp add: elem_ex2)

lemma elem_ex4:
  "t \<in> (X/R) \<Longrightarrow> (\<exists>x \<in> X. p x = t)" 
  using elem_ex3 by blast 

lemma elem_un1:
  "t \<in> (X/R) \<Longrightarrow> s \<in> (X/R) \<Longrightarrow> t \<noteq> s \<Longrightarrow>  t \<inter> s = {}"
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

lemma elem_un2:
  "t \<in> (X/R) \<Longrightarrow> s \<in> (X/R) \<Longrightarrow> a \<in> t \<Longrightarrow> a \<in> s \<Longrightarrow> t = s" 
  by (metis disjoint_iff elem_un1)

lemma p_mem_closed[intro]:
  "x \<in> t \<Longrightarrow> t \<in> (X/R) \<Longrightarrow> x \<in> X"
  using elem_ex2 by auto

lemma elem_ex5:
  "t \<in> (X/R) \<Longrightarrow> \<exists>x \<in> X. x \<in> t" 
    using elem_ex4 by blast

lemma proj_hom:
  "set_morphism p X (X/R)" 
  by (simp add: set_morphism.intro) 

lemma proj_hom2:
  "p \<in> set_morphisms X (X/R)"
  by (simp add: proj_hom set_morphism_iff)

lemma proj_epi:
  "set_epimorphism p X (X/R)" 
  by (simp add: elem_ex2 proj_hom set_epimorphism.intro sur_locale.intro)  

lemma proj_epi2:
  "p \<in> set_epimorphisms X (X/R)"
  by (simp add: elem_ex2 set_epimorphisms_def)

lemma rep_ex[dest]:
  "t \<in> X/R \<Longrightarrow> \<exists>x \<in> X. x \<in> t \<and> p x = t" 
  using elem_ex4 by blast

lemma projE:
  "t \<in> X/R \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> Q (p x)) \<Longrightarrow> Q t"
  by blast

lemma sec_rinv:
  "is_right_inv (X/R) p pinv" 
  by (simp add: elem_ex2 qsect_def rinv_is_rinv)

lemma sec_hom:"set_morphism pinv (X/R) X"
  by (simp add: elem_ex2 qsect_def rinv_inv_set_morphisms set_morphismI1)

lemma sec_hom2:"pinv \<in> set_morphisms (X/R) X"
  by (simp add: sec_hom set_morphism_iff)

lemma sec_inj:
  "inj_on pinv (X/R)"
  using rinv_inj sec_rinv by auto

lemma sec_mono:
  "set_monomorphism pinv (X/R) X"
  by (simp add: sec_hom2 sec_inj set_monoI1) 

lemma sec_mono_mem:"pinv \<in> set_monomorphisms (X/R) X"
  by (simp add: sec_mono set_monomorphism_iff)

lemma sec_closed[intro]:
  "t \<in> X/R \<Longrightarrow> pinv t \<in> X"
  by (simp add: elem_ex3 proj_hom2 qsect_def rinv_into_into)

lemma sec_undef:
  "t \<notin> X/R \<Longrightarrow> pinv t = undefined"
  by (simp add: qsect_def rinv_undef)  

lemma compat_factors1:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" 
  shows "\<And>x. x \<in> X \<Longrightarrow> f x =  compose (X/R) f (rinv p X (X/R)) (p x)"
  using compat surj_implies_factors(2)[of p X "X/R" f] elem_ex2 by blast

lemma compat_factors1b:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" 
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = qmap X R f (p x)"
  by(simp add:qsect_def qmap_def;rule surj_implies_factors(2),simp add:elem_ex2,fast elim:compat)

lemma compat_factors1c:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" 
  shows "\<And>x. x \<in> X \<Longrightarrow> f x = compose X (qmap X R f) p x"
  by(simp add:compose_eq[of _ X "qmap X R f" p],blast intro:compat compat_factors1b)


lemma compat_factors1d:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" and set_hom:"f \<in> set_morphisms X Y"
  shows "f = compose X (qmap X R f) p"
proof(rule maps_on_equalityI)
  show "f \<in> maps_on X"
    using hom_memD1 set_hom by blast
  show "compose X (qmap X R f) p \<in> maps_on X"
    by simp
  show "\<And>x. x \<in> X \<Longrightarrow> f x = compose X (qmap X R f) p x"
    using compat compat_factors1c[of f] by blast
qed

lemma compat_factors2:
  assumes compat:"\<And>x y. \<lbrakk>x \<in> X;y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y" and set_hom:"f \<in> set_morphisms X Y"
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
lemma psecE1:"t \<in> X/R \<Longrightarrow> p (pinv t) = t"  
  by (meson is_right_invE1 sec_rinv) 

end

lemma is_eqrelE1:"is_eqrel X R \<Longrightarrow> R \<subseteq> X \<times> X"  by (simp add: is_eqrel_def refl_on_def)
lemma is_eqrelE2:"is_eqrel X R \<Longrightarrow>x \<in> X \<Longrightarrow> (x,x)\<in>R"  by (simp add: is_eqrel_def refl_on_def)
lemma is_eqrelE3:"is_eqrel X R \<Longrightarrow>(x,y)\<in>R \<Longrightarrow> (y,x)\<in>R"  by (meson is_eqrel_def symE) 
lemma is_eqrelE4:"is_eqrel X R \<Longrightarrow>(x,y)\<in>R \<Longrightarrow> (y, z)\<in>R \<Longrightarrow> (x,z)\<in>R"  by (meson is_eqrel_def transE)  

lemma equivalence_relationI:
  assumes "is_eqrel X R"
  shows "equivalence_relation X R"
  apply(rule equivalence_relation.intro)
  using assms is_eqrelE1 apply blast
  apply (meson assms is_eqrelE2)
  apply (meson assms is_eqrelE3)
  by (meson assms is_eqrelE4)

locale kernel_pair_notation=fixes X::"'a set"
begin
definition kernel_pair_object ("Ker'(_')") where
  "kernel_pair_object f \<equiv> {(x, y). x \<in> X \<and> y \<in> X \<and> f x = f y} "
end

locale kernel_pair=set_morphism f X Y for f and X and Y
begin

sublocale kernel_pair_notation  X.

sublocale eqr:equivalence_relation 
  where X=X and R="Ker(f)" unfolding kernel_pair_object_def by(unfold_locales;auto)

definition h::"'a set \<Rightarrow> 'b" 
  where "h \<equiv> qmap X Ker(f) f"

lemma h_eq:
  "\<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> eqr.p x =eqr.p y \<longleftrightarrow> f x = f y"
  unfolding eqr.p_equivalence unfolding kernel_pair_object_def by simp

lemma h_simp[simp]:
  "x \<in> X \<Longrightarrow> h (eqr.p x) = f x" 
  unfolding  h_def using h_eq  eqr.compat_factors1b[of f]  by presburger

lemma quotient_map_hom:
  "h \<in> set_morphisms (X/Ker(f)) Y"
  unfolding h_def qmap_def using eqr.sec_hom2 hom2 mem_hom by blast

lemma ker_pair_ker:
  "Ker(f) = ker_pair X f" 
  unfolding kernel_pair_object_def ker_pair_def by(auto)

lemma kernel_memI:
  "\<lbrakk>x \<in> X; y \<in> X; f x = f y\<rbrakk> \<Longrightarrow> (x,y)\<in> Ker(f)"  
  using h_eq eqr.p_equivalence by force

interpretation quotient_map:set_morphism h "X/Ker(f)" Y  
  unfolding qmap_def h_def using eqr.sec_hom2 hom2 mem_hom set_morphismI1 by blast 

lemma h_inj_on:"inj_on h (X / Ker(f))" unfolding inj_on_def by (metis h_eq h_simp eqr.rep_ex)

sublocale quotient_map:set_monomorphism h "X/Ker(f)" Y
  by (simp add: h_inj_on quotient_map_hom set_monoI1) 

lemma factorization1:
  "x\<in>X \<Longrightarrow> compose X h eqr.p a = f a" 
  by (simp add: compose_def dom)

lemma factorization2[simp]:
  "compose X h eqr.p = f" 
  by (rule ext) (simp add: compose_def dom)

lemma factorization3:
  assumes A0:"g \<in> set_morphisms (X/Ker(f)) Y" and A1:"compose X g eqr.p = f"
  shows "g = h" 
proof
  fix t show "g t = h t"
  proof (cases "t \<in> X/Ker(f)")
    case True
    then obtain x where [simp]: "t = eqr.p x" "x \<in> X" 
      by fast
    then have "g (eqr.p x) = f x"
      by (metis compose_eq A1)
    also have "\<dots> = h (eqr.p x)"
      by simp
    finally show ?thesis
      by simp
  next
    case False then show ?thesis using A0 hom10 quotient_map.dom by fastforce
  qed
qed


end

context equivalence_relation
begin

lemma eqr_eq_proj_ker:
  "R = ker_pair X p"
  apply(auto simp add:ker_pair_def)
  using p_eq1 apply blast
  using p_eq1 by blast

end

section Fold


inductive_set foldSet::"'a set => ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('b set * 'a) set"
  for X :: "'a set" and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" and e :: 'a  where 
    emptyI[intro]:"e \<in> X \<Longrightarrow> ({}, e) \<in> foldSet X f e" |
    insertI[intro]:"\<lbrakk>j \<notin> I; f j y \<in> X; (I, y) \<in> foldSet X f e\<rbrakk> \<Longrightarrow> (insert j I, f j y) \<in> foldSet X f e"

inductive_cases empty_foldSetE[elim!]:"({}, x) \<in> foldSet X f e"

definition fold::"'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> 'a"
  where "fold X f e I = (THE x. (I, x) \<in> foldSet X f e)"

lemma foldSet_closed:"(I, z) \<in> foldSet X f e \<Longrightarrow> z \<in> X"
  by (erule foldSet.cases) auto

lemma Diff1_foldSet:
  "\<lbrakk>(I - {i}, x) \<in> foldSet X f e; i \<in> I; f i x \<in> X\<rbrakk> \<Longrightarrow> (I, f i x) \<in> foldSet X f e"
  by (metis Diff_insert_absorb foldSet.insertI mk_disjoint_insert)

lemma foldSet_imp_finite [simp]: "(I, x) \<in> foldSet X f e \<Longrightarrow> finite I"
  by (induct set: foldSet) auto

lemma finite_imp_foldSet:
  "\<lbrakk>finite I; e \<in> X; (\<And>i x. \<lbrakk>i \<in> I; x \<in> X\<rbrakk> \<Longrightarrow> f i x \<in> X)\<rbrakk>   \<Longrightarrow> \<exists>x. (I, x) \<in> foldSet X f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert i F)
  then obtain y where y: "(F, y) \<in> foldSet X f e" by auto
  with insert have "y \<in> X" by (auto dest: foldSet_closed)
  with y and insert have "(insert i F, f i y) \<in> foldSet X f e"
    by (intro foldSet.intros) auto
  then show ?case ..
qed

locale LCD =
  fixes B :: "'b set" and X :: "'a set" and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>" 70)
  assumes left_commute: "\<lbrakk>x \<in> B; y \<in> B; z \<in> X\<rbrakk> \<Longrightarrow> f x (f y z) = f y (f x z)" and 
		    f_closed [simp, intro!]: "!!x y. \<lbrakk>x \<in> B; y \<in> X\<rbrakk> \<Longrightarrow> f x y \<in> X"

lemma (in LCD) foldSet_closed [dest]: "(A, z) \<in> foldSet X f e \<Longrightarrow> z \<in> X"
  by (erule foldSet.cases) auto

lemma (in LCD) Diff1_foldSet:
  "\<lbrakk>(A - {x}, y) \<in> foldSet X f e; x \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow>  (A, f x y) \<in> foldSet X f e"
  by (meson Diff1_foldSet f_closed local.foldSet_closed subsetCE)

lemma (in LCD) finite_imp_foldSet:
  "\<lbrakk>finite A; A \<subseteq> B; e \<in> X\<rbrakk> \<Longrightarrow> \<exists>x. (A, x) \<in> foldSet X f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSet X f e" by auto
  with insert have "y \<in> X" by auto
  with y and insert have "(insert x F, f x y) \<in> foldSet X f e"
    by (intro foldSet.intros) auto
  then show ?case ..
qed


lemma (in LCD) foldSet_determ_aux:
  assumes "e \<in> X" and A: "card A < n" "A \<subseteq> B" "(A, x) \<in> foldSet X f e" "(A, y) \<in> foldSet X f e"
  shows "y = x"
  using A
proof (induction n arbitrary: A x y)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then consider "card A = n" | "card A < n"
    by linarith
  then show ?case
  proof cases
    case 1
    show ?thesis
      using foldSet.cases [OF \<open>(A,x) \<in> foldSet X (\<cdot>) e\<close>]
    proof cases
      case 1
      then show ?thesis
        using \<open>(A,y) \<in> foldSet X (\<cdot>) e\<close> by auto
    next
      case (2 x' A' y')
      note A' = this
      show ?thesis
        using foldSet.cases [OF \<open>(A,y) \<in> foldSet X (\<cdot>) e\<close>]
      proof cases
        case 1
        then show ?thesis
          using \<open>(A,x) \<in> foldSet X (\<cdot>) e\<close> by auto
      next
        case (2 x'' A'' y'')
        note A'' = this
        show ?thesis
        proof (cases "x' = x''")
          case True
          show ?thesis
          proof (cases "y' = y''")
            case True
            then show ?thesis
              using A' A'' \<open>x' = x''\<close> by (blast elim!: equalityE)
          next
            case False
            then show ?thesis
              using A' A'' \<open>x' = x''\<close>
              by (metis \<open>card A = n\<close> Suc.IH Suc.prems(2) card_insert_disjoint foldSet_imp_finite insert_eq_iff insert_subset lessI)
          qed
        next
          case False
          then have *: "A' - {x''} = A'' - {x'}" "x'' \<in> A'" "x' \<in> A''"
            using A' A'' by fastforce+
          then have "A' = insert x'' A'' - {x'}"
            using \<open>x' \<notin> A'\<close> by blast
          then have card: "card A' \<le> card A''"
            using A' A'' * by (metis card_Suc_Diff1 eq_refl foldSet_imp_finite)
          obtain u where u: "(A' - {x''}, u) \<in> foldSet X (\<cdot>) e"
            using finite_imp_foldSet [of "A' - {x''}"] A' Diff_insert \<open>A \<subseteq> B\<close> \<open>e \<in> X\<close> by fastforce
          have "y' = f x'' u"
            using Diff1_foldSet [OF u] \<open>x'' \<in> A'\<close> \<open>card A = n\<close> A' Suc.IH \<open>A \<subseteq> B\<close> by auto
          then have "(A'' - {x'}, u) \<in> foldSet X f e"
            using "*"(1) u by auto
          then have "y'' = f x' u"
            using A'' by (metis * \<open>card A = n\<close> A'(1) Diff1_foldSet Suc.IH \<open>A \<subseteq> B\<close>
                card card_Suc_Diff1 card_insert_disjoint foldSet_imp_finite insert_subset le_imp_less_Suc)
          then show ?thesis
            using A' A''
            by (metis \<open>A \<subseteq> B\<close> \<open>y' = x'' \<cdot> u\<close> insert_subset left_commute local.foldSet_closed u)
        qed
      qed
    qed
  next
    case 2 with Suc show ?thesis by blast
  qed
qed

lemma (in LCD) foldSet_determ:
  "\<lbrakk>(A, x) \<in> foldSet X f e; (A, y) \<in> foldSet X f e; e \<in> X; A \<subseteq> B\<rbrakk>
  \<Longrightarrow> y = x"
  by (blast intro: foldSet_determ_aux [rule_format])

lemma (in LCD) fold_equality:
  "\<lbrakk>(A, y) \<in> foldSet X f e; e \<in> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> fold X f e A = y"
  by (unfold fold_def) (blast intro: foldSet_determ)

lemma fold_empty [simp]:
  "e \<in> X \<Longrightarrow> fold X f e {} = e"
  by (unfold fold_def) blast

lemma (in LCD) fold_insert_aux:
  "\<lbrakk>x \<notin> A; x \<in> B; e \<in> X; A \<subseteq> B\<rbrakk>
    \<Longrightarrow> ((insert x A, v) \<in> foldSet X f e) \<longleftrightarrow> (\<exists>y. (A, y) \<in> foldSet X f e \<and> v = f x y)"
  apply auto
  by (metis Diff_insert_absorb f_closed finite_Diff foldSet.insertI foldSet_determ foldSet_imp_finite insert_subset local.finite_imp_foldSet local.foldSet_closed)

lemma (in LCD) fold_insert:
  assumes "finite A" "x \<notin> A" "x \<in> B" "e \<in> X" "A \<subseteq> B"
  shows "fold X f e (insert x A) = f x (fold X f e A)"
proof -
  have "(THE v. \<exists>y. (A, y) \<in> foldSet X (\<cdot>) e \<and> v = x \<cdot> y) = x \<cdot> (THE y. (A, y) \<in> foldSet X (\<cdot>) e)"
    by (rule the_equality) (use assms fold_def fold_equality fold_def finite_imp_foldSet in \<open>metis+\<close>)
  then show ?thesis
    unfolding fold_def using assms by (simp add: fold_insert_aux)
qed

lemma (in LCD) fold_closed [simp]:
  "\<lbrakk>finite A; e \<in> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> fold X f e A \<in> X"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: fold_insert)
qed

lemma (in LCD) fold_commute:
  "\<lbrakk>finite A; x \<in> B; e \<in> X; A \<subseteq> B\<rbrakk> \<Longrightarrow>
   f x (fold X f e A) = fold X f (f x e) A"
  by (induct set: finite) (auto simp add: left_commute fold_insert)

section Fold

lemma set_morphisms_empty:"\<exists>!f. f \<in> set_morphisms {} Y"
  by (simp add: hom1)


definition "seq X a f n \<equiv> {x \<in> set_morphisms {..Suc n} X. x 0 = a \<and> (\<forall>k \<in> {..<Suc n}. x (Suc k) = f (x k))}"
definition "inductive_seq X a f n \<equiv> (THE x. x \<in> seq X a f n)"
definition "ind_seq X a f \<equiv> (\<lambda>n \<in> Nats. inductive_seq X a f n n)"



lemma set_morphism_insert:
  assumes A0:"f \<in> set_morphisms A Y" and A1:"a \<notin> A" and A2:"y \<in> Y"
  defines "g \<equiv> (\<lambda>x \<in> (insert a A). if x=a then y else f x)"
  shows "g \<in> set_morphisms (insert a A) Y"
  using assms unfolding set_morphisms_def by(auto)

lemma suc_insert_lol:
  assumes A0:"f \<in> set_morphisms {..n} Y" and A1:"n \<in> Nats" and A2:"y \<in> Y"
  defines "g \<equiv> (\<lambda>x \<in> {..(Suc n)}. if x \<in>{..n} then f x else y)"
  shows "g \<in> set_morphisms {..(Suc n)} Y"
  using assms unfolding set_morphisms_def by auto



lemma iseq_ex0:
  assumes A0:"f \<in> set_morphisms X X" and A1:"a \<in> X"
  defines "x \<equiv> (\<lambda>i \<in>{..Suc 0}. (if i=0 then a else (f a)))"
  shows "x \<in> set_morphisms {..Suc 0} X" and "x 0 = a" and "(\<forall>k \<in> {..<Suc 0}. x (Suc k) = f (x k))" and
        "x \<in> seq X a f 0" and  "\<And>y. y \<in> seq X a f 0 \<Longrightarrow> y = x" and "\<exists>!x. x \<in> seq X a f 0" and
        "inductive_seq X a f 0 = x"
proof-
  obtain B0:"{..<Suc 0} = {0::nat}" and B1:"{.. Suc 0} = {0,1}"
    by (simp add: atMost_Suc insert_commute lessThan_atLeast0)
  obtain B2:"x 0 = a" and B3:"x 1 = f a"
    by (simp add: x_def)
  show B4:"x \<in> set_morphisms {.. Suc 0} X"
    unfolding x_def set_morphisms_def dom_def using A1 A0 hom9 by force
  show B5:"x 0 = a"
    using B2 by auto
  show B6:"(\<forall>k \<in> {..<Suc 0}. x (Suc k) = f (x k))"
    by (metis B0 B3 B5 One_nat_def singletonD)
  show B7:"x \<in> seq X a f 0"
    by (simp add: B4 B5 B6 seq_def)
  show B8:"\<And>y. y \<in> seq X a f 0 \<Longrightarrow> y = x"
  proof-
    fix y assume A2:"y \<in> seq X a f 0"
    then obtain "y \<in> set_morphisms {..Suc 0} X" and "y 0 = a" and "\<forall>k \<in> {..<Suc 0}. y (Suc k) = f (y k)"
      by (simp add: seq_def)
    then show "y = x"
      using fun_eqI[of y "{..Suc 0}" X x X]  by (metis B0 B1 B3 B4 B5 One_nat_def insertE singleton_iff)
  qed
  show "\<exists>!x. x \<in> seq X a f 0"
    using B7 B8 by auto
  show "inductive_seq X a f 0 = x"
    unfolding inductive_seq_def  using B7 B8 by blast
qed


lemma iseqrestric:
  assumes A0:"f \<in> set_morphisms X X"  and A1:"a \<in> X" and A2:"n \<in> Nats" and A3:"x \<in> seq X a f (Suc n)"
  shows "(\<lambda>i \<in> {..Suc n}. x i) \<in> seq X a f n"
proof-
  let ?r="(\<lambda>i \<in> {..Suc n}. x i)"
  obtain A4:"x \<in> set_morphisms {..Suc (Suc n)} X" and A6:"x 0 = a" and A7:"\<forall>k \<in> {..<Suc (Suc n)}. x (Suc k) = f (x k)"
    using A3 by (simp add: seq_def)
  have B0:"?r \<in> set_morphisms {..Suc n} X"
    using A4 unfolding set_morphisms_def by(auto)
  have B1:"?r 0 = a"
    by (simp add: A6)
  have B2:"\<forall>k \<in> {..<Suc n}. ?r (Suc k) = f (?r k)"
    using A7 by auto
  show ?thesis
    unfolding seq_def using B0 B1 B2 by blast
qed
  
lemma iseq_ex1:
  assumes A0:"f \<in> set_morphisms X X" and A1:"a \<in> X" and A2:"n \<in> Nats" and A3:"\<exists>!x. x \<in> seq X a f n"
  shows "\<exists>!x. x \<in> seq X a f (Suc n)" and "inductive_seq X a f (Suc n) \<in> seq X a f (Suc n)"
proof-
  obtain y where A4:"y \<in> seq X a f n" using A3 by auto
  then obtain A5:"y \<in> set_morphisms {..Suc n} X" and A6:"y 0 = a" and A7:"\<forall>k \<in> {..<Suc n}. y (Suc k) = f (y k)"
    by (simp add: seq_def)
  define x where "x \<equiv> (\<lambda>i \<in>{..Suc (Suc n)}. (if i \<in> {..Suc n} then y i else (f (y (Suc n)))))"
  have B0:"\<forall>k \<in> {..<Suc (Suc n)}. x k = y k"
    using x_def by auto
  have B1:"y (Suc n) \<in> X"
    using A5 hom9 by fastforce
  have B2:"x (Suc (Suc n)) = f (y (Suc n))"
    by (simp add: x_def)
  have B3:"f(y (Suc n)) \<in> X"
    by (meson A0 B1 hom9)
  have B4:"compose {..Suc n} f y \<in> set_morphisms {..Suc n} X"
    using A0 A5 hom2 by blast
  have B5:"{..Suc (Suc n)} = insert (Suc (Suc n)) {..<Suc (Suc n)}"
    using lessThan_Suc lessThan_Suc_atMost by auto 
  have B6:"\<forall>i \<in> {..Suc n}. x (Suc i) = f (x i)"
    by (metis A7 B0 B2 lessThan_Suc_atMost lessThan_iff less_Suc_eq less_Suc_eq_0_disj)
  have B7:"x 0 = a"
    by (simp add: A6 B0)
  have B8:"x \<in> set_morphisms {..Suc (Suc n)} X"
    unfolding x_def using B3 A5 suc_insert_lol[of y "Suc n" X "f (y (Suc n))"] by (simp add: set_morphisms_def)
  have B9:"\<forall>k \<in> {..<Suc n}. x (Suc k) = f (x k)"
    by (simp add: B6)
  have P0:"x \<in> seq X a f (Suc n)"
    unfolding seq_def by (simp add: B6 B7 B8)
  have P1:"\<And>z. z \<in> seq X a f (Suc n) \<Longrightarrow> z = x"
  proof-
    fix z assume A4:"z \<in> seq X a f (Suc n)"
    then obtain "(\<lambda>i \<in> {..Suc n}. z i) \<in> seq X a f n" and "(\<lambda>i \<in> {..Suc n}. x i) \<in> seq X a f n"
      by (simp add: A0 A1 P0 assms(3) iseqrestric)
    then obtain B10:"(\<lambda>i \<in> {..Suc n}. x i) = (\<lambda>i \<in> {..Suc n}. z i)"
      using A3 by auto
    then obtain B11:"\<forall>k \<in> {..Suc n}. z k = x k"
      by (metis restrict_apply1)
    obtain B12:"x (Suc (Suc n)) = f (y (Suc n))" and B13:"y (Suc n) = x (Suc n)" and B14:"z (Suc (Suc n)) = f (x (Suc n))"
      by (metis (mono_tags, lifting) A4 B0 B11 B6 insertI1 lessThan_Suc lessThan_Suc_atMost mem_Collect_eq seq_def)
    obtain B15:"x (Suc (Suc n)) = z (Suc (Suc n))"
      by (simp add: B13 B14 B2)
    have "\<And>k. k \<in> {..Suc (Suc n)} \<Longrightarrow> z k = x k"
    proof-
      fix k assume A5:"k \<in> {..Suc (Suc n)}" show "z k = x k"
      proof(cases "k=Suc(Suc n)")
        case True  then show ?thesis using B15 by auto
      next
        case False then obtain "k \<in> {..Suc n}"  using A5 by force
        then show ?thesis using B11 by auto
      qed
    qed
    then show "z = x"
      by (metis (mono_tags, lifting) A4 B8 fun_eqI mem_Collect_eq seq_def)
  qed
  show "\<exists>!x. x \<in> seq X a f (Suc n)"
    using P0 P1 by blast 
  then show "inductive_seq X a f (Suc n) \<in> seq X a f (Suc n)"
    unfolding inductive_seq_def using theI'[of "\<lambda>z. z \<in> seq X a f (Suc n)"] by auto
qed

lemma iseq_ex2:
  assumes A0:"f \<in> set_morphisms X X" and A1:"a \<in> X" 
  shows "\<exists>!x. x \<in> seq X a f n" 
proof(induct n)
  case 0
  then show ?case
    by (simp add: A0 A1 iseq_ex0(6) iseq_ex1) 
next
  case (Suc n)
  also have "n \<in> Nats"
    by (metis of_nat_id of_nat_in_Nats)
  then show ?case using A0 A1 iseq_ex1[of f X a n] using calculation by blast
qed


lemma iseq_ex3:"f \<in> set_morphisms X X \<Longrightarrow> a \<in> X \<Longrightarrow> inductive_seq X a f n \<in> seq X a f n" 
  unfolding inductive_seq_def using iseq_ex2[of f X a n] theI'[of "\<lambda>z. z \<in> seq X a f n"] by auto

lemma iseq_ex4:
  assumes A0:"f \<in> set_morphisms X X" and A1:"a \<in> X" and A2:"n \<in> Nats" and A3:"x = inductive_seq X a f n"
  shows "x \<in> set_morphisms {..Suc n} X" and "x 0 = a" and A7:"\<forall>k \<in> {..<Suc n}. x (Suc k) = f (x k)"
proof-
  obtain B0:"inductive_seq X a f n \<in> seq X a f n"
    by (simp add: A0 A1 iseq_ex3)
  then obtain B1:"x \<in> seq X a f n"
    by (simp add: A3)
  then show "x \<in> set_morphisms {..Suc n} X" and "x 0 = a" and A7:"\<forall>k \<in> {..<Suc n}. x (Suc k) = f (x k)"
    by (simp_all add: seq_def)
qed

lemma iseq_rest:
  assumes A0:"f \<in> set_morphisms X X" and A1:"a \<in> X" and A2:"n \<in> Nats" and A3:"m \<in> Nats" and A4:"n \<le> m"
  shows "(\<lambda>k \<in> {..Suc n}. (inductive_seq X a f m) k) = inductive_seq X a f n "
proof-
  let ?x="(inductive_seq X a f m)" let ?r="(\<lambda>k \<in> {..Suc n}. (inductive_seq X a f m) k) "
  let ?y="inductive_seq X a f n "
  obtain B0:"?x \<in> set_morphisms {..Suc m} X" and B1:"?x 0 = a" and B2:"\<forall>k \<in> {..<Suc m}. ?x (Suc k) = f (?x k)" and
         B3:"?y \<in> set_morphisms {..Suc n} X" and B4:"?y 0 = a" and B5:"\<forall>k \<in> {..<Suc n}. ?y (Suc k) = f (?y k)"
    by (metis A0 A1 A2 A3 A7 iseq_ex4(1) iseq_ex4(2)) 
  have B6:"{..Suc n} \<subseteq> {..Suc m}"
    by (simp add: A4)
  have B7:"?r \<in> set_morphisms {..Suc n} X" 
    using B0 B6 unfolding set_morphisms_def by(auto)
  obtain B8:"?r 0 = a" and B9:"\<forall>k \<in> {..<Suc n}. ?r (Suc k) = f (?r k)"
    using A4 B2 B1 by force
  then obtain "?r \<in> seq X a f n"
    by (simp add: B7 seq_def)
  then show "?r = ?y"
    by (metis A0 A1 iseq_ex2 iseq_ex3)
qed

lemma ind_seq_props:
  assumes A0:"f \<in> set_morphisms X X" and A1:"a \<in> X" 
  shows "(ind_seq X a f) \<in> set_morphisms Nats X" and 
        "(ind_seq X a f) 0 = a" and 
        "\<And>n. n \<in> Nats \<Longrightarrow> (ind_seq X a f) (Suc n) = f ((ind_seq X a f) n)"
proof-
  show  "(ind_seq X a f) \<in> set_morphisms Nats X"
    unfolding set_morphisms_def ind_seq_def using assms by(auto;meson atMost_iff hom9 iseq_ex4(1) le_Suc_eq le_eq_less_or_eq)
  show "(ind_seq X a f) 0 = a"
    by (metis (no_types, lifting) A0 A1 Nats_0 ind_seq_def iseq_ex4(2) restrict_apply)
  show "\<And>n. n \<in> Nats \<Longrightarrow> (ind_seq X a f) (Suc n) = f ((ind_seq X a f) n)"
  proof-
    fix n assume n:"(n::nat) \<in> Nats" then obtain "(Suc n) \<in> Nats"
      by (metis of_nat_id of_nat_in_Nats)
    then show "(ind_seq X a f) (Suc n) = f ((ind_seq X a f) n)"  unfolding ind_seq_def 
      using n  by (smt (verit, best) A0 A1 A7 Suc_leD atMost_iff eq_imp_le iseq_rest lessThan_Suc_atMost restrict_apply)
  qed
qed


section Magmas
subsection \<open>Magma Locale\<close>
definition magma_stable :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "magma_stable X f A \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A. f x y \<in> A) \<and> (A \<subseteq> X)"


lemma mamga_stableI:"A \<subseteq> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> f x y \<in> A) \<Longrightarrow> magma_stable X f A" by (simp add: magma_stable_def)
lemma magma_stableE1: "magma_stable X f A \<Longrightarrow> A \<subseteq> X" by (simp add: magma_stable_def)
lemma magma_stableE2:  "magma_stable X f A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x y \<in> A" by (simp add:magma_stable_def)
lemma magma_stable_int_closed:"(\<And>A. A \<in> \<A> \<Longrightarrow> magma_stable X f A) \<Longrightarrow> \<A> \<noteq> {} \<Longrightarrow> magma_stable X f (\<Inter>\<A>)" unfolding magma_stable_def by(blast)

locale magma=
  fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) 
  assumes closed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> X" 
begin
definition opposite_law where "opposite_law \<equiv> \<lambda>x. \<lambda>y. f y x"
definition stable where  "stable A \<equiv> magma_stable X f A"
definition commutes where  "commutes A B \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B. a \<cdot> b = b \<cdot> a)"

definition centralizer where "centralizer E \<equiv> {x \<in> X. \<forall>y \<in> E. commutes {x} {y}}"
definition center where "center = centralizer X"

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

lemma commutesI:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a) \<Longrightarrow> commutes A B"  using commutes_def by auto
lemma centralizer_memI1:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> E \<Longrightarrow> commutes {x} {y}) \<Longrightarrow> x \<in> centralizer E" by (simp add: centralizer_def)
lemma centralizer_memI2:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> E \<Longrightarrow> x \<cdot> y = y \<cdot> x) \<Longrightarrow> x \<in> centralizer E"  by (simp add: centralizer_memI1 commutes_def) 
lemma centralizer_memI3:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> E \<Longrightarrow> y \<cdot> x = x \<cdot> y) \<Longrightarrow> x \<in> centralizer E"  by (simp add: centralizer_memI1 commutes_def) 
lemma centralizer_memD:"x \<in> centralizer E \<Longrightarrow> (\<And>a. a \<in> E \<Longrightarrow>  a \<cdot> x = x \<cdot> a)"  by (simp add: centralizer_def commutes_def)
lemma center_memI1:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow>  commutes {x} {y}) \<Longrightarrow> x \<in> center"  using center_def centralizer_memI1 by auto
lemma center_memI2:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow>  x \<cdot> y = y \<cdot> x) \<Longrightarrow> x \<in> center"  using center_def centralizer_memI2 by auto  
lemma center_memI3:"x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow>  y \<cdot> x = x \<cdot> y) \<Longrightarrow> x \<in> center"  by (simp add: center_memI2) 
lemma center_memD:"x \<in> center \<Longrightarrow> (\<And>a. a \<in> X \<Longrightarrow>  a \<cdot> x = x \<cdot> a)"  using center_def centralizer_memD by blast  


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
lemma centralizer_antitone:"A \<subseteq> B \<Longrightarrow> centralizer B \<subseteq> centralizer  A" unfolding centralizer_def by blast
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
lemma r_trans_app:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> r_trans x y = l_trans y x" unfolding l_trans_def r_trans_def by(auto)

lemma l_trans_hom:"\<And>a. a \<in> X \<Longrightarrow> l_trans a \<in> set_morphisms X X" by (simp add: closed hom_memI1 l_trans_def)
lemma r_trans_hom:"\<And>a. a \<in> X \<Longrightarrow> r_trans a \<in> set_morphisms X X" by (simp add: closed hom_memI1 r_trans_def)


lemma l_trans_und:"\<And>a. a \<notin> X \<Longrightarrow> l_trans a = undefined" by (simp add: closed hom_memI1 l_trans_def)
lemma r_trans_und:"\<And>a. a \<notin> X \<Longrightarrow> r_trans a = undefined" by (simp add: closed hom_memI1 r_trans_def)


lemma l_trans_hom_mem:"l_trans \<in> set_morphisms X (set_morphisms X X)"  using hom_memI1 l_trans_hom l_trans_und by auto
lemma r_trans_hom_mem:"r_trans \<in> set_morphisms X (set_morphisms X X)"  using hom_memI1 r_trans_hom r_trans_und by auto

lemma id_elem_linj:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> inj_on (l_trans e) X " unfolding inj_on_def l_trans_def id_elem_def by(auto)
lemma id_elem_rinj:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> inj_on (r_trans e) X " unfolding inj_on_def r_trans_def id_elem_def by(auto)

inductive_set magma_generated::"'a set \<Rightarrow> 'a set" for A where
 iso:"a \<in> A \<Longrightarrow> a \<in> magma_generated A"
 |opc:"a \<in> magma_generated A \<Longrightarrow> b \<in> magma_generated A \<Longrightarrow> a\<cdot>b \<in> magma_generated A"

lemma generate_into: "a \<in> magma_generated (X \<inter> A) \<Longrightarrow> a \<in> X"  
  apply (induction rule: magma_generated.induct)  
   apply simp by (simp add: closed)

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

definition set_to_list :: "'b set \<Rightarrow> 'b list"
  where "set_to_list s = (SOME l. set l = s)"

lemma set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

definition list_of_set :: "'a set \<Rightarrow> 'a list" where
  "list_of_set A = (if finite A then SOME xs. distinct xs \<and> set xs = A else [])"

lemma list_of_set:
  assumes "finite A"
  shows   "set (list_of_set A) = A" "distinct (list_of_set A)"
proof -
  from assms have "\<exists>xs. set xs = A \<and> distinct xs"
    by (rule finite_distinct_list)
  from someI_ex[OF this] show "set (list_of_set A) = A" "distinct (list_of_set A)"
    using assms
    apply (metis (no_types, lifting) Eps_cong list_of_set_def)
    by (metis (no_types, lifting) Eps_cong \<open>set (SOME x::'a list. set x = (A::'a set) \<and> distinct x) = A \<and> distinct (SOME x::'a list. set x = A \<and> distinct x)\<close> assms list_of_set_def)
qed



(*definition "act_finprod I x \<equiv> fold (f \<circ> x) (set_to_list I) "*)
definition act_finprod:: "'b list \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where "act_finprod L x \<equiv> List.foldr (f \<circ> x) L "
definition list_finprod::"'b list \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "list_finprod L x \<equiv> act_finprod (tl L) x (x (hd L))"
definition finprod :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "finprod I x \<equiv> list_finprod (set_to_list I) x"
definition fprod::"'b::wellorder set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "fprod I x \<equiv> list_finprod (sorted_list_of_set I) x"
(*
lemma fprod_ins: 
  fixes I::"'b::wellorder set"
  assumes A0:"finite I" and A1:"x \<in> set_morphisms I X" and A2:"I \<noteq> {}" 
  shows "fprod I x \<in> X"
proof-
  obtain L L' where B0:"L=sorted_list_of_set I" and B1:"L'=sorted_list_of_set (I - {Min I})"
    by simp
  obtain \<beta> where B2:"\<beta> = Min I"
    by simp
  have B3:"\<beta> = hd L"
    by (simp add: A0 A2 B0 B2 sorted_list_of_set_nonempty)
  have B4: "L = Min I # sorted_list_of_set (I - {Min I})"
    using A0 A2 B0 sorted_list_of_set_nonempty by blast
  have B5:"\<beta> # L' = L"
    using B1 B2 B4 by blast
  have B5:"fprod I x = List.foldr (f \<circ> x) L' (x \<beta>)"
    by (metis B0 B1 B3 B4 list.sel(3) magma.act_finprod_def magma.fprod_def magma.list_finprod_def magma_axioms)
  have B6:"sorted L'"
    using B1 sorted_list_of_set.sorted_sorted_key_list_of_set by blast
  have B7:"foldr ((\<cdot>) \<circ> x) [] (x \<beta>) \<in> X"
    by (metis A0 A1 A2 B2 Min_in foldr.simps(1) hom9 id_apply)
  
  have B6:" List.foldr (f \<circ> x) L (x \<beta>) \<in> X"
  proof(induct L)
    case Nil
    then show ?case using B7 by auto
  next
    case (Cons a L)
    then show ?case 

  qed
    
  also have "... =  (f \<circ> x) \<beta> List.foldr (f \<circ> x) L"
  have B6:"... = "
  have B2:"\<beta> = hd L"
    by (metis A0 A1 A4 B1 Collect_mem_eq Least_Min all_not_in_conv list.sel(1))
  define L' where "L'=tl L" 
  have B3:"L'=(sorted_list_of_set (I - {Min I}))"
    by (simp add: B1 L'_def)
  have B1:"fprod I x = List.fold (f \<circ> x) L' (x \<beta>)"
    by (simp add: B0 B2 L'_def act_finprod_def fprod_def list_finprod_def)
  have B2:"f (x \<beta>) (fprod I x) = f (x \<beta>)  (List.fold (f \<circ> x) L' (x \<beta>)) "
    by (simp add: B1)
  also have B3:"... =  (f \<circ> x) \<beta>  (List.fold (f \<circ> x) L' (x \<beta>))"
    by simp
  also have B4:"... = ()"

lemma fprod_closed:
  assumes A0:"finite I" and A1:"I \<noteq> {}" and A2:"x \<in> set_morphisms I X" 
  shows "fprod I x \<in> X"
proof-
  obtain L where B0:"L= sorted_list_of_set I "
    by simp
  define L' where "L'=butlast L" 
  define \<beta> where "\<beta>=last L"
  have B1:"fprod I x = List.fold ((\<cdot>) \<circ> x) L' (x \<beta>)"
    by (simp add: B0 L'_def \<beta>_def act_finprod_def fprod_def list_finprod_def)
  
  (* List.fold ((\<cdot>) \<circ> x) (butlast (sorted_list_of_set I)) (x (last (sorted_list_of_set I))) \<in> X*)


*)
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

sublocale magma \<subseteq> opposite:magma X "\<lambda>x. \<lambda>y. f y x"  by(unfold_locales,simp add: closed)

context magma 
begin
lemma lr_trans_dual:"l_trans = opposite.r_trans"  using l_trans_def opposite.r_trans_def by presburger
lemma rl_trans_dual:"r_trans = opposite.l_trans"  using r_trans_def opposite.l_trans_def by presburger

end

interpretation ex1a:magma "Pow X" "(\<lambda>A. \<lambda>B. A \<union> B)" apply(unfold_locales) by simp
interpretation ex1b:magma "Pow X" "(\<lambda>A. \<lambda>B. A \<inter> B)" apply(unfold_locales) by blast
interpretation ex2a:magma "UNIV::nat set" "(\<lambda>x. \<lambda>y. x+y)"  by (simp add: magma.intro)
interpretation ex2b:magma "UNIV::nat set" "(\<lambda>x. \<lambda>y. x*y)"  by (simp add: magma.intro)


subsection \<open>Submagma Locale\<close>
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


lemma submamga_trans[trans]: 
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


subsection \<open>Magma Homomorphism Locale\<close>


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


lemma imag_comp2:"magma_stable X (\<cdot>) A \<Longrightarrow> x \<in> f ` A \<Longrightarrow> y \<in> f ` A \<Longrightarrow> x \<star> y \<in> f ` A"
proof-
  fix x y assume A0:"magma_stable X (\<cdot>) A" and A1:"x \<in> f ` A" and A2:"y \<in> f `A" 
  then obtain a b where A3:"a \<in> A" and  A4:"b \<in> A" and A5:"x = f a" and A6:"y = f b"
    by blast
  obtain A7:"A \<subseteq> X" 
    using A0 unfolding magma_stable_def by auto
  then obtain A8:"y \<in> Y" and A8:"x \<in> Y" and A9:"a \<in> X" and A10:"b \<in> X"
    using A3 A4 A5 A6 by blast
  obtain A11:"a\<cdot>b \<in> A" and A12:"a \<cdot> b \<in> X"
    using A0 A3 A4 unfolding magma_stable_def by auto
  then obtain A13:"f (a \<cdot>b) \<in> f `A" and A14: "f (a \<cdot> b) = (f a)\<star>(f b)"
    using A10 A11 A9 cmp by blast
  then show "x \<star> y \<in> f ` A"
    using A5 A6 by auto 
qed

lemma stable_image:
  assumes A0:"magma_stable X (\<cdot>) A"
  shows "magma_stable Y (\<star>) (f`A)"
proof-
  have B0:"f`A \<subseteq> Y"
    by (metis assms cod image_subset_iff magma_stableE1 subsetD)
  have B1:"\<And>x y. x \<in> f ` A \<Longrightarrow> y \<in> f ` A \<Longrightarrow> x \<star> y \<in> f ` A"
    using A0 imag_comp2 by(auto)
  show ?thesis 
    using mamga_stableI B0 B1 by auto
qed


lemma magma_stable_vimage:"magma_stable Y (\<star>) B \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow>magma_stable X (\<cdot>) (vimage f B)" 
proof-
  assume A0:"magma_stable Y (\<star>) B " and A1:" (vimage f B) \<subseteq> X"
  show "magma_stable X (\<cdot>) (vimage f B)"
    apply(rule mamga_stableI)
    apply (simp add: A1)
    using A0 A1 cmp magma_stable_def subsetD by fastforce
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

sublocale ker:kernel_pair f X Y  by (simp add: kernel_pair_def set_morphism_axioms)
definition kernel where "kernel \<equiv> ker.kernel_pair_object f"
notation ker.kernel_pair_object ("R'(_')")
sublocale im:submagma "f`X" Y "(\<star>)" by (simp add: dom.closed dom.magma_axioms submagma1 submagmaI)

lemma kernel_ref:"refl_on X kernel"  by (simp add: kernel_def refl_on_def)
lemma kernel_sym:"sym kernel"   by (simp add: ker.eqr.sym kernel_def symI) 
lemma kernel_trn:"trans  kernel" unfolding kernel_def using ker.eqr.trn transI  by auto
lemma eqr_kernel:"is_eqrel X  kernel" unfolding is_eqrel_def using kernel_ref kernel_sym kernel_trn by auto

end

subsection \<open>Magma Epimorphism Locale\<close>

locale magma_epimorphism=set_epimorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
sublocale ker:kernel_pair f X Y  by (simp add: kernel_pair_def set_morphism_axioms)
notation ker.kernel_pair_object ("R'(_')")


end
 
  


subsection \<open>Magma Monomorphism Locale\<close>

locale magma_monomorphism=set_monomorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
end


subsection \<open>Magma Isomorphism Locale\<close>

locale magma_isomorphism=set_isomorphism f X Y+ dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism by(unfold_locales,simp add: cmp)
sublocale magma_epimorphism by(unfold_locales,simp add: cmp)
sublocale magma_monomorphism by(unfold_locales,simp add: cmp)
end

     
subsection \<open>Quotient Magma Locale\<close>

definition l_cong::"'a set\<Rightarrow>('a\<Rightarrow>'b\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where
  "l_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f a x, f a y) \<in> R)"

definition r_cong::"'a set\<Rightarrow>('b\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where
  "r_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f x a, f y a) \<in> R)"

definition cong::"'a set\<Rightarrow>('a\<Rightarrow>'a\<Rightarrow>'a)\<Rightarrow>('a\<times>'a) set \<Rightarrow> bool" where
  "cong X f R \<equiv> (\<forall>(x1, x2) \<in> R. \<forall>(y1, y2) \<in> R.  (f x1 y1, f x2 y2) \<in> R)"

lemma l_congI1:
  "(\<And>a x y. a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R) \<Longrightarrow> l_cong X f R" 
  using l_cong_def by fastforce

lemma r_congI1:
  "(\<And>a x y. a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R) \<Longrightarrow> r_cong X f R"
  using r_cong_def by fastforce

lemma congI1:
  "(\<And>x1 x2 y1 y2. (x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (f x1 y1 , f x2 y2) \<in> R) \<Longrightarrow> cong X f R"
  using cong_def by fastforce

lemma congD1:
  "cong X f R \<Longrightarrow> (x1,x2)\<in>R \<Longrightarrow> (y1,y2) \<in> R \<Longrightarrow> (f x1 y1, f x2 y2) \<in> R" 
  using cong_def by fastforce

lemma l_congD1:
  "l_cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R" 
  using l_cong_def by fastforce

lemma r_congD1:
  "r_cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R" 
  using r_cong_def by fastforce

lemma congDR:
  "refl_on X R \<Longrightarrow> cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f x a, f y a) \<in> R" 
proof-  
  assume A0:"refl_on X R" "cong X f R" "a \<in> X" "(x,y)\<in>R"  
  then have B0:"(a,a)\<in>R"   
    by (simp add: refl_onD)  
  then show "(f x a, f y a) \<in> R"  
    using A0 cong_def by 
fastforce
qed
lemma congDL:
  "refl_on X R \<Longrightarrow> cong X f R \<Longrightarrow> a \<in> X \<Longrightarrow> (x, y) \<in> R \<Longrightarrow>  (f a x, f a y) \<in> R"
proof-  
  assume A0:"refl_on X R" "cong X f R" "a \<in> X" "(x,y)\<in>R"
  then have B0:"(a,a)\<in>R"   
    by (simp add: refl_onD)  
  then show "(f a x, f a y) \<in> R"  
    using A0 cong_def by fastforce 
qed

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

context magma_homomorphism
begin
lemma ker_cong:"cong X (\<cdot>) kernel"
proof(rule congI1)
  fix x1 x2 y1 y2 assume x12:"(x1, x2) \<in> kernel" and  y12:"(y1, y2) \<in> kernel" 
  then obtain px12:"f x1 = f x2" and py12:"f y1 = f y2" and x1:"x1 \<in> X" and y1:"y1 \<in> X" and x2:"x2 \<in> X" and y2:"y2 \<in> X"          
    using ker.eqr.l_closed ker.eqr.p_eq1 ker.eqr.r_closed ker.h_eq kernel_def by force
  then obtain "f (x1 \<cdot> y1) = (f x1) \<star> f(y1)" and "f (x2 \<cdot> y2) = (f x2) \<star> f(y2)"
    using cmp by force 
  then obtain "f (x1 \<cdot> y1) = f (x2 \<cdot> y2)"
    using px12 py12 by auto
  then show "(x1 \<cdot> y1, x2 \<cdot> y2) \<in> kernel"
    by (simp add: dom.closed ker.kernel_memI kernel_def x1 x2 y1 y2)
qed

end

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
definition quotient_law (infixl "\<bullet>" 70) where "quotient_law \<equiv> (\<lambda>t \<in> X/R. \<lambda>s \<in> X/R. \<pi> (f (\<sigma> t) (\<sigma> s)) )"
lemma op_compat1:"\<lbrakk>\<pi> x1=\<pi> x2;\<pi> y1=\<pi> y2; x1\<in>X; x2\<in>X;y1\<in>X; y2\<in>X\<rbrakk> \<Longrightarrow> \<pi> (x1 \<cdot>y1) = \<pi> (x2 \<cdot> y2)" 
  by (meson closed p_equivalence quotient_magma.compatible quotient_magma_axioms) 

lemma left_compatible:"a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (a\<cdot>x, a\<cdot>y) \<in> R"  using compatible by auto 
lemma right_compatible:"a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (x\<cdot>a, y\<cdot>a) \<in> R"  using compatible by auto 
lemma left_trans_compat:"\<And>a. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (l_trans a x, l_trans a y)\<in>R" 
  by (simp add: compatible l_closed l_trans_def r_closed)
lemma right_trans_compat:"\<And>a. a \<in> X \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (r_trans a x, r_trans a y)\<in>R"  
  by (simp add: compatible r_closed r_trans_def l_closed)

lemma psecE3:"t \<in> X/R \<Longrightarrow> s \<in> X/R \<Longrightarrow>  (\<sigma> t)\<cdot>(\<sigma> s) \<in> X" 
  by (simp add: closed sec_closed) 

lemma qlaw1:"t \<in> X/R \<Longrightarrow> s \<in> X/R  \<Longrightarrow> t\<bullet>s \<in> X/R" 
  by (simp add: closed sec_closed quotient_law_def)  

lemma qlaw2:"x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> y1 \<in> \<pi> x1 \<Longrightarrow> y2 \<in> \<pi> x2 \<Longrightarrow> y1 \<cdot> y2 \<in> \<pi> (x1 \<cdot> x2)" 
  by (meson compatible p_D1 p_I1)  

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

lemma qlaw4:"\<lbrakk>t \<in> X/R;s \<in> X/R\<rbrakk> \<Longrightarrow>t\<bullet>s = \<pi>((\<sigma> t) \<cdot> (\<sigma> s))" 
  by (metis psecE1 qlaw3 sec_closed) 

sublocale quotient: magma "X/R" "(\<bullet>)" 
  by (simp add: magma.intro qlaw1)

lemma proj_homomorphism:"magma_homomorphism \<pi> X (\<cdot>) (X/R) (\<bullet>)"  
  by(unfold_locales)(auto simp add:qlaw3)

lemma proj_epimorphism:"magma_epimorphism \<pi> X (\<cdot>) (X/R) (\<bullet>)"  
  by(unfold_locales)(auto simp add:qlaw3)

sublocale proj:magma_homomorphism \<pi> X f "(X/R)" "(\<bullet>)"  by (simp add: proj_homomorphism) 

sublocale proj_epi:magma_epimorphism \<pi> X f "(X/R)" "(\<bullet>)" by (simp add: proj_epimorphism) 

lemma qlaw5:"\<lbrakk>t \<in> X/R;s \<in> X/R\<rbrakk> \<Longrightarrow>t\<bullet>s = (\<pi> (\<sigma> t)) \<bullet> (\<pi>(\<sigma> s))" 
  using psecE1 by auto 

lemma qlaw6:"\<lbrakk>t \<in> X/R;s \<in> X/R\<rbrakk> \<Longrightarrow>(\<pi> (\<sigma> t)) \<bullet> (\<pi>(\<sigma> s)) =\<pi>((\<sigma> t) \<cdot> (\<sigma> s))" 
  using psecE1 qlaw4 by presburger 

end

theorem magma_liftable_operation_iff_congruent:
  fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)  and R::"'a rel"
  assumes A0:"magma X (\<cdot>)" and A1:"equivalence_relation X R"
  shows "(\<exists>q::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set. magma (X/R) q \<and> magma_homomorphism (qproj X R) X (\<cdot>) (X/R) q)
        \<longleftrightarrow> cong X f R"
proof
  assume "(\<exists>q::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set. magma (X/R) q \<and> magma_homomorphism (qproj X R) X (\<cdot>) (X/R) q)"
  then obtain q (infixl "\<bullet>" 70) where A2:"magma (X/R) (\<bullet>)" and A3:"magma_homomorphism (qproj X R) X (\<cdot>) (X/R) (\<bullet>)"
    by auto
  show "cong X f R"
  proof(rule congI1)
    fix x1 x2 y1 y2 assume x12:"(x1, x2) \<in> R" and  y12:"(y1, y2) \<in> R" 
    then obtain px12:"(qproj X R) x1 = (qproj X R) x2" and py12:"(qproj X R) y1 = (qproj X R) y2"
      by (simp add: A1 equivalence_relation.p_eq1)
    then obtain "(qproj X R) (x1 \<cdot> y1) = ((qproj X R) x1) \<bullet> ((qproj X R) y1)" and
                "(qproj X R) (x2 \<cdot> y2) = ((qproj X R) x2) \<bullet> ((qproj X R) y2)"
      by (meson A1 A3 equivalence_relation.l_closed equivalence_relation.r_closed magma_homomorphism.cmp x12 y12) 
    then show "(x1 \<cdot> y1, x2 \<cdot> y2) \<in> R"
      by (metis A0 A1 equivalence_relation.l_closed equivalence_relation.p_D1 equivalence_relation.p_self 
          equivalence_relation.r_closed magma.closed px12 py12 x12 y12)
  qed
next
  assume A2:"cong X f R"
  show "(\<exists>q::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set. magma (X/R) q \<and> magma_homomorphism (qproj X R) X (\<cdot>) (X/R) q)"
    using A0 A1 A2 congD1 magma_homomorphism.axioms(3) quotient_magma.intro quotient_magma.proj_homomorphism
          quotient_magma_axioms_def by fastforce
qed


context magma_homomorphism
begin

lemma quotient_magma:"quotient_magma X (\<cdot>) R(f)"
  using congD1 dom.magma_axioms ker.eqr.equivalence_relation_axioms ker_cong kernel_def quotient_magma.intro quotient_magma_axioms_def by fastforce
end


subsection \<open>First Isomorphism For Magmas\<close>
locale magma_homomorphism_fundamental=magma_homomorphism 
begin
sublocale quotient:quotient_magma X "(\<cdot>)" "R(f)"  by (simp add: quotient_magma)
notation quotient.quotient_law (infixl "(\<bullet>)" 70)
lemma first_isomorphism_magmas1:"submagma (f`X) Y (\<star>)"  by (simp add: im.submagma_axioms)
lemma first_isomorphism_magmas2:"cong X (\<cdot>) R(f)"  using ker_cong kernel_def by force
lemma first_isomorphism_magmas3a:"magma_homomorphism (ker.h) (X/R(f)) (\<bullet>) (f`X) (\<star>)"  
 apply(unfold_locales)
  using ker.quotient_map.dom apply blast
  apply auto
  using cmp dom.closed quotient.qlaw3 by fastforce

lemma first_isomorphism_magmas3b:"magma_isomorphism ker.h (X/R(f)) (\<bullet>) (f`X) (\<star>)"
  apply(unfold_locales)
  using ker.quotient_map.dom apply blast
    apply(auto)
  apply (metis ker.eqr.elem_ex2 ker.factorization2 inj_on_imp_bij_betw ker.quotient_map.inj surj_compose)
  using cmp dom.closed quotient.qlaw3 by fastforce

sublocale induced:magma_isomorphism ker.h "X/R(f)" "(\<bullet>)" "f`X" "(\<star>)"
  by (simp add: first_isomorphism_magmas3b)

lemma first_isomorphism_magmas:
  shows "submagma (f`X) Y (\<star>)" and 
        "cong X (\<cdot>) R(f)" and
        "magma_isomorphism ker.h (X/R(f)) (\<bullet>) (f`X) (\<star>)"
  apply (simp add: first_isomorphism_magmas1)
  apply (simp add: first_isomorphism_magmas2)
  by (simp add: first_isomorphism_magmas3b)

lemma third_isomorphism_magmas2:
  assumes A0:"submagma B Y (\<star>)" and A1:"(vimage f B) \<subseteq> X"
  shows "vimage f B = (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
proof-
  let ?A="vimage f B"
  have B0:"\<And>x. x \<in>?A \<Longrightarrow> ker.eqr.p x \<subseteq>?A"
  proof-
    fix x assume x0:"x \<in> ?A" then obtain x1:"x \<in> X"
      using A1 by blast 
    show "ker.eqr.p x \<subseteq> ?A "
    proof
      fix y assume y0:"y \<in> ker.eqr.p x"
      then obtain "f x = f y"
        by (meson ker.h_eq ker.eqr.p_D1 ker.eqr.p_closed1 ker.eqr.p_eq1 x1)
      then show "y \<in> ?A"
        using x0 by auto
    qed
  qed
  then have B1:"(\<Union>x \<in> (vimage f B). ker.eqr.p x) \<subseteq> ?A"
    by blast
  have B2:"\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ker.eqr.p x"
    using A1 by force
  then have B3:"?A \<subseteq> (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
    by blast
  then show ?thesis
    using B1 by blast
qed

lemma third_isomorphism_magmas:
  shows "\<And>A. submagma A X (\<cdot>) \<Longrightarrow> submagma (f`A) Y (\<star>)" and
        "\<And>B. submagma B Y (\<star>) \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow> submagma (vimage f B) X (\<cdot>) \<and> 
             (vimage f B) = (\<Union>x \<in> (vimage f B). ker.eqr.p x)" 
  apply (simp add: submagma1)
  using submagma12 third_isomorphism_magmas2 by presburger

end


subsection \<open>Magma Epimorphism Factoring\<close>


locale magma_epimorphism_factoring=
  map:magma_homomorphism f X "(\<cdot>)" Y "(\<star>)" +epi:magma_epimorphism g X "(\<cdot>)" Z "(\<bullet>)"
  for f and g and X and Y and Z and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and law3 (infixl "\<bullet>" 70)+
  assumes ker_sub:"ker_pair X g \<subseteq> ker_pair X f"
begin

definition "h \<equiv> compose Z f (rinv g X Z)"

lemma h_set_hom:"h \<in>set_morphisms Z Y"
  by (metis h_def hom2 map.mem_hom epi.right_inv_is_set_morphism epi.right_inverse_def)

lemma hg_set_hom:"compose X h g \<in> set_morphisms X Y"  using h_set_hom hom2 epi.mem_hom by blast 
lemma compat:"\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X;g x1 = g x2\<rbrakk> \<Longrightarrow> f x1 = f x2"  using ker_sub unfolding ker_pair_def by auto


lemma h_eq1:"\<And>x. x \<in> X \<Longrightarrow> f x = h (g x)"
  unfolding h_def using compat epi.sur surj_implies_factors(2)[of g X Z f] by blast

lemma h_eq2:"\<And>x. x \<in> X \<Longrightarrow> f x = (compose X h g) x"
  by (simp add: compose_eq h_eq1)

lemma h_eq3:"compose X h g = f"
proof-
  obtain B5:"f \<in> set_morphisms X Y" and B6:"g \<in> set_morphisms X Z"
    by (simp add: map.mem_hom epi.mem_hom) 
  then show ?thesis
    by (metis fun_eqI h_eq2 hg_set_hom)
qed  

lemma magma_hom0:"\<And>x1 x2. \<lbrakk>x1\<in>X;x2\<in>X\<rbrakk> \<Longrightarrow>h ((g x1) \<bullet> (g x2)) = (h (g x1))\<star>(h (g x2)) "
  using h_eq1 map.cmp map.dom.closed epi.cmp by force

lemma magma_hom1:"\<And>z1 z2. \<lbrakk>z1\<in>Z;z2\<in>Z\<rbrakk> \<Longrightarrow>h (z1\<bullet>z2) = (h z1) \<star> (h z2) "
proof-
  fix z1 z2 assume z10:"z1 \<in> Z" and z20:"z2 \<in> Z"
  then obtain x1 x2 where "x1 \<in> X" and "z1 = g x1" and "x2 \<in> X" and "z2 = g x2"
    using epi.sur by blast
  then show "h (z1\<bullet>z2) = (h z1) \<star> (h z2) "
    by (simp add: magma_hom0)
qed

lemma magma_hom:"magma_homomorphism h Z (\<bullet>) Y (\<star>)"
  apply(unfold_locales)
  apply (meson h_set_hom hom10)
  apply (meson h_set_hom hom9)
  using magma_hom1 by blast

end

subsection \<open>Magma Monomorphism Factoring\<close>
locale magma_monomorphism_factoring=
  map:magma_homomorphism f X "(\<cdot>)" Y "(\<star>)" +mono:magma_monomorphism g Z "(\<bullet>)" Y "(\<star>)"
  for f and g and X and Y and Z and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and law3 (infixl "\<bullet>" 70)+
  assumes im_sub:"f`X \<subseteq> g`Z"
begin

definition "h \<equiv> compose X (rinv g Z Y) f"

lemma g_inj:"inj_on g Z"
  by simp

lemma h_set_hom:"h \<in>set_morphisms X Z"
  by (simp add: h_def inj_implies_factors_concrete(2) im_sub map.mem_hom mono.mem_hom)

lemma gh_set_hom:"compose X g h \<in> set_morphisms X Y"
  using h_set_hom hom2 mono.mem_hom by blast 

lemma h_eq1:"\<And>x. x \<in> X \<Longrightarrow> f x = g (compose X (rinv g Z Y) f x) "
proof-
  fix x assume x0:"x \<in> X"
  then have "f x = g ((rinv g Z Y) (f x))"
    by (meson g_inj im_sub inj_implies_factors_concrete(1) map.mem_hom mono.mem_hom)
  also have "... = g (compose X (rinv g Z Y) f x)"
    by (simp add: compose_eq x0)
  finally show "f x = g (compose X (rinv g Z Y) f x)"
    by blast
qed

lemma h_eq2:"\<And>x. x \<in> X \<Longrightarrow> f x = g (h x)"
  using h_def h_eq1 by force

lemma h_eq3:"\<And>x. x \<in> X \<Longrightarrow> f x = (compose X g h) x"
  by (simp add: compose_eq h_eq2)

lemma h_eq4:"compose X g h = f"
proof-
  obtain B5:"f \<in> set_morphisms X Y" and B6:"g \<in> set_morphisms Z Y"
    by (simp add: map.mem_hom mono.mem_hom) 
  then show ?thesis
    by (metis g_inj h_def im_sub inj_implies_factors_concrete(5))
qed  


lemma magma_hom1:"\<And>x1 x2. \<lbrakk>x1\<in>X;x2\<in>X\<rbrakk> \<Longrightarrow>h (x1\<cdot>x2) = (h x1) \<bullet> (h x2) "
proof-
  fix x1 x2 assume x10:"x1 \<in> X" and x20:"x2 \<in> X"
  then obtain "f x1 \<in> Y" and "f x2 \<in> Y" and h0:"h x1 \<in> Z" and h1:"h x2 \<in> Z"
    by (meson h_set_hom hom9 map.mem_hom) 
  let ?r="rinv g Z Y"
  have B0:"h  (x1\<cdot>x2) = ?r (f(x1 \<cdot> x2))"
    by (simp add: compose_eq h_def map.dom.closed x10 x20)
  also have B1:"... = ?r ((f x1) \<star> (f x2))"
    by (simp add: map.cmp x10 x20)
  also have "... = ?r ((g (h x1)) \<star>( g (h x2)))"
    using h_eq2 x10 x20 by force
  also have "... = ?r (g ((h x1) \<bullet> (h x2)))"
    by (simp add: h0 h1 mono.cmp)
   also have "... = ((h x1) \<bullet> h (x2))"
     using h0 h1 mono.dom.closed mono.left_inverse_comp3 mono.left_inverse_def by force
  finally show "h (x1\<cdot>x2) = (h x1) \<bullet> (h x2) "
    by simp
qed


lemma magma_hom:"magma_homomorphism h X (\<cdot>) Z (\<bullet>)"
  apply(unfold_locales)
  apply (meson h_set_hom hom10)
  apply (meson h_set_hom hom9)
  using magma_hom1 by blast


end



subsection \<open>Preimage of Magma Congruence\<close>

locale magma_epimorphism_congruence_image_=
  map:magma_epimorphism f X "(\<cdot>)" Y "(\<star>)"+eqr:quotient_magma X "(\<cdot>)" R
  for f and X and Y and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and R+
  assumes sub:"(ker_pair X f ) \<subseteq> R"
begin
notation local.map.ker.kernel_pair_object ("R'(_')")
notation eqr.quotient_law ("\<bullet>")

lemma f_ker_coarser:"ker_pair X f \<subseteq> ker_pair X eqr.p"
  using eqr.eqr_eq_proj_ker sub by auto

sublocale magma_epimorphism_factoring eqr.p f X "X/R" Y "(\<cdot>)" "(\<bullet>)" "(\<star>)"
  by(unfold_locales;simp add:f_ker_coarser)

definition factor_map where "factor_map \<equiv> compose Y eqr.p (rinv f X Y)"

definition "Q\<equiv> {(f x, f y)|x y. (x,y) \<in> R}"

lemma Q_memE:assumes "(y1, y2)\<in>Q"
  obtains x1 x2 where "x1 \<in> X" and "x2 \<in> X" and "y1 = f x1" and "y2 = f x2" and "(x1, x2)\<in>R"
  using assms Q_def by auto

lemma Q_refl_on:"refl_on Y Q"
  unfolding refl_on_def Q_def using map.sur by(blast)

lemma Q_sym:"sym Q"
  unfolding Q_def sym_def using eqr.sym by(blast)

lemma Q_trans:"trans Q"
proof(rule transI)
  fix y1 y2 y3 assume xy:"(y1, y2) \<in> Q" and yz:"(y2, y3) \<in> Q" 
  then obtain x1 x2 x3 where "x1 \<in> X" and "x2 \<in> X" and "x3 \<in> X" and y1:"y1 = f x1" and "y2 = f x2" and
                             y3:"y3 = f x3"
    by (meson Q_memE)
  then obtain x12:"(x1, x2)\<in>R" and x23:"(x2, x3)\<in>R"
    by (metis Q_memE compat eqr.p_equivalence xy yz)
  then obtain "(x1, x3)\<in>R"
    using eqr.trn by blast
  then show "(y1, y3) \<in> Q"
    using Q_def y1 y3 by auto
qed

lemma q_eqr:"is_eqrel Y Q"
  by (simp add: Q_refl_on Q_sym Q_trans is_eqrel_def) 

lemma factor_maps_factors:"compose X (factor_map) f = eqr.p"
  using factor_map_def h_def h_eq3 by auto

lemma q_eq_ker_factor:"Q = ker_pair Y (factor_map)"
proof 
  show " Q \<subseteq> ker_pair Y factor_map"
  proof
    fix u assume "u \<in> Q" then obtain x1 x2 where "(x1, x2)\<in>R" and u:"u=(f x1, f x2)"
      using Q_def by auto
    then obtain "f x1 \<in> Y" and "f x2 \<in> Y" and "factor_map (f x1) = factor_map (f x2)"
      by (metis compose_eq eqr.l_closed eqr.p_eq1 eqr.r_closed factor_maps_factors map.cod)
     then have "(f x1, f x2) \<in> ker_pair Y (factor_map)"
       unfolding ker_pair_def by blast
     then show "u \<in> ker_pair Y (factor_map)"
       by (simp add: u)
   qed
   show "ker_pair Y factor_map \<subseteq> Q"
   proof
     fix u assume "u \<in> ker_pair Y factor_map"
   then obtain y1 y2 where "y1 \<in> Y" and "y2 \<in> Y" and eq:"factor_map y1 = factor_map y2" and u:"u=(y1,y2)"
     unfolding ker_pair_def by blast
   then obtain x1 x2 where "x1 \<in> X" and "x2 \<in> X" and y1:"y1 = f x1" and y2:"y2 = f x2"
     using map.sur by blast 
   then obtain "(x1, x2)\<in>R"
     by (metis compose_eq eq eqr.p_equivalence factor_maps_factors)
   then show "u \<in> Q"
     using Q_def u y1 y2 by auto
 qed
qed

lemma q_eqr2:"equivalence_relation Y Q"
  by (simp add: equivalence_relationI q_eqr)

lemma q_cong:"cong Y (\<star>) Q"
proof(rule congI1)
  fix y1 y2 y3 y4 assume "(y1, y2) \<in> Q" and "(y3, y4) \<in> Q"
  then obtain x1 x2 x3 x4 where "x1 \<in> X" and "x2 \<in> X" and "x3 \<in> X" and "x4 \<in> X"and 
    y1:"y1 = f x1" and y2:"y2 = f x2" and y3:"y3 = f x3" and y4:"y4 = f x4" and  "(x1, x2)\<in>R" and "(x3, x4)\<in>R"
    by (meson Q_memE)
  then obtain "(x1 \<cdot> x3, x2 \<cdot> x4) \<in> R" and "f (x1 \<cdot> x3) = y1 \<star> y3" and "f (x2 \<cdot> x4) = y2 \<star> y4"
    using eqr.compatible map.cmp by presburger
  then show "(y1 \<star> y3, y2 \<star> y4) \<in> Q"
    using Q_def by fastforce
qed


sublocale domain_eqr:equivalence_relation X R
  by (simp add: eqr.equivalence_relation_axioms)

sublocale codomain_ker:kernel_pair factor_map Y "X/R"
  using factor_map_def h_def h_set_hom kernel_pair.intro set_morphismI1 by fastforce

sublocale codom_hom:magma_homomorphism "factor_map" Y "(\<star>)" "X/R" "(\<bullet>)"
  apply(unfold_locales)
  using factor_map_def h_def magma_hom1 by presburger

sublocale codom_quotient:quotient_magma Y "(\<star>)" Q
  using codom_hom.quotient_magma codomain_ker.ker_pair_ker q_eq_ker_factor by auto

notation codom_quotient.quotient_law ("\<otimes>")

sublocale magma_homomorphism "factor_map" "Y" "(\<star>)" "(X/R)" "(\<bullet>)"
  using codom_hom.magma_homomorphism_axioms by blast

sublocale first_isomorphism:magma_homomorphism_fundamental "factor_map" "Y" "(\<star>)" "(X/R)" "(\<bullet>)"
  by (simp add: codom_hom.magma_homomorphism_axioms magma_homomorphism_fundamental_def)

lemma epi_then_iso:
  assumes A0:"f`X=Y"
  shows "magma_isomorphism codomain_ker.h (Y/Q) (\<otimes>) (X/R) (\<bullet>)"
  apply(unfold_locales)
  apply (simp add: codomain_ker.ker_pair_ker first_isomorphism.induced.dom q_eq_ker_factor)
  apply (simp add: codomain_ker.ker_pair_ker q_eq_ker_factor)
  apply (metis assms codomain_ker.ker_pair_ker eqr.proj_epi.sur factor_maps_factors first_isomorphism.induced.iso q_eq_ker_factor surj_compose)
  using codomain_ker.ker_pair_ker first_isomorphism.induced.cmp q_eq_ker_factor by force


end


subsection \<open>Image of Magma Congruence\<close>
locale magma_congruence_vimage_=
  map:magma_homomorphism f X "(\<cdot>)" Y "(\<star>)"+eqr:quotient_magma Y "(\<star>)" S
  for f and X and Y and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and S
begin
notation local.map.ker.kernel_pair_object ("R'(_')")
notation eqr.quotient_law ("\<bullet>")

lemma ker_pair_eq:"S = ker_pair Y (eqr.p)"  using eqr.eqr_eq_proj_ker by blast

definition "Q \<equiv> {(x, y) \<in> X \<times> X. (f x, f y) \<in> S}"

lemma q_vimage_comp:"Q = ker_pair X (compose X eqr.p f)"
  apply(auto simp add:Q_def ker_pair_def)
  apply (simp add: compose_eq eqr.p_eq1)
  apply (simp add: compose_eq eqr.p_eq1)
  by (simp add: compose_eq eqr.p_equivalence)

lemma q_eqr:"is_eqrel X Q" unfolding is_eqrel_def Q_def refl_on_def sym_def trans_def apply(auto)
  using eqr.sym apply presburger
  by (meson eqr.trn)

lemma q_eqr2:"equivalence_relation X Q"
  apply(unfold_locales)
  using Q_def apply force
  apply (simp add: Q_def)
  apply (simp add: Q_def eqr.sym)
  by (simp add: ker_pair_def q_vimage_comp)

lemma q_cong:"cong X (\<cdot>) Q"
  unfolding Q_def
  apply(rule congI1)
  using eqr.compatible map.cmp map.dom.closed by auto

lemma ker_sub_q:"R(f) \<subseteq> Q" unfolding Q_def  local.map.ker.kernel_pair_object_def  by fastforce

sublocale domain_eqr:equivalence_relation X Q 
  by (simp add: q_eqr2)

sublocale domain_ker:kernel_pair "(compose X eqr.p f)" X "Y/S"
  using eqr.proj_hom2 hom2 kernel_pair_def map.mem_hom set_morphismI1 by blast  

sublocale codom_hom:magma_homomorphism "(compose X eqr.p f)" X "(\<cdot>)" "Y/S" "(\<bullet>)"
  apply(unfold_locales)
  by (simp add: compose_eq eqr.proj_epi.cmp map.cmp map.dom.closed)

sublocale dom_quotient:quotient_magma X "(\<cdot>)" Q
  using codom_hom.quotient_magma domain_ker.ker_pair_ker q_vimage_comp by auto

notation dom_quotient.quotient_law ("\<otimes>")

sublocale magma_homomorphism "(compose X eqr.p f)" "X" "(\<cdot>)" "(Y/S)" "(\<bullet>)"
  using codom_hom.magma_homomorphism_axioms by blast

sublocale first_isomorphism:magma_homomorphism_fundamental "(compose X eqr.p f)" "X" "(\<cdot>)" "(Y/S)" "(\<bullet>)"
  by (simp add: codom_hom.magma_homomorphism_axioms magma_homomorphism_fundamental_def)

lemma epi_then_iso:
  assumes A0:"f`X=Y"
  shows "magma_isomorphism domain_ker.h (X/Q) (\<otimes>) (Y/S) (\<bullet>)"
  apply(unfold_locales)
  using domain_ker.ker_pair_ker domain_ker.quotient_map.dom q_vimage_comp apply presburger
  apply (simp add: domain_ker.ker_pair_ker q_vimage_comp)
  apply (metis assms domain_ker.ker_pair_ker eqr.proj_epi.sur_locale_axioms first_isomorphism.induced.iso q_vimage_comp sur_locale.sur surj_compose)
  using domain_ker.ker_pair_ker first_isomorphism.induced.cmp q_vimage_comp by force


end

section \<open>Actions\<close>

definition "actions \<Omega> E \<equiv> (set_morphisms \<Omega> (set_morphisms E E))"

locale action=fixes \<Omega>::"'a set" and E::"'b set" and \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes acts[intro,simp]:"\<alpha> \<in> actions \<Omega> E"
begin
definition "l_law \<equiv> (\<lambda>\<omega> \<in> \<Omega>. \<lambda>x \<in> E. \<alpha> \<omega> x)"
definition "r_law \<equiv> (\<lambda>x \<in> E. \<lambda>\<omega> \<in> \<Omega>. \<alpha> \<omega> x)"
lemma actsE1:"\<alpha> \<in> set_morphisms \<Omega> (set_morphisms E E)"  using actions_def acts by auto
lemma actsE21[intro,simp]:"\<omega> \<in> \<Omega> \<Longrightarrow> \<alpha> \<omega> \<in> set_morphisms E E"   using actions_def acts hom9 by fastforce
lemma actsE22[intro,simp]:"\<omega> \<notin> \<Omega> \<Longrightarrow> \<alpha> \<omega> = undefined"  using actions_def acts hom10 by fastforce  
lemma actsE211[intro,simp]:"\<omega> \<in> \<Omega> \<Longrightarrow> x \<in> E \<Longrightarrow> \<alpha> \<omega> x \<in> E"  using hom9[of "(\<alpha> \<omega>)" E E x]  actsE21 by auto
lemma actsE212[intro,simp]:"\<omega> \<in> \<Omega> \<Longrightarrow> x \<notin> E \<Longrightarrow> \<alpha> \<omega> x = undefined" using hom10[of "(\<alpha> \<omega>)" E E x]  actsE21 by auto 
end


context magma
begin
sublocale l_action:action X X "l_trans" by(unfold_locales,simp add: actions_def l_trans_hom_mem)
sublocale r_action:action X X "r_trans"  by(unfold_locales,simp add: actions_def r_trans_hom_mem)

lemma l_derived_law_eq1:"\<And>a. a \<in> X \<Longrightarrow> l_trans a = l_action.l_law a" 
  using l_action.l_law_def by force

lemma r_derived_law_eq1:"\<And>a. a \<in> X \<Longrightarrow> r_trans a = l_action.r_law a"
  using l_action.r_law_def l_trans_app by fastforce

lemma l_derived_law_eq2:"l_trans = l_action.l_law"
  using l_action.l_law_def lr_trans_dual opposite.r_trans_def by auto 

lemma r_derived_law_eq2:"r_trans = l_action.r_law"
  using l_action.r_law_def r_derived_law_eq1 by auto


end

locale set_endomorphisms=fixes E::"'a set"
begin
sublocale magma "set_morphisms E E" "compose E"  by(unfold_locales;simp add: hom2)

lemma id_lid:"l_identity (Id E)"  by (simp add: hom5 l_identity_def)
lemma id_rid:"r_identity (Id E)"  by (simp add: hom6 r_identity_def)  
lemma id_id:"id_elem (Id E)"  by (simp add: hom5 hom6 id_elem_def) 


end


section \<open>Semigroup\<close>
subsection \<open>Semigroup Loale\<close>
locale semigroup=magma+
  assumes asc[ac_simps]:"\<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
begin
definition l_cancel where "l_cancel a \<equiv> inj_on (l_trans a) X"
definition r_cancel where "r_cancel a \<equiv> inj_on (r_trans a) X"
definition b_cancel where "b_cancel a \<equiv> inj_on (l_trans a) X \<and> inj_on (r_trans a) X"

lemma associate2:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (x\<cdot>y)\<cdot>z = x \<cdot> y \<cdot> z"   by simp
lemma associate3:assumes mem:"x \<in> X" "y \<in> X""z \<in> X" and xy:"x \<cdot> y = y \<cdot> x" shows "x\<cdot>(y\<cdot>z) = (y\<cdot>x)\<cdot>z" 
proof- 
  have " x\<cdot>(y\<cdot>z) = (x\<cdot>y)\<cdot>z " 
    by (simp add: mem asc)
  also have "... = (y \<cdot> x) \<cdot> z" 
    by (simp add: xy) 
  finally show ?thesis
    by simp
qed

lemma commutes_assoc:
  assumes mem:"x \<in> X" "y \<in> X""z \<in> X" and xy:"x \<cdot> y = y \<cdot> x" and xz:"x \<cdot> z = z \<cdot> x" 
  shows " x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x"
proof-
  have " x\<cdot>(y\<cdot>z) = (y\<cdot>x)\<cdot>z"
    by (simp add: associate3 mem xy)
  also have "... = (y \<cdot> z) \<cdot> x"
    by (simp add: asc mem xz)
  finally show ?thesis by simp
qed

lemma assoc4:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X;d\<in>X\<rbrakk> \<Longrightarrow> (a\<cdot>b)\<cdot>(c\<cdot>d) = a\<cdot>(b\<cdot>c)\<cdot>d"
  using asc closed by auto

lemma ltranslation_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>  \<Longrightarrow> compose X (l_trans x) (l_trans y) z = l_trans (x \<cdot> y) z" 
  by (simp add: asc closed compose_def l_trans_def)

lemma rtranslation_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>  \<Longrightarrow> compose X (r_trans y) (r_trans x) z = r_trans (x \<cdot> y) z"
  by (simp add: asc closed compose_def r_trans_def) 

lemma ltranslation_comp:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans x) (l_trans y) = l_trans (x \<cdot> y)"
  using fun_eqI[of "compose X (l_trans x) (l_trans y)" X X "l_trans (x \<cdot> y)" X]
  by (metis closed hom2 l_trans_hom ltranslation_comp1)

lemma rtranslation_comp:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans y) (r_trans x) = r_trans (x \<cdot> y)"
  using fun_eqI[of "compose X (r_trans y) (r_trans x)" X X "r_trans (x \<cdot> y)" X]
  by (metis closed hom2 r_trans_hom rtranslation_comp1)


lemma l_cancelI: "(\<And>x y. \<lbrakk>x \<in> X; y \<in> X;  (l_trans a) x =  (l_trans a) y\<rbrakk> \<Longrightarrow> x =y) \<Longrightarrow> l_cancel a " 
  unfolding l_cancel_def inj_on_def by auto 

lemma r_cancelI: "(\<And>x y. \<lbrakk>x \<in> X; y \<in> X;  (r_trans a) x =  (r_trans a) y\<rbrakk> \<Longrightarrow> x =y) \<Longrightarrow> r_cancel a " 
  unfolding r_cancel_def inj_on_def by auto 

lemma b_cancelI: "r_cancel a \<Longrightarrow> l_cancel a  \<Longrightarrow> b_cancel a "
  by (simp add: b_cancel_def l_cancel_def r_cancel_def) 

lemma id_cancel:"e \<in> X \<Longrightarrow> id_elem e \<Longrightarrow> b_cancel e" 
  by (simp add: b_cancel_def id_elem_linj id_elem_rinj)

lemma id_elem_id_map:
  assumes is_mem:"e \<in> X" and is_id:"id_elem e"
  shows "l_trans e = Id X" and "r_trans e = Id X" 
proof-
  obtain idhom:"Id X \<in> set_morphisms X X" and lhom:"l_trans e \<in> set_morphisms X X" and rhom:"r_trans e \<in> set_morphisms X X" 
    using hom7[of X] l_trans_hom[of e] r_trans_hom[of e] is_mem by auto
  show " l_trans e = Id X" using lhom idhom  proof(rule fun_eqI) 
    show "\<And>x. x \<in> X \<Longrightarrow> l_trans e x = Id X x"
      using id_elem_def is_id is_mem l_trans_def by auto
  qed
  show " r_trans e = Id X" using rhom idhom  
  proof(rule fun_eqI)
    show "\<And>x. x \<in> X \<Longrightarrow> r_trans e x = Id X x" 
      using id_elem_def is_id is_mem r_trans_def by auto
  qed
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
    also have "... = y \<cdot> (x \<cdot> y \<cdot> z)"   using asc calculation r_identity_def rid rinvz xmem ymem zmem by auto
    also have "... = y \<cdot> (e \<cdot> z)" by (simp add: rinvy)
    also have "... = (y \<cdot>e ) \<cdot> z"    by (simp add: asc emem ymem zmem) 
    also have "... = e"  using r_identity_def rid rinvz ymem by force
    finally have "x \<cdot> y = e \<and> y \<cdot> x = e"
      by (simp add: rinvy)
    then show "(\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)"
      using ymem by auto
  qed
  then show "id_elem e" 
    using asc id_elem_def r_identity_def rid by fastforce
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
    also have "... = z\<cdot>(y\<cdot>x\<cdot>y)"  by (simp add: asc closed xmem ymem zmem)  
    also have "... = z\<cdot>(e\<cdot>y)" by (simp add: linvy)
    also have "... = z\<cdot>y"   using l_identity_def lid ymem by auto  
    also have "... = e"  using l_identity_def lid linvz ymem by force
    finally have "x \<cdot> y = e \<and> y \<cdot> x = e"    by (simp add: linvy)
    then show "(\<exists>y \<in> X. x \<cdot> y = e \<and> y \<cdot> x = e)"
      using ymem by auto
  qed
  then show "id_elem e" using asc id_elem_def l_identity_def lid by fastforce
qed

lemma commute_prod1:"\<lbrakk>x\<in>X;y\<in>X;z\<in>X; x\<cdot>y=y\<cdot>x;x\<cdot>z=z\<cdot>x\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x"
  using commutes_assoc by auto
lemma commute_prod2:"\<lbrakk>x\<in>X;y\<in>X;z\<in>X; x\<cdot>y=y\<cdot>x;x\<cdot>z=z\<cdot>x\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = (y \<cdot> z) \<cdot> x" 
  by (simp add: asc) 
lemma commute_prod3:"\<lbrakk>x\<in>X;y\<in>X;z\<in>X; commutes {x} {y,z}\<rbrakk> \<Longrightarrow> commutes {x} {y \<cdot> z}" 
  unfolding commutes_def  by (simp add: commutes_assoc)

lemma centralizer_stable:"A \<subseteq> X \<Longrightarrow> stable (centralizer A)"
  apply(rule stableI)
   apply (simp add: centralizer_sub)
  apply(rule centralizer_memI2)
  using closed magma.centralizer_sub magma_axioms apply blast
  by (simp add: centralizer_def commutes_assoc commutes_def in_mono)

lemma bicentralizer_stable:"A \<subseteq> X \<Longrightarrow> stable (bicentralizer A)" 
  by (simp add: centralizer_stable centralizer_sub)

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
  show "l_trans (x \<cdot> y) \<in> set_morphisms X X"
    by (simp add: A0 A1 closed l_trans_hom)
  show "compose X (l_trans x) (l_trans y) \<in> set_morphisms X X"
    using A0 A1 hom2 l_trans_hom by blast
  show "\<And>z. z \<in> X \<Longrightarrow> l_trans (x \<cdot> y) z = compose X (l_trans x) (l_trans y) z"
    by (simp add: A0 A1 ltranslation_comp)
qed


lemma right_trans_comp:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "r_trans (x \<cdot> y) = compose X (r_trans y) (r_trans x)"
proof(rule fun_eqI)
  show "r_trans (x \<cdot> y) \<in> set_morphisms X X"
    by (simp add: A0 A1 closed r_trans_hom)
  show "compose X (r_trans y) (r_trans x) \<in> set_morphisms X X"
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
    using A2 A3 A4 asc x y by force
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
    using A2 A3 A4 asc x y by force
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
      then obtain "x = a\<cdot>(b\<cdot>c)" using A0 asc by blast
      then show "x \<in> ?R"  unfolding set_prod_def using B0 by blast
    qed
    next show "?R \<subseteq> ?L"
    proof
      fix x assume A1:"x \<in>?R"
      then obtain a b c where B0: "a\<in>A" "b\<in>B" "c\<in>C" "x = a\<cdot>(b\<cdot>c)" unfolding set_prod_def by blast
      then obtain "x = (a\<cdot>b)\<cdot>c" using A0 by (simp add: asc in_mono) 
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
    also have "... \<longleftrightarrow> (\<exists>y \<in> E. x = y \<cdot> (a \<cdot> b))"   by (metis A0 A1 A2 asc subsetD)
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
    also have "... \<longleftrightarrow> (\<exists>y \<in> E. x = (a \<cdot> b) \<cdot>y)" by (metis A0 A1 A2 asc subsetD)   
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

subsection \<open>Subsemigroup Locale\<close>

locale subsemigroup=semigroup X "(\<cdot>)" for A and X and magma_law (infixl "\<cdot>" 70)+
  assumes submem:"A \<subseteq> X" and 
          subfun:"\<lbrakk>x \<in>A; y \<in> A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> A" and
          asc[ac_simps]:"\<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"
begin
sublocale submagma A X "(\<cdot>)"  using magma_axioms subfun submagmaI submem by blast 
sublocale sub:semigroup A "(\<cdot>)" by (simp add: semigroup.intro asc semigroup_axioms_def sub.magma_axioms)

end


lemma subsemigroup_trans[trans]:
  assumes "subsemigroup A B f" and 
          "subsemigroup B C f" 
  shows   "subsemigroup A C f" 
proof-
  interpret A: subsemigroup A B f  by fact 
  interpret C: subsemigroup B C f  by fact 
  show ?thesis
    using A.subfun C.asc C.semigroup_axioms subsemigroup.intro subsemigroup_axioms_def by blast
qed

subsection \<open>Semigroup Homomorphisms\<close>
locale semigroup_homomorphism=set_morphism f X Y+ dom:semigroup X "(\<cdot>)" + cod:semigroup Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) +
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale magma_homomorphism f X "(\<cdot>)" Y "(\<star>)"
  by (simp add: cmp cod.magma_axioms dom.magma_axioms magma_homomorphism.intro 
      magma_homomorphism_axioms.intro set_morphism_axioms)

lemma assoc_comm:"\<lbrakk>x \<in> X; y \<in> X;z \<in> X\<rbrakk> \<Longrightarrow>f ((x\<cdot>y)\<cdot>z) = (f x) \<star>((f y) \<star> (f z))"  by (simp add: cmp dom.asc dom.closed)

lemma im_subsemigroup1:"subsemigroup A X (\<cdot>) \<Longrightarrow> subsemigroup (f`A) Y (\<star>)" 
  apply(unfold_locales)
  apply (meson im.submem image_mono subsemigroup.submem subset_trans)
  apply (simp add: dom.magma_axioms imag_comp submagmaI subsemigroup.subfun subsemigroup.submem)
  using cod.asc by presburger


lemma im_subsemigroup2:"subsemigroup B Y (\<star>) \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow>subsemigroup (vimage f B) X (\<cdot>)" 
proof-
  assume A0:"subsemigroup B Y (\<star>)" and A1:"(vimage f B) \<subseteq> X"
  then show "subsemigroup (vimage f B) X (\<cdot>)"
  apply(unfold_locales)
  using A1 apply blast
  apply (simp add: cmp subsemigroup.subfun subset_eq)
  by (simp add: dom.asc)
qed

sublocale im:subsemigroup "f`X" Y "(\<star>)"
  by (simp add: cod.asc cod.semigroup_axioms im.subfun im.submem subsemigroup.intro subsemigroup_axioms_def) 

end


locale semigroup_epimorphism=set_epimorphism f X Y+ dom:semigroup X "(\<cdot>)" + cod:semigroup Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) +
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)"
  using cmp cod.semigroup_axioms dom.semigroup_axioms semigroup_homomorphism.intro
        semigroup_homomorphism_axioms_def set_morphism_axioms by blast
end


locale semigroup_monomorphism=set_monomorphism f X Y+ dom:semigroup X "(\<cdot>)" + cod:semigroup Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) +
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)"
  using cmp cod.semigroup_axioms dom.semigroup_axioms semigroup_homomorphism.intro
        semigroup_homomorphism_axioms_def set_morphism_axioms by blast
end


locale semigroup_isomorphism=set_isomorphism f X Y+ dom:semigroup X "(\<cdot>)" + cod:semigroup Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) +
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)"
  using cmp cod.semigroup_axioms dom.semigroup_axioms semigroup_homomorphism.intro
        semigroup_homomorphism_axioms_def set_morphism_axioms by blast
end



subsection \<open>Quotient Semigroup Locale\<close>
locale quotient_semigroup= 
  semigroup X "(\<cdot>)" +
  equivalence_relation X R
  for X::"'a set" and 
      f:: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70) and 
      R::"'a rel"+
  assumes compat:"(x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (x1\<cdot>y1 , x2\<cdot>y2) \<in> R"
begin

sublocale quotient_magma X "(\<cdot>)" R 
  by (simp add: compat equivalence_relation_axioms magma_axioms quotient_magma_axioms_def quotient_magma_def)

lemma p_associative:"\<lbrakk>x \<in> X; y \<in> X; z \<in>X\<rbrakk> \<Longrightarrow> ((p x) \<bullet> (p y)) \<bullet> (p z) = (p x)\<bullet>((p y)\<bullet>(p z))" 
  by (simp add: asc closed qlaw3)

lemma associative:"\<lbrakk>t \<in> X/R; s \<in> X/R; r \<in> X/R\<rbrakk>  \<Longrightarrow> (t\<bullet>s)\<bullet>r = t\<bullet>(s\<bullet>r)"  
  apply(erule projE)+ using p_associative by presburger


lemma proj_homomorphism:"semigroup_homomorphism \<pi> X (\<cdot>) (X/R) (\<bullet>)"  
  apply(unfold_locales)
  using associative apply presburger
  using proj_epi.cmp by auto

lemma proj_epimorphism:"semigroup_epimorphism \<pi> X (\<cdot>) (X/R) (\<bullet>)"  
  apply(unfold_locales)
  apply (meson associative)
  by (simp add: qlaw3)

sublocale quotient:semigroup "X/R" "(\<bullet>)" 
  using semigroup.intro associative quotient.magma_axioms semigroup_axioms_def by blast

sublocale proj:semigroup_homomorphism \<pi> X f "(X/R)" "(\<bullet>)"
  by (simp add: proj.cmp proj_hom quotient.semigroup_axioms semigroup_axioms
      semigroup_homomorphism.intro semigroup_homomorphism_axioms_def)

sublocale proj_epi:semigroup_epimorphism \<pi> X f "(X/R)" "(\<bullet>)"
  by (simp add: proj_epi qlaw3 quotient.semigroup_axioms semigroup_axioms
      semigroup_epimorphism.intro semigroup_epimorphism_axioms_def)

lemma rel_is_cong:"cong X (\<cdot>) R" 
  by (simp add: congI1 local.compatible)

end

theorem semigroup_liftable_operation_iff_congruent:
  fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)  and R::"'a rel"
  assumes A0:"semigroup X (\<cdot>)" and A1:"equivalence_relation X R"
  shows "(\<exists>q::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set. semigroup (X/R) q \<and> semigroup_homomorphism (qproj X R) X (\<cdot>) (X/R) q)
        \<longleftrightarrow> cong X f R"
proof
  assume "(\<exists>q::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set. semigroup (X/R) q \<and> semigroup_homomorphism (qproj X R) X (\<cdot>) (X/R) q)"
  then obtain q (infixl "\<bullet>" 70) where A2:"semigroup (X/R) (\<bullet>)" and A3:"semigroup_homomorphism (qproj X R) X (\<cdot>) (X/R) (\<bullet>)"
    by auto
  show "cong X f R"
  proof(rule congI1)
    fix x1 x2 y1 y2 assume x12:"(x1, x2) \<in> R" and  y12:"(y1, y2) \<in> R"  
    then obtain  x1:"x1 \<in> X" and x2:"x2 \<in> X" and y1:"y1 \<in> X" and y2:"y2 \<in> X"
      by (meson A1 equivalence_relation.l_closed equivalence_relation.r_closed)
    then obtain px12:"(qproj X R) x1 = (qproj X R) x2" and py12:"(qproj X R) y1 = (qproj X R) y2"
      by (simp add: A1 equivalence_relation.p_equivalence x12 y12)
    then obtain eq1:"(qproj X R) (x1 \<cdot> y1) = ((qproj X R) x1) \<bullet> ((qproj X R) y1)" and
                eq2:"(qproj X R) (x2 \<cdot> y2) = ((qproj X R) x2) \<bullet> ((qproj X R) y2)"
      by (meson A3 semigroup_homomorphism.cmp x1 x2 y1 y2)
    then show "(x1 \<cdot> y1, x2 \<cdot> y2) \<in> R"
      by (metis A0 A1 semigroup_def equivalence_relation.p_equivalence magma.closed px12 py12 x1 x2 y1 y2)
  qed
next
  assume A2:"cong X f R"
  show "(\<exists>q::'a set \<Rightarrow> 'a set \<Rightarrow> 'a set. semigroup (X/R) q \<and> semigroup_homomorphism (qproj X R) X (\<cdot>) (X/R) q)"
    using A0 A1 A2 congD1 semigroup_homomorphism.axioms(3) quotient_semigroup.intro quotient_semigroup.proj_homomorphism
          quotient_semigroup_axioms_def  by fastforce 
qed




subsection \<open>First Isomorphism For Semigroups\<close>

context semigroup_homomorphism
begin
lemma quotient_semigroup:"quotient_semigroup X (\<cdot>) R(f)"
  apply(unfold_locales)
  by (meson quotient_magma quotient_magma.compatible)
end

locale semigroup_homomorphism_fundamental=semigroup_homomorphism 
begin
sublocale quotient:quotient_semigroup X "(\<cdot>)" "R(f)"   using quotient_semigroup by blast
notation quotient.quotient_law (infixl "(\<bullet>)" 70)

lemma first_isomorphism_semigroups1:"subsemigroup (f`X) Y (\<star>)"
  by (simp add: im.subsemigroup_axioms)

lemma first_isomorphism_semigroups2:"cong X (\<cdot>) R(f)"  
  using ker_cong kernel_def by force

lemma first_isomorphism_semigroups3a:"semigroup_homomorphism (ker.h) (X/R(f)) (\<bullet>) (f`X) (\<star>)"  
 apply(unfold_locales)
  using ker.quotient_map.dom apply blast
  apply auto
  using cmp dom.closed quotient.qlaw3 by fastforce

lemma first_isomorphism_semigroups3b:"semigroup_isomorphism ker.h (X/R(f)) (\<bullet>) (f`X) (\<star>)"
  apply(unfold_locales)
  using ker.quotient_map.dom apply blast
    apply(auto)
  apply (metis bij_betw_imageI ker.factorization2 ker.quotient_map.inj quotient.proj_epi.sur surj_compose)
  using cmp dom.closed quotient.qlaw3 by fastforce

sublocale induced:semigroup_isomorphism ker.h "X/R(f)" "(\<bullet>)" "f`X" "(\<star>)"
  by (simp add: first_isomorphism_semigroups3b)

lemma first_isomorphism_semigroups:
  shows "subsemigroup (f`X) Y (\<star>)" and 
        "cong X (\<cdot>) R(f)" and
        "semigroup_isomorphism ker.h (X/R(f)) (\<bullet>) (f`X) (\<star>)"
  apply (simp add: first_isomorphism_semigroups1)
  apply (simp add: first_isomorphism_semigroups2)
  by (simp add: first_isomorphism_semigroups3b)

lemma third_isomorphism_subsemigroups2:
  assumes A0:"subsemigroup B Y (\<star>)" and A1:"(vimage f B) \<subseteq> X"
  shows "vimage f B = (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
proof-
  let ?A="vimage f B"
  have B0:"\<And>x. x \<in>?A \<Longrightarrow> ker.eqr.p x \<subseteq>?A"
  proof-
    fix x assume x0:"x \<in> ?A" then obtain x1:"x \<in> X"
      using A1 by blast 
    show "ker.eqr.p x \<subseteq> ?A "
    proof
      fix y assume y0:"y \<in> ker.eqr.p x"
      then obtain "f x = f y"
        by (meson ker.h_eq ker.eqr.p_D1 ker.eqr.p_closed1 ker.eqr.p_eq1 x1)
      then show "y \<in> ?A"
        using x0 by auto
    qed
  qed
  then have B1:"(\<Union>x \<in> (vimage f B). ker.eqr.p x) \<subseteq> ?A"
    by blast
  have B2:"\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ker.eqr.p x"
    using A1 by force
  then have B3:"?A \<subseteq> (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
    by blast
  then show ?thesis
    using B1 by blast
qed

lemma third_isomorphism_semigroups:
  shows "\<And>A. subsemigroup A X (\<cdot>) \<Longrightarrow> subsemigroup (f`A) Y (\<star>)" and
        "\<And>B. subsemigroup B Y (\<star>) \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow> subsemigroup (vimage f B) X (\<cdot>) \<and> 
             (vimage f B) = (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
  apply (simp add: im_subsemigroup1)
  using im_subsemigroup2 third_isomorphism_subsemigroups2 by force 

end


subsection \<open>Semigroup Epimorphism Factoring\<close>


locale semigroup_epimorphism_factoring=
  map:semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)" +epi:semigroup_epimorphism g X "(\<cdot>)" Z "(\<bullet>)"
  for f and g and X and Y and Z and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and law3 (infixl "\<bullet>" 70)+
  assumes ker_sub:"ker_pair X g \<subseteq> ker_pair X f"
begin

definition "h \<equiv> compose Z f (rinv g X Z)"

lemma h_set_hom:"h \<in>set_morphisms Z Y"
  by (metis h_def hom2 map.mem_hom epi.right_inv_is_set_morphism epi.right_inverse_def)

lemma hg_set_hom:"compose X h g \<in> set_morphisms X Y"  using h_set_hom hom2 epi.mem_hom by blast 
lemma compat:"\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X;g x1 = g x2\<rbrakk> \<Longrightarrow> f x1 = f x2"  using ker_sub unfolding ker_pair_def by auto


lemma h_eq1:"\<And>x. x \<in> X \<Longrightarrow> f x = h (g x)"
  unfolding h_def using compat epi.sur surj_implies_factors(2)[of g X Z f] by blast

lemma h_eq2:"\<And>x. x \<in> X \<Longrightarrow> f x = (compose X h g) x"
  by (simp add: compose_eq h_eq1)

lemma h_eq3:"compose X h g = f"
proof-
  obtain B5:"f \<in> set_morphisms X Y" and B6:"g \<in> set_morphisms X Z"
    by (simp add: map.mem_hom epi.mem_hom) 
  then show ?thesis
    by (metis fun_eqI h_eq2 hg_set_hom)
qed  

lemma magma_hom0:"\<And>x1 x2. \<lbrakk>x1\<in>X;x2\<in>X\<rbrakk> \<Longrightarrow>h ((g x1) \<bullet> (g x2)) = (h (g x1))\<star>(h (g x2)) "
  using h_eq1 map.cmp map.dom.closed epi.cmp by force

lemma magma_hom1:"\<And>z1 z2. \<lbrakk>z1\<in>Z;z2\<in>Z\<rbrakk> \<Longrightarrow>h (z1\<bullet>z2) = (h z1) \<star> (h z2) "
proof-
  fix z1 z2 assume z10:"z1 \<in> Z" and z20:"z2 \<in> Z"
  then obtain x1 x2 where "x1 \<in> X" and "z1 = g x1" and "x2 \<in> X" and "z2 = g x2"
    using epi.sur by blast
  then show "h (z1\<bullet>z2) = (h z1) \<star> (h z2) "
    by (simp add: magma_hom0)
qed

lemma semigroup_hom:"semigroup_homomorphism h Z (\<bullet>) Y (\<star>)"
  apply(unfold_locales)
  apply (meson h_set_hom hom10)
  apply (meson h_set_hom hom9)
  using magma_hom1 by blast

end

subsection \<open>Semigroups Monomorphism Factoring\<close>
locale semigroup_monomorphism_factoring=
  map:semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)" +mono:semigroup_monomorphism g Z "(\<bullet>)" Y "(\<star>)"
  for f and g and X and Y and Z and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and law3 (infixl "\<bullet>" 70)+
  assumes im_sub:"f`X \<subseteq> g`Z"
begin

definition "h \<equiv> compose X (rinv g Z Y) f"

lemma g_inj:"inj_on g Z"
  by simp

lemma h_set_hom:"h \<in>set_morphisms X Z"
  by (simp add: h_def inj_implies_factors_concrete(2) im_sub map.mem_hom mono.mem_hom)

lemma gh_set_hom:"compose X g h \<in> set_morphisms X Y"
  using h_set_hom hom2 mono.mem_hom by blast 

lemma h_eq1:"\<And>x. x \<in> X \<Longrightarrow> f x = g (compose X (rinv g Z Y) f x) "
proof-
  fix x assume x0:"x \<in> X"
  then have "f x = g ((rinv g Z Y) (f x))"
    by (meson g_inj im_sub inj_implies_factors_concrete(1) map.mem_hom mono.mem_hom)
  also have "... = g (compose X (rinv g Z Y) f x)"
    by (simp add: compose_eq x0)
  finally show "f x = g (compose X (rinv g Z Y) f x)"
    by blast
qed

lemma h_eq2:"\<And>x. x \<in> X \<Longrightarrow> f x = g (h x)"
  using h_def h_eq1 by force

lemma h_eq3:"\<And>x. x \<in> X \<Longrightarrow> f x = (compose X g h) x"
  by (simp add: compose_eq h_eq2)

lemma h_eq4:"compose X g h = f"
proof-
  obtain B5:"f \<in> set_morphisms X Y" and B6:"g \<in> set_morphisms Z Y"
    by (simp add: map.mem_hom mono.mem_hom) 
  then show ?thesis
    by (metis g_inj h_def im_sub inj_implies_factors_concrete(5))
qed  


lemma magma_hom1:"\<And>x1 x2. \<lbrakk>x1\<in>X;x2\<in>X\<rbrakk> \<Longrightarrow>h (x1\<cdot>x2) = (h x1) \<bullet> (h x2) "
proof-
  fix x1 x2 assume x10:"x1 \<in> X" and x20:"x2 \<in> X"
  then obtain "f x1 \<in> Y" and "f x2 \<in> Y" and h0:"h x1 \<in> Z" and h1:"h x2 \<in> Z"
    by (meson h_set_hom hom9 map.mem_hom) 
  let ?r="rinv g Z Y"
  have B0:"h  (x1\<cdot>x2) = ?r (f(x1 \<cdot> x2))"
    by (simp add: compose_eq h_def map.dom.closed x10 x20)
  also have B1:"... = ?r ((f x1) \<star> (f x2))"
    by (simp add: map.cmp x10 x20)
  also have "... = ?r ((g (h x1)) \<star>( g (h x2)))"
    using h_eq2 x10 x20 by force
  also have "... = ?r (g ((h x1) \<bullet> (h x2)))"
    by (simp add: h0 h1 mono.cmp)
   also have "... = ((h x1) \<bullet> h (x2))"
     using h0 h1 mono.dom.closed mono.left_inverse_comp3 mono.left_inverse_def by force
  finally show "h (x1\<cdot>x2) = (h x1) \<bullet> (h x2) "
    by simp
qed


lemma semigroup_hom:"semigroup_homomorphism h X (\<cdot>) Z (\<bullet>)"
  apply(unfold_locales)
  apply (meson h_set_hom hom10)
  apply (meson h_set_hom hom9)
  using magma_hom1 by blast


end



subsection \<open>Preimage of Semigroups Congruence\<close>

locale semigroup_epimorphism_congruence_image_=
  map:semigroup_epimorphism f X "(\<cdot>)" Y "(\<star>)"+eqr:quotient_semigroup X "(\<cdot>)" R
  for f and X and Y and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and R+
  assumes sub:"(ker_pair X f ) \<subseteq> R"
begin
notation local.map.ker.kernel_pair_object ("R'(_')")
notation eqr.quotient_law ("\<bullet>")

lemma f_ker_coarser:"ker_pair X f \<subseteq> ker_pair X eqr.p"
  using eqr.eqr_eq_proj_ker sub by auto

sublocale semigroup_epimorphism_factoring eqr.p f X "X/R" Y "(\<cdot>)" "(\<bullet>)" "(\<star>)"
  by(unfold_locales;simp add:f_ker_coarser)

definition factor_map where "factor_map \<equiv> compose Y eqr.p (rinv f X Y)"

definition "Q\<equiv> {(f x, f y)|x y. (x,y) \<in> R}"

lemma Q_memE:assumes "(y1, y2)\<in>Q"
  obtains x1 x2 where "x1 \<in> X" and "x2 \<in> X" and "y1 = f x1" and "y2 = f x2" and "(x1, x2)\<in>R"
  using Q_def assms eqr.l_closed eqr.r_closed by auto

lemma Q_refl_on:"refl_on Y Q"
  unfolding refl_on_def Q_def using map.sur by(blast)

lemma Q_sym:"sym Q"
  unfolding Q_def sym_def using eqr.sym by(blast)

lemma Q_trans:"trans Q"
proof(rule transI)
  fix y1 y2 y3 assume xy:"(y1, y2) \<in> Q" and yz:"(y2, y3) \<in> Q" 
  then obtain x1 x2 x3 where "x1 \<in> X" and "x2 \<in> X" and "x3 \<in> X" and y1:"y1 = f x1" and "y2 = f x2" and
                             y3:"y3 = f x3"
    by (meson Q_memE)
  then obtain x12:"(x1, x2)\<in>R" and x23:"(x2, x3)\<in>R"
    by (metis Q_memE compat eqr.p_equivalence xy yz)
  then obtain "(x1, x3)\<in>R"
    using eqr.trn by blast
  then show "(y1, y3) \<in> Q"
    using Q_def y1 y3 by auto
qed

lemma q_eqr:"is_eqrel Y Q"
  by (simp add: Q_refl_on Q_sym Q_trans is_eqrel_def) 

lemma factor_maps_factors:"compose X (factor_map) f = eqr.p"
  using factor_map_def h_def h_eq3 by auto

lemma q_eq_ker_factor:"Q = ker_pair Y (factor_map)"
proof 
  show " Q \<subseteq> ker_pair Y factor_map"
  proof
    fix u assume "u \<in> Q" then obtain x1 x2 where "(x1, x2)\<in>R" and u:"u=(f x1, f x2)"
      using Q_def by auto
    then obtain "f x1 \<in> Y" and "f x2 \<in> Y" and "factor_map (f x1) = factor_map (f x2)"
      by (metis compose_eq eqr.l_closed eqr.p_eq1 eqr.r_closed factor_maps_factors map.cod)
     then have "(f x1, f x2) \<in> ker_pair Y (factor_map)"
       unfolding ker_pair_def by blast
     then show "u \<in> ker_pair Y (factor_map)"
       by (simp add: u)
   qed
   show "ker_pair Y factor_map \<subseteq> Q"
   proof
     fix u assume "u \<in> ker_pair Y factor_map"
   then obtain y1 y2 where "y1 \<in> Y" and "y2 \<in> Y" and eq:"factor_map y1 = factor_map y2" and u:"u=(y1,y2)"
     unfolding ker_pair_def by blast
   then obtain x1 x2 where "x1 \<in> X" and "x2 \<in> X" and y1:"y1 = f x1" and y2:"y2 = f x2"
     using map.sur by blast 
   then obtain "(x1, x2)\<in>R"
     by (metis compose_eq eq eqr.p_equivalence factor_maps_factors)
   then show "u \<in> Q"
     using Q_def u y1 y2 by auto
 qed
qed

lemma q_eqr2:"equivalence_relation Y Q"
  by (simp add: equivalence_relationI q_eqr)

lemma q_cong:"cong Y (\<star>) Q"
proof(rule congI1)
  fix y1 y2 y3 y4 assume "(y1, y2) \<in> Q" and "(y3, y4) \<in> Q"
  then obtain x1 x2 x3 x4 where "x1 \<in> X" and "x2 \<in> X" and "x3 \<in> X" and "x4 \<in> X"and 
    y1:"y1 = f x1" and y2:"y2 = f x2" and y3:"y3 = f x3" and y4:"y4 = f x4" and  "(x1, x2)\<in>R" and "(x3, x4)\<in>R"
    by (meson Q_memE)
  then obtain "(x1 \<cdot> x3, x2 \<cdot> x4) \<in> R" and "f (x1 \<cdot> x3) = y1 \<star> y3" and "f (x2 \<cdot> x4) = y2 \<star> y4"
    using eqr.compatible map.cmp by presburger
  then show "(y1 \<star> y3, y2 \<star> y4) \<in> Q"
    using Q_def by fastforce
qed


sublocale domain_eqr:equivalence_relation X R
  by (simp add: eqr.equivalence_relation_axioms)

sublocale codomain_ker:kernel_pair factor_map Y "X/R"
  using factor_map_def h_def h_set_hom kernel_pair.intro set_morphismI1 by fastforce

sublocale codom_hom:semigroup_homomorphism "factor_map" Y "(\<star>)" "X/R" "(\<bullet>)"
  apply(unfold_locales)
  using factor_map_def h_def magma_hom1 by presburger

sublocale codom_quotient:quotient_semigroup Y "(\<star>)" Q
  using codom_hom.quotient_semigroup codomain_ker.ker_pair_ker q_eq_ker_factor by auto

notation codom_quotient.quotient_law ("\<otimes>")

sublocale semigroup_homomorphism "factor_map" "Y" "(\<star>)" "(X/R)" "(\<bullet>)"
  by (simp add: codom_hom.semigroup_homomorphism_axioms)

sublocale first_isomorphism:semigroup_homomorphism_fundamental "factor_map" "Y" "(\<star>)" "(X/R)" "(\<bullet>)"
  by (simp add: codom_hom.semigroup_homomorphism_axioms semigroup_homomorphism_fundamental_def)

lemma epi_then_iso:
  assumes A0:"f`X=Y"
  shows "semigroup_isomorphism codomain_ker.h (Y/Q) (\<otimes>) (X/R) (\<bullet>)"
  apply(unfold_locales)
  apply (simp add: codomain_ker.ker_pair_ker first_isomorphism.induced.dom q_eq_ker_factor)
  apply (simp add: codomain_ker.ker_pair_ker q_eq_ker_factor)
  apply (metis assms codomain_ker.ker_pair_ker eqr.proj_epi.sur factor_maps_factors first_isomorphism.induced.iso q_eq_ker_factor surj_compose)
  using codomain_ker.ker_pair_ker first_isomorphism.induced.cmp q_eq_ker_factor by force


end


subsection \<open>Image of Semigroups Congruence\<close>
locale semigroup_congruence_vimage_=
  map:semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)"+eqr:quotient_semigroup Y "(\<star>)" S
  for f and X and Y and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and S
begin
notation local.map.ker.kernel_pair_object ("R'(_')")
notation eqr.quotient_law ("\<bullet>")

lemma ker_pair_eq:"S = ker_pair Y (eqr.p)"  using eqr.eqr_eq_proj_ker by blast

definition "Q \<equiv> {(x, y) \<in> X \<times> X. (f x, f y) \<in> S}"

lemma q_vimage_comp:"Q = ker_pair X (compose X eqr.p f)"
  apply(auto simp add:Q_def ker_pair_def)
  apply (simp add: compose_eq eqr.p_eq1)
  apply (simp add: compose_eq eqr.p_eq1)
  by (simp add: compose_eq eqr.p_equivalence)

lemma q_eqr:"is_eqrel X Q" unfolding is_eqrel_def Q_def refl_on_def sym_def trans_def apply(auto)
  using eqr.sym apply presburger
  by (meson eqr.trn)

lemma q_eqr2:"equivalence_relation X Q"
  apply(unfold_locales)
  using Q_def apply force
  apply (simp add: Q_def)
  apply (simp add: Q_def eqr.sym)
  by (simp add: ker_pair_def q_vimage_comp)

lemma q_cong:"cong X (\<cdot>) Q"
  unfolding Q_def
  apply(rule congI1)
  using eqr.compatible map.cmp map.dom.closed by auto

lemma ker_sub_q:"R(f) \<subseteq> Q" unfolding Q_def  local.map.ker.kernel_pair_object_def  by fastforce

sublocale domain_eqr:equivalence_relation X Q 
  by (simp add: q_eqr2)

sublocale domain_ker:kernel_pair "(compose X eqr.p f)" X "Y/S"
  using eqr.proj_hom2 hom2 kernel_pair_def map.mem_hom set_morphismI1 by blast  

sublocale codom_hom:semigroup_homomorphism "(compose X eqr.p f)" X "(\<cdot>)" "Y/S" "(\<bullet>)"
  apply(unfold_locales)
  by (simp add: compose_eq eqr.proj_epi.cmp map.cmp map.dom.closed)

sublocale dom_quotient:quotient_semigroup X "(\<cdot>)" Q
  using codom_hom.quotient_semigroup domain_ker.ker_pair_ker q_vimage_comp by auto

notation dom_quotient.quotient_law ("\<otimes>")

sublocale semigroup_homomorphism "(compose X eqr.p f)" "X" "(\<cdot>)" "(Y/S)" "(\<bullet>)"
  using codom_hom.semigroup_homomorphism_axioms by blast

sublocale first_isomorphism:semigroup_homomorphism_fundamental "(compose X eqr.p f)" "X" "(\<cdot>)" "(Y/S)" "(\<bullet>)"
  by (simp add: codom_hom.semigroup_homomorphism_axioms semigroup_homomorphism_fundamental_def)

lemma epi_then_iso:
  assumes A0:"f`X=Y"
  shows "semigroup_isomorphism domain_ker.h (X/Q) (\<otimes>) (Y/S) (\<bullet>)"
  apply(unfold_locales)
  using domain_ker.ker_pair_ker domain_ker.quotient_map.dom q_vimage_comp apply presburger
  apply (simp add: domain_ker.ker_pair_ker q_vimage_comp)
  apply (metis assms domain_ker.ker_pair_ker eqr.proj_epi.sur_locale_axioms first_isomorphism.induced.iso q_vimage_comp sur_locale.sur surj_compose)
  using domain_ker.ker_pair_ker first_isomorphism.induced.cmp q_vimage_comp by force


end

section Monoids
subsection \<open>Monoid Locale\<close>
locale monoid=semigroup X "(\<cdot>)" for X and f (infixl "\<cdot>" 70) and e+
  assumes idin[intro,simp]:"e \<in> X" and
          lid[intro,simp]:"x \<in> X \<Longrightarrow> e \<cdot> x = x" and 
          rid[intro,simp]:"x \<in> X \<Longrightarrow> x \<cdot> e = x"
begin
definition invertible where "u \<in> X \<Longrightarrow> invertible u \<longleftrightarrow> (\<exists>v \<in> X. u \<cdot> v = e \<and> v \<cdot> u = e)"
definition inv where "inv = (\<lambda>u \<in> X. THE v. v \<in>X \<and> u \<cdot> v = e \<and> v \<cdot> u = e)"
definition set_inv where "set_inv H = (\<Union>h\<in>H. {inv h})"

definition "Units = {u \<in> X. invertible u}"
lemma mem_UnitsI: "\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> u \<in> Units"  unfolding Units_def by clarify
lemma mem_UnitsD:  "\<lbrakk> u \<in> Units \<rbrakk> \<Longrightarrow> invertible u \<and> u \<in> X"  unfolding Units_def by clarify
lemma isid:"id_elem e" by (simp add: id_elem_def)

lemma ltranslation_id:"l_trans e = Id X "
  by (simp add: id_elem_id_map(1) isid)  

lemma rtranslation_id:"r_trans e = Id X "
  by (simp add: id_elem_id_map(2) isid) 

lemma m_closed:"x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<cdot> y \<in> X"  
  by (simp add: closed)

lemma invertibleI[intro]:"\<lbrakk> u \<cdot> v = e; v \<cdot> u = e; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> invertible u"
  unfolding invertible_def by fast

lemma invertibleE[elim]: "\<lbrakk>invertible u; \<And>v. \<lbrakk> u \<cdot> v = e; v \<cdot> u = e; v \<in> X \<rbrakk> \<Longrightarrow> P; u \<in> X\<rbrakk> \<Longrightarrow> P" 
  unfolding invertible_def by fast

lemma inverse_unique:"\<lbrakk>u \<cdot> v' =e; v \<cdot> u = e; u \<in> X;  v \<in> X; v' \<in> X \<rbrakk> \<Longrightarrow> v = v'" 
  by (metis asc lid rid)

lemma inv_eq:"\<lbrakk>u \<cdot> v = e; v \<cdot> u = e; u \<in> X; v \<in> X \<rbrakk> \<Longrightarrow> inv u = v"
  unfolding inv_def using inverse_unique by simp blast

lemma unit_inv_closed[intro, simp]:"\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv u \<in> X" 
  using inv_eq by auto

lemma inverse_undefined[intro, simp]:"u \<notin> X \<Longrightarrow> inv u = undefined"  
  by (simp add: inv_def)

lemma unit_linv [simp]:"\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv u \<cdot> u = e" 
  using inv_eq by auto

lemma unit_rinv [simp]:"\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> u \<cdot> inv u = e" 
  using inv_eq by auto

lemma invertible_left_cancel[simp]:"\<lbrakk> invertible x; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow> x \<cdot> y = x \<cdot> z \<longleftrightarrow> y = z" 
  by (metis asc invertible_def lid)

lemma invertible_right_cancel [simp]:"\<lbrakk> invertible x; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow> y \<cdot> x = z \<cdot> x \<longleftrightarrow> y = z" 
  by (metis asc invertible_def rid)

lemma inv_ident[simp]:"inv e = e" using inv_eq lid by blast
lemma e_unit:"invertible e"  by auto

lemma invertible_inverse_invertible [intro, simp]:"\<lbrakk> invertible u; u \<in> X\<rbrakk> \<Longrightarrow> invertible (inv u)" 
  using unit_linv unit_rinv by blast

lemma invertible_inverse_inverse [simp]:"\<lbrakk> invertible u; u \<in> X \<rbrakk> \<Longrightarrow> inv (inv u) = u" 
  by (simp add: inv_eq)

lemma prod_rinv:"\<lbrakk>x \<in>X; y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot>((inv y) \<cdot> (inv x )) = e"
  by (simp add: assoc4)

lemma prod_linv:"\<lbrakk>x \<in>X; y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow> ((inv y) \<cdot> (inv x))\<cdot>(x \<cdot> y) = e"
  by (simp add: assoc4)

lemma prod_inv:
  "\<lbrakk>x \<in>X; y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = (inv y) \<cdot> (inv x )"
  using inv_eq m_closed prod_linv prod_rinv unit_inv_closed by presburger

lemma prod_invertible:
  "\<lbrakk>x \<in>X; y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow> invertible (x \<cdot> y)"
  by (meson invertibleI m_closed prod_linv prod_rinv unit_inv_closed)

lemma inv_rcancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> (inv x \<cdot> y) = y"
  by (simp add: associate3)

lemma inv_lcancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x \<cdot> (x \<cdot> y) = y"
  by (metis asc lid unit_inv_closed unit_linv)

lemma l_trans_inv1:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans x) (l_trans (inv x)) = Id X" 
  by (simp add: ltranslation_comp ltranslation_id)

lemma l_trans_inv2:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans (inv x)) (l_trans x) = Id X"  
  by (simp add: ltranslation_comp ltranslation_id) 

lemma r_trans_inv1:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans x) (r_trans (inv x)) = Id X" 
  by (simp add: rtranslation_comp rtranslation_id) 

lemma r_trans_inv2:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans (inv x)) (r_trans x) = Id X" 
  using rtranslation_comp rtranslation_id by auto 

lemma l_coset_id_prod:"H \<subseteq> X \<Longrightarrow> l_coset e H = H"
  apply(rule subset_antisym)
  using subset_eq apply fastforce
  by (metis l_coset_memI lid subset_eq)

lemma r_coset_id_prod:"H \<subseteq> X \<Longrightarrow> r_coset H e = H"
  apply(rule subset_antisym)
  using  subset_eq apply fastforce
  by (metis r_coset_memI rid subset_eq)

lemma r_coset_id[simp]: "A \<subseteq> X \<Longrightarrow> r_coset A e = A"
  by (simp add: r_coset_id_prod)

lemma l_coset_id[simp]: "A \<subseteq> X \<Longrightarrow> l_coset e A = A"
  by (simp add: l_coset_id_prod)

lemma r_set_prod_id[simp]: "A \<subseteq> X \<Longrightarrow> set_prod A {e} = A"
  using r_coset_id r_coset_singleton_prod by auto

lemma l_set_prod_id[simp]: "A \<subseteq> X \<Longrightarrow> set_prod {e} A = A"
  using l_coset_id l_coset_singleton_prod by auto

end



subsection \<open>Submonoid Locale\<close>
locale submonoid=monoid X "(\<cdot>)" e for A and X and f (infixl "\<cdot>" 70) and unit ("e") +
  assumes setsub:"A \<subseteq> X" and 
          opsub:"\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A" and  
          idsub:"e \<in> A"
begin
lemma subD[intro,simp]:"a \<in> A \<Longrightarrow> a \<in> X" using setsub by auto  

sublocale sub:monoid A "(\<cdot>)" e   by(unfold_locales)(auto simp add: opsub asc idsub)

lemma submonoid_invertible [intro, simp]:  "\<lbrakk> sub.invertible u; u \<in> A \<rbrakk> \<Longrightarrow> invertible u"
  using invertibleI by blast

lemma submonoid_inverse_closed [intro, simp]:  "\<lbrakk> sub.invertible u; u \<in> A \<rbrakk> \<Longrightarrow> inv u \<in> A" 
  using inv_eq by auto
end

subsection \<open>Monoid Homomorphisms\<close>

locale monoid_homomorphism=set_morphism f X Y+ dom:monoid X "(\<cdot>)" e+ cod:monoid Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and e and Y and codomain_law (infixl "\<star>" 70) and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)" and
          unt:"f e = d"
begin
sublocale magma_homomorphism f X "(\<cdot>)" Y "(\<star>)"
  by (simp add: cmp cod.magma_axioms dom.magma_axioms magma_homomorphism.intro 
      magma_homomorphism_axioms.intro set_morphism_axioms)

sublocale semigroup_homomorphism f X "(\<cdot>)" Y "(\<star>)"
  by (simp add: cmp cod.semigroup_axioms dom.semigroup_axioms semigroup_homomorphism_axioms_def 
      semigroup_homomorphism_def set_morphism_axioms)

lemma im_subsmonoid1:"submonoid A X (\<cdot>) e \<Longrightarrow> submonoid (f`A) Y (\<star>) d"  
  apply(unfold_locales)
  apply (simp add: maps_to_im maps_to_memI submonoid.subD)
  apply (simp add: dom.magma_axioms imag_comp submagmaI submonoid.opsub submonoid.setsub)
  by (metis rev_image_eqI submonoid.idsub unt)

lemma im_subsemigroup2:"submonoid B Y (\<star>) d \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow>submonoid (vimage f B) X (\<cdot>) e" 
proof-
  assume A0:"submonoid B Y (\<star>) d" and A1:"(vimage f B) \<subseteq> X"
  then show "submonoid (vimage f B) X (\<cdot>) e"
  apply(unfold_locales)
  using A1 apply blast
  apply (simp add: cmp submonoid.opsub subsetD)
  by (simp add: submonoid.idsub unt)
qed


lemma inverse_image_id1:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> (f x) \<star> (f (dom.inv x)) = d"  
  by (metis cmp dom.unit_inv_closed dom.unit_rinv unt)

lemma inverse_image_id2:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> (f (dom.inv x)) \<star> (f x) = d"  
  by (metis cmp dom.unit_inv_closed dom.unit_linv unt) 

lemma dom_inv_cod_inv:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> cod.invertible (f x)" 
  using inverse_image_id1 inverse_image_id2 by auto

lemma inv_comm:"x \<in> X \<Longrightarrow> dom.invertible x \<Longrightarrow> f (dom.inv x) = cod.inv (f x)" 
  by (metis cod cod.inv_eq dom.unit_inv_closed inverse_image_id1 inverse_image_id2)

sublocale im:submonoid "f`X" Y "(\<star>)" "f e"
  by (simp add: dom.m_closed dom.monoid_axioms im_subsmonoid1 submonoid.intro submonoid_axioms_def unt)


end


lemma submonoid_transitive[trans]:
  assumes "submonoid A B f e" and 
          "submonoid B C f e" 
  shows   "submonoid A C f e" 
proof-
  interpret A:submonoid A B f e by fact 
  interpret C:submonoid B C f e by fact 
  show ?thesis
    by (metis A.opsub A.setsub A.sub.idin C.monoid_axioms C.setsub submonoid.intro submonoid_axioms_def subset_trans)
qed


locale monoid_epimorphism=set_epimorphism f X Y+ dom:monoid X "(\<cdot>)" e+ cod:monoid Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and e and Y and codomain_law (infixl "\<star>" 70) and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)" and
          unt:"f e = d"
begin
sublocale monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d
  by (simp add: cmp cod.monoid_axioms dom.monoid_axioms monoid_homomorphism_axioms_def
      monoid_homomorphism_def set_morphism_axioms unt)

end

locale monoid_monomorphism=set_monomorphism f X Y+ dom:monoid X "(\<cdot>)" e+ cod:monoid Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and e and Y and codomain_law (infixl "\<star>" 70) and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)" and
          unt:"f e = d"
begin
sublocale monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d
  by (simp add: cmp cod.monoid_axioms dom.monoid_axioms monoid_homomorphism_axioms_def
      monoid_homomorphism_def set_morphism_axioms unt)
end

locale monoid_isomorphism=set_isomorphism f X Y+ dom:monoid X "(\<cdot>)" e+ cod:monoid Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and e and Y and codomain_law (infixl "\<star>" 70) and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)" and
          unt:"f e = d"
begin
sublocale monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d
  by (simp add: cmp cod.monoid_axioms dom.monoid_axioms monoid_homomorphism_axioms_def
      monoid_homomorphism_def set_morphism_axioms unt)
end

context set_endomorphisms
begin

end



locale transformation_monoid=set_endomorphisms E+submonoid M "set_morphisms E E" "compose E" "Id E" for M and E
begin
lemma tr_closed[intro,simp]:"\<lbrakk>f \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> f x \<in> E"  using hom9 by fastforce
lemma tr_undef[intro,simp]:"\<lbrakk>f \<in> M; x \<notin> E\<rbrakk> \<Longrightarrow> f x = undefined"  using hom10 by fastforce
end


locale monoid_clone=monoid
begin
sublocale transformation:set_endomorphisms X .

sublocale transformation:transformation_monoid "l_trans`X" X apply(unfold_locales)
  apply (simp add: hom3)
  apply (simp add: hom7)
  apply (simp add: hom5)
  apply (simp add: hom6)
    apply blast
  apply(auto simp add: image_iff )
  apply (metis left_trans_comp opposite.closed)
  using ltranslation_id by force


sublocale set_morphism l_trans X "l_trans`X"
  by (simp add: hom_memI1 set_morphismI1)

sublocale monoid_homomorphism l_trans X "(\<cdot>)" e  "l_trans`X" "compose X" "Id X"
  apply(unfold_locales)
  using left_trans_comp apply blast
  by (simp add: ltranslation_id)


sublocale iso:monoid_isomorphism l_trans X "(\<cdot>)" e  "l_trans`X" "compose X" "Id X"
  apply(unfold_locales)
    apply(simp add:bij_betw_def)
  apply(rule inj_onI)
  apply (metis idin magma.l_trans_app magma_axioms restrict_apply1 rtranslation_id)
  using left_trans_comp apply presburger
  by (simp add: unt)



end



locale monoid_operating_on_set= monoid M "(\<cdot>)" e+action M E \<alpha> 
  for M::"'a set" and 
      law::"'a\<Rightarrow>'a\<Rightarrow>'a" (infixl "\<cdot>" 70) and
      unit::"'a" ("e") and
      E::"'b set" and
      \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b" +
  assumes unid:"\<alpha> e = Id E" and
          comp:"\<lbrakk>x\<in>M;y\<in>M\<rbrakk> \<Longrightarrow> \<alpha> (x \<cdot> y) = compose E (\<alpha> x) (\<alpha> y)"

begin
sublocale morphisms_comp:monoid "(set_morphisms E E)" "(compose E)" "(Id E)"
  by (simp add: monoid_axioms.intro monoid_def semigroup.intro hom2 hom3 hom5 hom6 hom7 magma.intro 
      semigroup_axioms.intro)
end


lemma composition_monoid:"monoid (set_morphisms X X) (compose X) (Id X)"by(unfold_locales, auto simp add:hom2 hom3 hom5 hom6 hom7)

subsection \<open>Composition Monoid Locale\<close>

locale compositional_monoid =submonoid M "set_morphisms E E" "compose E" "Id E" for M and E
begin
lemma hom_mem:"f \<in> M \<Longrightarrow> f \<in> set_morphisms E E" using subD by blast
lemma eval_simp[intro, simp]:"f \<in> M  \<Longrightarrow> x \<in> E \<Longrightarrow> f x \<in> E" by(auto intro:  hom9)
lemma eval_ndef[intro,simp]:"f \<in> M \<Longrightarrow> x \<notin> E \<Longrightarrow> f x = undefined" using hom10 by fastforce
end


subsection \<open>Quotient Monoid Locale\<close>
locale quotient_monoid=
  monoid X "(\<cdot>)" e +
  equivalence_relation X R
  for X::"'a set" and 
      f::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70) and 
      R::"'a rel" and
      e::"'a"+
  assumes compat:"(x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (x1\<cdot>y1 , x2\<cdot>y2) \<in> R"
begin

sublocale quotient_magma X "(\<cdot>)" R
  by (simp add: compat equivalence_relation_axioms magma_axioms quotient_magma.intro quotient_magma_axioms_def)

sublocale quotient_semigroup X "(\<cdot>)" R
  by (simp add: compatible equivalence_relation_axioms quotient_semigroup.intro quotient_semigroup_axioms_def semigroup_axioms)

lemma quotient_lid:"\<And>t. t \<in> X / R \<Longrightarrow> (p e) \<bullet> t = t" by (metis idin lid qlaw3 rep_ex) 
lemma quotient_rid:"\<And>t. t \<in> X / R \<Longrightarrow> t \<bullet> (p e) = t" by (metis idin rid qlaw3 rep_ex) 
definition "H = p e"
lemma quotient_identity:"H \<in> X/R"  using H_def idin by blast

lemma quotient_id1:"\<And>t. t \<in> X / R \<Longrightarrow> H \<bullet> t = t" using H_def quotient_lid by presburger 
lemma quotient_id2:"\<And>t. t \<in> X / R \<Longrightarrow> t \<bullet> H = t" using H_def quotient_rid by presburger 

sublocale quotient:monoid "X/R" "(\<bullet>)" "H" by(unfold_locales) (auto simp add: quotient_id1 quotient_id2 quotient_identity)

sublocale proj:monoid_homomorphism \<pi> X "(\<cdot>)" e "(X/R)" "(\<bullet>)" H
  apply(unfold_locales)
  using proj.cmp apply presburger
  using H_def by auto

sublocale proj_epi:monoid_epimorphism \<pi> X "(\<cdot>)" e "(X/R)" "(\<bullet>)" H
  apply(unfold_locales)
  using proj_epi.cmp apply force
  by (simp add: H_def)


end


subsection \<open>First Isomorphism For Monoids\<close>

context monoid_homomorphism
begin
lemma quotient_monoid:"quotient_monoid X (\<cdot>) R(f) e"
  apply(unfold_locales)
  by (meson quotient_magma quotient_magma.compatible)
end

locale monoid_homomorphism_fundamental=monoid_homomorphism 
begin
sublocale quotient:quotient_monoid X "(\<cdot>)" "R(f)"  e  using quotient_monoid by blast
notation quotient.quotient_law (infixl "(\<bullet>)" 70)

lemma first_isomorphism_monoids1:"submonoid (f`X) Y (\<star>) (f e)"
  by (simp add: im.submonoid_axioms)

lemma first_isomorphism_monoids2:"cong X (\<cdot>) R(f)"  
  using ker_cong kernel_def by force

lemma first_isomorphism_monoids3a:"monoid_homomorphism (ker.h) (X/R(f)) (\<bullet>) quotient.H (f`X) (\<star>) (f e)"  
 apply(unfold_locales)
  using ker.quotient_map.dom apply blast
  apply auto
  apply (metis cmp dom.m_closed ker.eqr.psecE1 ker.eqr.sec_closed ker.h_simp quotient_magma quotient_magma.qlaw4)
  using quotient.H_def by auto

lemma first_isomorphism_monoids3b:"monoid_isomorphism ker.h (X/R(f)) (\<bullet>)quotient.H (f`X) (\<star>) (f e)"
  apply(unfold_locales)
  using ker.quotient_map.dom apply blast
    apply(auto)
  apply (metis bij_betw_imageI ker.factorization2 ker.quotient_map.inj quotient.proj_epi.sur surj_compose)
  apply (metis cmp dom.m_closed ker.eqr.psecE1 ker.eqr.sec_closed ker.h_simp quotient_magma quotient_magma.qlaw4)
  using quotient.H_def by auto

sublocale induced:monoid_isomorphism ker.h "X/R(f)" "(\<bullet>)" quotient.H "f`X" "(\<star>)" "f e"
  by (simp add: first_isomorphism_monoids3b)

lemma first_isomorphism_monoids:
  shows "submonoid (f`X) Y (\<star>) (f e)" and 
        "cong X (\<cdot>) R(f)" and
        "monoid_isomorphism ker.h (X/R(f)) (\<bullet>) quotient.H (f`X) (\<star>) (f e)"
  apply (simp add: first_isomorphism_monoids1)
  apply (simp add: first_isomorphism_monoids2)
  by (simp add: first_isomorphism_monoids3b)

lemma third_isomorphism_monoids2:
  assumes A0:"submonoid B Y (\<star>) d" and A1:"(vimage f B) \<subseteq> X"
  shows "vimage f B = (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
proof-
  let ?A="vimage f B"
  have B0:"\<And>x. x \<in>?A \<Longrightarrow> ker.eqr.p x \<subseteq>?A"
  proof-
    fix x assume x0:"x \<in> ?A" then obtain x1:"x \<in> X"
      using A1 by blast 
    show "ker.eqr.p x \<subseteq> ?A "
    proof
      fix y assume y0:"y \<in> ker.eqr.p x"
      then obtain "f x = f y"
        by (meson ker.h_eq ker.eqr.p_D1 ker.eqr.p_closed1 ker.eqr.p_eq1 x1)
      then show "y \<in> ?A"
        using x0 by auto
    qed
  qed
  then have B1:"(\<Union>x \<in> (vimage f B). ker.eqr.p x) \<subseteq> ?A"
    by blast
  have B2:"\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ker.eqr.p x"
    using A1 by force
  then have B3:"?A \<subseteq> (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
    by blast
  then show ?thesis
    using B1 by blast
qed

lemma third_isomorphism_semigroups:
  shows "\<And>A. submonoid A X (\<cdot>) e \<Longrightarrow> submonoid (f`A) Y (\<star>) (f e)" and
        "\<And>B. submonoid B Y (\<star>) d \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow> submonoid (vimage f B) X (\<cdot>) e \<and> 
             (vimage f B) = (\<Union>x \<in> (vimage f B). ker.eqr.p x)"
  apply (simp add: im_subsemigroup1)
  apply (simp add: im_subsmonoid1 unt)
  using im_subsemigroup2 third_isomorphism_monoids2 by force

end


subsection \<open>Monoid Epimorphism Factoring\<close>


locale monoid_epimorphism_factoring=
  map:monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d+epi:monoid_epimorphism g X "(\<cdot>)" e Z "(\<bullet>)" c
  for f and g and X and Y and Z and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and law3 (infixl "\<bullet>" 70)
  and e and d and c+
  assumes ker_sub:"ker_pair X g \<subseteq> ker_pair X f"
begin

definition "h \<equiv> compose Z f (rinv g X Z)"

lemma h_set_hom:"h \<in>set_morphisms Z Y"
  by (metis h_def hom2 map.mem_hom epi.right_inv_is_set_morphism epi.right_inverse_def)

lemma hg_set_hom:"compose X h g \<in> set_morphisms X Y"  using h_set_hom hom2 epi.mem_hom by blast 
lemma compat:"\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X;g x1 = g x2\<rbrakk> \<Longrightarrow> f x1 = f x2"  using ker_sub unfolding ker_pair_def by auto


lemma h_eq1:"\<And>x. x \<in> X \<Longrightarrow> f x = h (g x)"
  unfolding h_def using compat epi.sur surj_implies_factors(2)[of g X Z f] by blast

lemma h_eq2:"\<And>x. x \<in> X \<Longrightarrow> f x = (compose X h g) x"
  by (simp add: compose_eq h_eq1)

lemma h_eq3:"compose X h g = f"
proof-
  obtain B5:"f \<in> set_morphisms X Y" and B6:"g \<in> set_morphisms X Z"
    by (simp add: map.mem_hom epi.mem_hom) 
  then show ?thesis
    by (metis fun_eqI h_eq2 hg_set_hom)
qed  

lemma monoid_hom0:"\<And>x1 x2. \<lbrakk>x1\<in>X;x2\<in>X\<rbrakk> \<Longrightarrow>h ((g x1) \<bullet> (g x2)) = (h (g x1))\<star>(h (g x2)) "
  using h_eq1 map.cmp map.dom.closed epi.cmp by force

lemma monoid_hom1:"\<And>z1 z2. \<lbrakk>z1\<in>Z;z2\<in>Z\<rbrakk> \<Longrightarrow>h (z1\<bullet>z2) = (h z1) \<star> (h z2) "
proof-
  fix z1 z2 assume z10:"z1 \<in> Z" and z20:"z2 \<in> Z"
  then obtain x1 x2 where "x1 \<in> X" and "z1 = g x1" and "x2 \<in> X" and "z2 = g x2"
    using epi.sur by blast
  then show "h (z1\<bullet>z2) = (h z1) \<star> (h z2) "
    by (simp add: monoid_hom0)
qed

lemma monoid_hom2:"h c = d"
  using epi.unt h_eq1 map.unt by auto

lemma monoid_hom:"monoid_homomorphism h Z (\<bullet>) c  Y (\<star>) d"
  apply(unfold_locales)
  apply (meson h_set_hom hom10)
  apply (meson h_set_hom hom9)
  using monoid_hom1 apply blast
  using monoid_hom2 by blast

end

subsection \<open>Monoid Monomorphism Factoring\<close>
locale monoid_monomorphism_factoring=
  map:monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d +mono:monoid_monomorphism g Z "(\<bullet>)" c Y "(\<star>)" d
  for f and g and X and Y and Z and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and law3 (infixl "\<bullet>" 70) and e and d and c+
  assumes im_sub:"f`X \<subseteq> g`Z"
begin

definition "h \<equiv> compose X (rinv g Z Y) f"

lemma g_inj:"inj_on g Z"
  by simp

lemma h_set_hom:"h \<in>set_morphisms X Z"
  by (simp add: h_def inj_implies_factors_concrete(2) im_sub map.mem_hom mono.mem_hom)

lemma gh_set_hom:"compose X g h \<in> set_morphisms X Y"
  using h_set_hom hom2 mono.mem_hom by blast 

lemma h_eq1:"\<And>x. x \<in> X \<Longrightarrow> f x = g (compose X (rinv g Z Y) f x) "
proof-
  fix x assume x0:"x \<in> X"
  then have "f x = g ((rinv g Z Y) (f x))"
    by (meson g_inj im_sub inj_implies_factors_concrete(1) map.mem_hom mono.mem_hom)
  also have "... = g (compose X (rinv g Z Y) f x)"
    by (simp add: compose_eq x0)
  finally show "f x = g (compose X (rinv g Z Y) f x)"
    by blast
qed

lemma h_eq2:"\<And>x. x \<in> X \<Longrightarrow> f x = g (h x)"
  using h_def h_eq1 by force

lemma h_eq3:"\<And>x. x \<in> X \<Longrightarrow> f x = (compose X g h) x"
  by (simp add: compose_eq h_eq2)

lemma h_eq4:"compose X g h = f"
proof-
  obtain B5:"f \<in> set_morphisms X Y" and B6:"g \<in> set_morphisms Z Y"
    by (simp add: map.mem_hom mono.mem_hom) 
  then show ?thesis
    by (metis g_inj h_def im_sub inj_implies_factors_concrete(5))
qed  


lemma monoid_hom1:"\<And>x1 x2. \<lbrakk>x1\<in>X;x2\<in>X\<rbrakk> \<Longrightarrow>h (x1\<cdot>x2) = (h x1) \<bullet> (h x2) "
proof-
  fix x1 x2 assume x10:"x1 \<in> X" and x20:"x2 \<in> X"
  then obtain "f x1 \<in> Y" and "f x2 \<in> Y" and h0:"h x1 \<in> Z" and h1:"h x2 \<in> Z"
    by (meson h_set_hom hom9 map.mem_hom) 
  let ?r="rinv g Z Y"
  have B0:"h  (x1\<cdot>x2) = ?r (f(x1 \<cdot> x2))"
    by (simp add: compose_eq h_def map.dom.closed x10 x20)
  also have B1:"... = ?r ((f x1) \<star> (f x2))"
    by (simp add: map.cmp x10 x20)
  also have "... = ?r ((g (h x1)) \<star>( g (h x2)))"
    using h_eq2 x10 x20 by force
  also have "... = ?r (g ((h x1) \<bullet> (h x2)))"
    by (simp add: h0 h1 mono.cmp)
   also have "... = ((h x1) \<bullet> h (x2))"
     using h0 h1 mono.dom.closed mono.left_inverse_comp3 mono.left_inverse_def by force
  finally show "h (x1\<cdot>x2) = (h x1) \<bullet> (h x2) "
    by simp
qed

lemma monoid_hom2:"h e = c"
  by (metis compose_eq h_def map.cod.id_elem_unique map.dom.idin map.im.idin map.im.isid mono.dom.idin mono.im.idin mono.im.isid mono.left_inverse_def mono.set_monomorphism_axioms set_monomorphism.left_inverse_comp3)

lemma monoid_hom3:"monoid_homomorphism h X (\<cdot>) e  Z (\<bullet>) c"
  apply(unfold_locales)
  apply (meson h_set_hom hom10)
  apply (meson h_set_hom hom9)
  using monoid_hom1 apply blast
  using monoid_hom2 by blast



end



subsection \<open>Preimage of Monoid Congruence\<close>

locale monoid_epimorphism_congruence_image=
  map:monoid_epimorphism f X "(\<cdot>)" e Y "(\<star>)" d+eqr:quotient_monoid X "(\<cdot>)" R e
  for f and X and Y and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and R and e and d+
  assumes sub:"(ker_pair X f ) \<subseteq> R"
begin
notation local.map.ker.kernel_pair_object ("R'(_')")
notation eqr.quotient_law ("\<bullet>")

lemma f_ker_coarser:"ker_pair X f \<subseteq> ker_pair X eqr.p"
  using eqr.eqr_eq_proj_ker sub by auto

sublocale monoid_epimorphism_factoring eqr.p f X "X/R" Y "(\<cdot>)" "(\<bullet>)" "(\<star>)" e eqr.H d
  by(unfold_locales;simp add:f_ker_coarser)

definition factor_map where "factor_map \<equiv> compose Y eqr.p (rinv f X Y)"

definition "Q\<equiv> {(f x, f y)|x y. (x,y) \<in> R}"

lemma Q_memE:assumes "(y1, y2)\<in>Q"
  obtains x1 x2 where "x1 \<in> X" and "x2 \<in> X" and "y1 = f x1" and "y2 = f x2" and "(x1, x2)\<in>R"
  using Q_def assms eqr.l_closed eqr.r_closed by auto

lemma Q_refl_on:"refl_on Y Q"
  unfolding refl_on_def Q_def using map.sur by(blast)

lemma Q_sym:"sym Q"
  unfolding Q_def sym_def using eqr.sym by(blast)

lemma Q_trans:"trans Q"
proof(rule transI)
  fix y1 y2 y3 assume xy:"(y1, y2) \<in> Q" and yz:"(y2, y3) \<in> Q" 
  then obtain x1 x2 x3 where "x1 \<in> X" and "x2 \<in> X" and "x3 \<in> X" and y1:"y1 = f x1" and "y2 = f x2" and
                             y3:"y3 = f x3"
    by (meson Q_memE)
  then obtain x12:"(x1, x2)\<in>R" and x23:"(x2, x3)\<in>R"
    by (metis Q_memE compat eqr.p_equivalence xy yz)
  then obtain "(x1, x3)\<in>R"
    using eqr.trn by blast
  then show "(y1, y3) \<in> Q"
    using Q_def y1 y3 by auto
qed

lemma q_eqr:"is_eqrel Y Q"
  by (simp add: Q_refl_on Q_sym Q_trans is_eqrel_def) 

lemma factor_maps_factors:"compose X (factor_map) f = eqr.p"
  using factor_map_def h_def h_eq3 by auto

lemma q_eq_ker_factor:"Q = ker_pair Y (factor_map)"
proof 
  show " Q \<subseteq> ker_pair Y factor_map"
  proof
    fix u assume "u \<in> Q" then obtain x1 x2 where "(x1, x2)\<in>R" and u:"u=(f x1, f x2)"
      using Q_def by auto
    then obtain "f x1 \<in> Y" and "f x2 \<in> Y" and "factor_map (f x1) = factor_map (f x2)"
      by (metis compose_eq eqr.l_closed eqr.p_eq1 eqr.r_closed factor_maps_factors map.cod)
     then have "(f x1, f x2) \<in> ker_pair Y (factor_map)"
       unfolding ker_pair_def by blast
     then show "u \<in> ker_pair Y (factor_map)"
       by (simp add: u)
   qed
   show "ker_pair Y factor_map \<subseteq> Q"
   proof
     fix u assume "u \<in> ker_pair Y factor_map"
   then obtain y1 y2 where "y1 \<in> Y" and "y2 \<in> Y" and eq:"factor_map y1 = factor_map y2" and u:"u=(y1,y2)"
     unfolding ker_pair_def by blast
   then obtain x1 x2 where "x1 \<in> X" and "x2 \<in> X" and y1:"y1 = f x1" and y2:"y2 = f x2"
     using map.sur by blast 
   then obtain "(x1, x2)\<in>R"
     by (metis compose_eq eq eqr.p_equivalence factor_maps_factors)
   then show "u \<in> Q"
     using Q_def u y1 y2 by auto
 qed
qed

lemma q_eqr2:"equivalence_relation Y Q"
  by (simp add: equivalence_relationI q_eqr)

lemma q_cong:"cong Y (\<star>) Q"
proof(rule congI1)
  fix y1 y2 y3 y4 assume "(y1, y2) \<in> Q" and "(y3, y4) \<in> Q"
  then obtain x1 x2 x3 x4 where "x1 \<in> X" and "x2 \<in> X" and "x3 \<in> X" and "x4 \<in> X"and 
    y1:"y1 = f x1" and y2:"y2 = f x2" and y3:"y3 = f x3" and y4:"y4 = f x4" and  "(x1, x2)\<in>R" and "(x3, x4)\<in>R"
    by (meson Q_memE)
  then obtain "(x1 \<cdot> x3, x2 \<cdot> x4) \<in> R" and "f (x1 \<cdot> x3) = y1 \<star> y3" and "f (x2 \<cdot> x4) = y2 \<star> y4"
    using eqr.compatible map.cmp by presburger
  then show "(y1 \<star> y3, y2 \<star> y4) \<in> Q"
    using Q_def by fastforce
qed


sublocale domain_eqr:equivalence_relation X R
  by (simp add: eqr.equivalence_relation_axioms)

sublocale codomain_ker:kernel_pair factor_map Y "X/R"
  using factor_map_def h_def h_set_hom kernel_pair.intro set_morphismI1 by fastforce

sublocale codom_hom:monoid_homomorphism "factor_map" Y "(\<star>)" "d" "X/R" "(\<bullet>)" "eqr.H"
  apply(unfold_locales)
  using factor_map_def h_def monoid_hom1 apply presburger
  using factor_map_def h_def monoid_hom2 by force

sublocale codom_quotient:quotient_monoid Y "(\<star>)" Q d
  using codomain_ker.ker_pair_ker factor_map_def h_def monoid_hom monoid_homomorphism.quotient_monoid q_eq_ker_factor by fastforce

notation codom_quotient.quotient_law ("\<otimes>")
notation codom_quotient.H ("G")

sublocale monoid_homomorphism "factor_map" "Y" "(\<star>)" "d" "(X/R)" "(\<bullet>)" "eqr.H"
  using codom_hom.monoid_homomorphism_axioms by auto

sublocale first_isomorphism:monoid_homomorphism_fundamental "factor_map" "Y" "(\<star>)" "d"  "(X/R)" "(\<bullet>)" "eqr.H"
  using codom_hom.monoid_homomorphism_axioms monoid_homomorphism_fundamental_def by force

lemma epi_then_iso:
  assumes A0:"f`X=Y"
  shows "monoid_isomorphism codomain_ker.h (Y/Q) (\<otimes>) G (X/R) (\<bullet>) eqr.H"
  apply(unfold_locales)                                           
  apply (simp add: codomain_ker.ker_pair_ker first_isomorphism.induced.dom q_eq_ker_factor)
  apply (simp add: codomain_ker.ker_pair_ker q_eq_ker_factor)
  apply (metis assms codomain_ker.ker_pair_ker eqr.proj_epi.sur factor_maps_factors first_isomorphism.induced.iso q_eq_ker_factor surj_compose)
  using codomain_ker.ker_pair_ker first_isomorphism.induced.cmp q_eq_ker_factor apply force
  using codom_hom.unt codomain_ker.ker_pair_ker first_isomorphism.induced.unt q_eq_ker_factor by force

end


subsection \<open>Image of Monoid Congruence\<close>
locale monoid_congruence_vimage=
  map:monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d+eqr:quotient_monoid Y "(\<star>)" S d
  for f and X and Y and law1 (infixl "\<cdot>" 70) and law2 (infixl "\<star>" 70) and S and e and d
begin
notation local.map.ker.kernel_pair_object ("R'(_')")
notation eqr.quotient_law ("\<bullet>")

lemma ker_pair_eq:"S = ker_pair Y (eqr.p)"  using eqr.eqr_eq_proj_ker by blast

definition "Q \<equiv> {(x, y) \<in> X \<times> X. (f x, f y) \<in> S}"

lemma q_vimage_comp:"Q = ker_pair X (compose X eqr.p f)"
  apply(auto simp add:Q_def ker_pair_def)
  apply (simp add: compose_eq eqr.p_eq1)
  apply (simp add: compose_eq eqr.p_eq1)
  by (simp add: compose_eq eqr.p_equivalence)

lemma q_eqr:"is_eqrel X Q" unfolding is_eqrel_def Q_def refl_on_def sym_def trans_def apply(auto)
  using eqr.sym apply presburger
  by (meson eqr.trn)

lemma q_eqr2:"equivalence_relation X Q"
  apply(unfold_locales)
  using Q_def apply force
  apply (simp add: Q_def)
  apply (simp add: Q_def eqr.sym)
  by (simp add: ker_pair_def q_vimage_comp)

lemma q_cong:"cong X (\<cdot>) Q"
  unfolding Q_def
  apply(rule congI1)
  using eqr.compatible map.cmp map.dom.closed by auto

lemma ker_sub_q:"R(f) \<subseteq> Q" unfolding Q_def  local.map.ker.kernel_pair_object_def  by fastforce

sublocale domain_eqr:equivalence_relation X Q 
  by (simp add: q_eqr2)

sublocale domain_ker:kernel_pair "(compose X eqr.p f)" X "Y/S"
  using eqr.proj_hom2 hom2 kernel_pair_def map.mem_hom set_morphismI1 by blast  

sublocale codom_hom:monoid_homomorphism "(compose X eqr.p f)" X "(\<cdot>)" "e"  "Y/S" "(\<bullet>)" "eqr.H"
  apply(unfold_locales)
  apply (simp add: compose_eq eqr.proj_epi.cmp map.cmp map.dom.m_closed)
  by (simp add: compose_eq eqr.proj_epi.unt map.unt)

sublocale dom_quotient:quotient_monoid X "(\<cdot>)" Q e
  using codom_hom.quotient_monoid domain_ker.ker_pair_ker q_vimage_comp by auto

notation dom_quotient.quotient_law ("\<otimes>")

sublocale monoid_homomorphism "(compose X eqr.p f)" "X" "(\<cdot>)" e "(Y/S)" "(\<bullet>)" eqr.H
  using codom_hom.monoid_homomorphism_axioms by blast

sublocale first_isomorphism:monoid_homomorphism_fundamental "(compose X eqr.p f)" "X" "(\<cdot>)" e "(Y/S)" "(\<bullet>)" eqr.H
  by (simp add: codom_hom.monoid_homomorphism_axioms monoid_homomorphism_fundamental_def)

lemma epi_then_iso:
  assumes A0:"f`X=Y"
  shows "monoid_isomorphism domain_ker.h (X/Q) (\<otimes>) dom_quotient.H (Y/S) (\<bullet>) eqr.H"
  apply(unfold_locales)
  using domain_ker.ker_pair_ker domain_ker.quotient_map.dom q_vimage_comp apply presburger
  apply (simp add: domain_ker.ker_pair_ker q_vimage_comp)
  apply (metis assms domain_ker.ker_pair_ker eqr.proj_epi.sur_locale_axioms first_isomorphism.induced.iso q_vimage_comp sur_locale.sur surj_compose)
  using domain_ker.ker_pair_ker first_isomorphism.induced.cmp q_vimage_comp apply auto[1]
  using codom_hom.unt domain_ker.ker_pair_ker first_isomorphism.induced.unt q_vimage_comp by auto

end


section Groups
subsection \<open>Group Locale\<close>
locale group = 
  monoid X "(\<cdot>)" e for X and f (infixl "\<cdot>" 70) and unit ("e") + 
  assumes invertible [simp, intro]: "u \<in> X \<Longrightarrow> invertible u"
begin

lemma l_cancel1:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X; a\<cdot>x=a\<cdot>y\<rbrakk> \<Longrightarrow> x = y " by simp
lemma r_cancel1:"\<lbrakk>b \<in> X; x \<in> X; y \<in> X;x\<cdot>b=y\<cdot>b\<rbrakk> \<Longrightarrow> x = y " by simp
lemma inv2_prod:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> inv (a \<cdot> inv b) \<in> X" using closed by fastforce
lemma insert_id1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (c \<cdot> inv c) \<cdot>b " by fastforce 
lemma insert_id2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (inv c \<cdot> c) \<cdot>b " by fastforce 
lemma remove_id1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> (a \<cdot> inv c) \<cdot> (c \<cdot> b) = a \<cdot>b " by (simp add: assoc4)
lemma remove_id2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> (a \<cdot> c) \<cdot> (inv c \<cdot> b) = a \<cdot>b " by (simp add: assoc4)
lemma l_inv_ex[simp]:"x \<in> X \<Longrightarrow> \<exists>y \<in> X. y \<cdot>x  = e" using unit_linv by blast
lemma r_inv_ex[simp]:"x \<in> X \<Longrightarrow> \<exists>y \<in> X. x\<cdot>y  = e" using unit_rinv by blast
lemma l_inv_simp[simp]:"x \<in> X \<Longrightarrow> inv x \<cdot> x = e"  using unit_linv by blast
lemma inv_id_iff[simp]:"x \<in> X \<Longrightarrow> inv x = e \<longleftrightarrow> x = e" using invertible_inverse_inverse by fastforce
lemma r_inv_simp[simp]:"x \<in> X \<Longrightarrow> x \<cdot> inv x = e" using unit_rinv by blast
lemma r_cancel2[simp]:"\<lbrakk>x \<in>X; y \<in>X; z \<in>X\<rbrakk> \<Longrightarrow> y\<cdot>x = z \<cdot> x \<longleftrightarrow> y = z" by auto
lemma l_cancel2[simp]:"\<lbrakk>x \<in>X; y \<in>X; z \<in>X\<rbrakk> \<Longrightarrow> x\<cdot>y =x\<cdot>z \<longleftrightarrow> y = z" by auto
lemma double_inv[simp]:"x \<in> X \<Longrightarrow> inv (inv x) = x" by simp
lemma inv_commute:"\<lbrakk>x \<cdot> y  = e; x \<in> X ; y \<in> X\<rbrakk> \<Longrightarrow> y \<cdot> x = e" using l_inv_ex local.inverse_unique by blast
lemma inv_eq:"\<lbrakk>y \<cdot> x =e; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x = y"  using inv_commute inv_eq by blast
lemma inv_lsolve1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a=inv b \<cdot> c \<longleftrightarrow> c=b \<cdot> a" using inv_lcancel inv_rcancel by force  
lemma inv_rsolve1:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> a=b \<cdot> inv c \<longleftrightarrow> b=a \<cdot> c" using asc by auto 
lemma inv_lsolve2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> inv b \<cdot> c=a \<longleftrightarrow> c=b \<cdot> a" using inv_lcancel inv_rcancel by force  
lemma inv_rsolve2:"\<lbrakk>a\<in>X;b\<in>X;c\<in>X\<rbrakk> \<Longrightarrow> b \<cdot> inv c=a \<longleftrightarrow> b=a \<cdot> c" using asc by auto 
lemma set_inv_sub:"H \<subseteq> X \<Longrightarrow> set_inv H \<subseteq> X" unfolding set_inv_def by blast
lemma set_inv_iso:"A \<subseteq> B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> set_inv A \<subseteq> set_inv B" unfolding set_inv_def   by blast
lemma set_inv_memI1:"H \<subseteq> X \<Longrightarrow> (\<exists>h \<in> H. x = inv h) \<Longrightarrow> x \<in> set_inv H"  by (simp add: set_inv_def)
lemma set_inv_memI2:"H \<subseteq> X \<Longrightarrow> h \<in> H \<Longrightarrow> x = inv h \<Longrightarrow> x \<in> set_inv H"  using set_inv_memI1 by blast

lemma inv_prod_l_coset1:
  "\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;l_coset (inv x \<cdot> y) H = H\<rbrakk> \<Longrightarrow> l_coset x H = l_coset y H"
  by (metis inv_rcancel invertible l_coset_assoc m_closed unit_inv_closed) 

lemma inv_prod_r_coset1:
  "\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;r_coset H (x \<cdot> inv y) = H\<rbrakk> \<Longrightarrow> r_coset H x = r_coset H y"
  by (metis group.inv_rsolve1 group_axioms invertible m_closed r_coset_assoc unit_inv_closed)  

lemma inv_prod_l_coset2:"\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;l_coset x H = l_coset y H\<rbrakk> \<Longrightarrow> l_coset (inv x \<cdot> y) H = H"  
  by (metis invertible l_coset_assoc l_coset_id_prod l_inv_simp monoid.unit_inv_closed monoid_axioms) 

lemma inv_prod_r_coset2:"\<lbrakk>x \<in> X;y \<in> X;H \<subseteq> X;r_coset H x = r_coset H y\<rbrakk> \<Longrightarrow> r_coset H (x \<cdot> inv y) = H" 
  by (metis invertible monoid.unit_inv_closed monoid_axioms r_coset_assoc r_coset_id_prod r_inv_simp) 

lemma l_trans_inj1:"\<And>g h. g \<in> X \<Longrightarrow> h \<in> X \<Longrightarrow> l_trans g = l_trans h \<Longrightarrow> g = h"
  by (metis id1 idin l_trans_app rtranslation_id)

lemma r_trans_inj2:"\<And>g h. g \<in> X \<Longrightarrow> h \<in> X \<Longrightarrow> r_trans g = r_trans h \<Longrightarrow> g = h"
  by (metis id2 idin lr_trans_dual ltranslation_id opposite.lr_trans_dual opposite.r_trans_app)

end

subsection Monoid_subgroup
locale monoid_subgroup=
  submonoid A X "(\<cdot>)" e+sub: group A "(\<cdot>)" e for A and X and f (infixl "\<cdot>" 70) and unit ("e")
begin
lemma monoid_subgroup_inv_eq [simp]:  
  "u \<in> A \<Longrightarrow> inv u = sub.inv u" by (simp add: inv_eq)
lemma monoid_subgroup_inverse_iff [simp]: 
  "\<lbrakk>invertible x; x \<in> X \<rbrakk> \<Longrightarrow> inv x \<in> A\<longleftrightarrow> x \<in> A" 
  using invertible_inverse_inverse sub.unit_inv_closed by fastforce
end 

lemma monoid_subgroup_transitive [trans]:
  assumes "monoid_subgroup K H f e" and
          "monoid_subgroup H G f e" shows 
          "monoid_subgroup K G f e"
proof-
  interpret K: monoid_subgroup K H f e by fact interpret H: monoid_subgroup H G f e by fact 
  show ?thesis
    by (meson H.submonoid_axioms K.sub.group_axioms K.submonoid_axioms monoid_subgroup.intro submonoid_transitive)
qed

context monoid begin

lemma monoid_subgroupI2:
  fixes A
  assumes subset [THEN subsetD, intro]: "A \<subseteq> X"
    and [intro]: "e \<in> A"
    and [intro]: "\<And>g h. \<lbrakk> g \<in> A; h \<in> A\<rbrakk> \<Longrightarrow> g \<cdot> h \<in> A"
    and [intro]: "\<And>g. g \<in> A \<Longrightarrow> invertible g"
    and [intro]: "\<And>g. g \<in> A \<Longrightarrow> inv g \<in> A"
  shows "monoid_subgroup A X (\<cdot>) e"
proof -
  interpret sub: monoid A "(\<cdot>)" e  by(unfold_locales,auto,simp add: asc subset)
  show ?thesis
    apply(unfold_locales)
       apply(auto)
    using unit_linv unit_rinv by blast
qed

interpretation units: monoid_subgroup Units X f e
  apply(rule monoid_subgroupI2)
  apply (simp add: Units_def)
  apply (simp add: e_unit mem_UnitsI)
  apply (meson m_closed mem_UnitsD mem_UnitsI prod_invertible)
  apply (simp add: mem_UnitsD)
  using mem_UnitsD mem_UnitsI by blast
 
lemma prod_unit[simp, intro]:
  "\<lbrakk>invertible x; invertible y; x \<in> X; y \<in>X \<rbrakk> \<Longrightarrow> invertible (x \<cdot> y)"
  by (simp add: monoid.prod_invertible monoid_axioms)
lemma group_of_units:"group Units f e"  by (simp add: units.sub.group_axioms)

lemma unit_rinv2:"\<lbrakk>invertible u; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> u \<cdot> ((inv u) \<cdot> v) = v" using inv_rcancel by blast  
lemma unit_rinv3:"\<lbrakk>invertible u; u \<in> X; v \<in> X\<rbrakk> \<Longrightarrow> (u \<cdot> (inv u)) \<cdot> v = v" by auto 
lemma unit_linv2: "\<lbrakk> invertible u; u \<in> X; v\<in>X\<rbrakk> \<Longrightarrow> (inv u) \<cdot> (u \<cdot> v) = v" using inv_lcancel by blast 
lemma unit_linv3: "\<lbrakk> invertible u; u \<in> X; v\<in>X\<rbrakk> \<Longrightarrow> ((inv u \<cdot> u)) \<cdot> v = v"  using lid unit_linv by presburger
lemma units_prod[simp]:"\<lbrakk>x \<in> X;y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow>inv (x \<cdot> y) = inv y \<cdot> inv x "  using prod_inv by blast
end

context compositional_monoid
begin
lemma invertible_is_bijective:assumes dom: "u \<in> set_morphisms E E" shows "invertible u \<longleftrightarrow> bij_betw u E E" 
proof-  
  from dom interpret set_morphism u E E  by (metis (full_types) hom10 hom9 set_morphism_def)
  show "invertible u \<longleftrightarrow> bij_betw u E E"  using bij_betw_iff_has_inverse mem_hom by blast
qed
lemma Units_bijective: "Units = {u \<in>  set_morphisms E E. bij_betw u E E}"  unfolding Units_def by (auto simp add: invertible_is_bijective)
lemma Units_bij_betwI [intro, simp]: "u \<in> Units \<Longrightarrow> bij_betw u E E" by (simp add: Units_bijective)
lemma Units_bij_betwD [dest, simp]: "\<lbrakk>u \<in> set_morphisms E E; bij_betw u E E \<rbrakk> \<Longrightarrow> u \<in> Units" unfolding Units_bijective by simp
sublocale symmetric: group "Units" "compose E" "Id E"  by (simp add: group_of_units) 
end

locale compositional_group = compositional_monoid M E+monoid_subgroup M Units "compose E" "Id E" for M and E
begin
lemma compositional_group_closed [intro, simp]: "\<lbrakk>u \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> u x \<in> E" using bij_betwE by blast
lemma compositional_group_undef [intro, simp]:  "\<lbrakk>u \<in> M; x \<notin> E\<rbrakk> \<Longrightarrow> u x = undefined"  by simp
end

subsection \<open>Subgroup Locale\<close>
locale subgroup=group G "(\<cdot>)" e for H and G and f (infixl "\<cdot>" 70) and unit ("e")+
  assumes subset:"H \<subseteq> G" and
          closed:"\<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a\<cdot>b \<in> H" and
          id_mem:"e \<in> H" and
          inv_cl:"a \<in> H \<Longrightarrow> inv a \<in> H"
begin
lemma sub_mem[intro,simp]:"a \<in> H \<Longrightarrow> a \<in> G" using subset by auto
sublocale sub:group H "(\<cdot>)" e
  by (metis closed id_mem inv_cl invertible monoid_subgroup.axioms(2) monoid_subgroupI2 sub_mem subset) 
lemma subgroup_inv_eq [simp]: "u \<in> H \<Longrightarrow> inv u = sub.inv u"  by (simp add: inv_eq)
lemma subgroup_is_group1:"group H (\<cdot>) e" by (simp add: sub.group_axioms)

end


context group
begin
lemma l_coset_absorb:"x \<in> X \<Longrightarrow> subgroup H X (\<cdot>) e \<Longrightarrow> l_coset x H =H \<Longrightarrow> x \<in> H"
  by (metis l_coset_memI rid subgroup.id_mem) 

lemma r_coset_absorb:"x \<in> X \<Longrightarrow> subgroup H X (\<cdot>) e \<Longrightarrow> r_coset H x =H \<Longrightarrow> x \<in> H"
  by (metis lid r_coset_memI subgroup.id_mem)  

lemma r_coset_rel1:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; r_coset A (x \<cdot> (inv y)) = A\<rbrakk> \<Longrightarrow>r_coset A x = r_coset A y"
  using inv_prod_r_coset1 by presburger

lemma l_coset_rel1:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; l_coset (inv y \<cdot> x) A = A\<rbrakk> \<Longrightarrow>l_coset x A = l_coset y A" 
  by (metis closed invertible unit_inv_closed unit_rinv2 l_coset_assoc)

lemma r_coset_rel2:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; r_coset A x = r_coset A y\<rbrakk> \<Longrightarrow>r_coset A (x \<cdot> (inv y)) = A "
  using inv_prod_r_coset2 by auto

lemma l_coset_rel2:"\<lbrakk>x \<in> X;y\<in>X; A\<subseteq>X; l_coset x A = l_coset y A\<rbrakk> \<Longrightarrow> l_coset (inv y \<cdot> x) A = A"
  using inv_prod_l_coset2 by auto  

lemma r_coset_absorb1:"\<lbrakk>x\<in>X; subgroup H X f e; r_coset H x = H\<rbrakk> \<Longrightarrow> x \<in> H "
  using r_coset_absorb by blast 

lemma l_coset_absorb1:"\<lbrakk>x\<in>X; subgroup H X f e; l_coset x H = H\<rbrakk> \<Longrightarrow> x \<in> H "
  using l_coset_absorb by blast 

lemma subgroup_solve_eq:
  assumes A0:"subgroup H X (\<cdot>) e" and A1:"x \<in> H" and A2:"y \<in> H"
  shows "\<exists>h \<in> H. y = h \<cdot> x" and "\<exists>h \<in> H. y = x \<cdot> h"       
proof-
  show "\<exists>h \<in> H. y = h \<cdot> x"
  proof-
    obtain "y = (y \<cdot> (inv x)) \<cdot> x" and "y \<cdot> inv x \<in> H"
      by (meson A0 A1 A2 group.inv_rsolve1 group_axioms subgroup.closed subgroup.inv_cl subgroup.sub_mem)
    then show ?thesis
      by blast
  qed
  show "\<exists>h \<in> H. y = x \<cdot> h"    
  proof-
    obtain "inv x \<cdot> y \<in> H"
      by (meson A0 A1 A2 subgroup.closed subgroup.inv_cl)
    then show ?thesis
      by (meson A0 A1 A2 inv_lsolve1 subgroup.sub_mem)
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
    using A0 g0 subgroup.sub_mem by fastforce
  also have " ... =  (inv h \<cdot>  (inv g \<cdot> g) \<cdot> k)"
    by (meson A0 assoc4 g0 h0 invertible k0 subgroup.sub_mem unit_inv_closed)
  finally have "inv x \<cdot> y = inv h \<cdot> k"
    using A0 g0 h0 subgroup.sub_mem by fastforce
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
    by (metis A0 g0 invertible subgroup.sub_mem units_prod)
  also have " ... =  (h \<cdot>  (g \<cdot> inv g) \<cdot> inv k)"
    by (meson A0 assoc4 g0 h0 invertible k0 subgroup.sub_mem unit_inv_closed)
  finally have "x \<cdot> inv y = h \<cdot> inv k"
    by (metis A0 g0 h0 r_inv_simp rid subgroup.sub_mem)
  then show "x \<cdot> inv y \<in> H"
    by (metis A0 h0 k0 subgroup.closed subgroup.inv_cl) 
qed

lemma l_coset_absorb2:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> l_coset x H"
  by (metis l_coset_memI rid subgroup.id_mem) 

lemma r_coset_absorb2:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> r_coset H x"
  by (metis lid r_coset_memI subgroup.id_mem) 

lemma l_coset_absorb3:"subgroup H X (\<cdot>) e \<Longrightarrow> x \<in> H \<Longrightarrow>  l_coset x H =H"
proof-
  assume A0:"subgroup H X (\<cdot>) e" and A1: "x \<in> H"
  have B0:"l_coset x H \<subseteq> H"
    by (metis A0 A1 magma.l_coset_sub magma_def subgroup.closed subset_refl)
  also have B1:"H \<subseteq> l_coset x H"
  proof
    fix h assume A2:"h \<in> H" then obtain "inv x \<cdot> h \<in> H" and "h = x \<cdot> ( inv x \<cdot> h)"
      by (meson A0 A1 inv_lsolve1 subgroup.closed subgroup.inv_cl subgroup.sub_mem)
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
      by (meson A0 A1 group.inv_rsolve1 group_axioms subgroup.closed subgroup.inv_cl subgroup.sub_mem)
    then show "h \<in> r_coset H x"
      by (metis r_coset_memI)
  qed
  finally show "r_coset H x =H"
    by blast
qed
    
    

end

context subgroup
begin
lemma r_cosets_elem_ne: 
  assumes "t \<in> r_cosets H" 
  shows "t \<noteq> {}"
proof -
  obtain g where "g \<in> G" "t =r_coset H g"  
    using assms unfolding r_cosets_def by blast
  hence "e \<cdot> g \<in> t"
    by blast
  thus ?thesis by blast
qed

lemma l_cosets_elem_ne: 
  assumes "t \<in> l_cosets H" 
  shows "t \<noteq> {}"
proof -
  obtain g where "g \<in> G" "t =l_coset g H" 
    using assms unfolding l_cosets_def by blast
  hence "g \<cdot> e\<in> t" 
    by blast
  thus ?thesis
    by blast
qed

lemma set_prod_sub:"H \<subseteq> set_prod H H"
proof
  fix h assume h:"h \<in> H"
  then obtain "h = e \<cdot> h" and "e \<in> H"
    using id_mem by auto
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
      using a subset by auto
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
      using a subset by auto
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
  apply (meson assms subgroup.subset)
  using assms subgroup.id_mem apply fastforce
  apply (simp add: assms subgroup.inv_cl)
  by (meson assms subgroup.closed)


lemma trivial_subgroup:"subgroup {e} X f e"  using subgroupI1 by fastforce
lemma subgroup_inv_eq[simp]:
  assumes A0:"subgroup H X f e" and "x \<in> H"
  shows "monoid.inv H f e x= inv x"
  by (metis A0 assms(2) subgroup.subgroup_inv_eq)
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
lemma subgroup_r_eqsol:"\<lbrakk>x\<in>H; y \<in> H; subgroup H X f e\<rbrakk> \<Longrightarrow> \<exists>h \<in> H. y = h \<cdot> x"
  by (simp add: subgroup_solve_eq(1)) 

lemma subgroup_l_eqsol:"\<lbrakk>x\<in>H; y \<in> H; subgroup H X f e\<rbrakk> \<Longrightarrow> \<exists>h \<in> H. y = x \<cdot> h"
  using subgroup_solve_eq(2) by auto  

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
  using A0 A1 A3 l_coset_absorb2 by auto

lemma l_coset_eq2:
  assumes A0:"subgroup H X f e" and A1:"a \<in> X" and A2:"b \<in> X" and A3:"a \<in> l_coset b H"
  shows "l_coset a H = l_coset b H" 
proof-
  obtain ha where A4:"ha \<in> H" and A5:"a = b \<cdot> ha" using A3 by blast
  then obtain A6:"inv ha \<in> H" and A7:"b = a \<cdot> inv ha"
    by (metis A0 A1 A2 inv_rsolve1 subgroup.sub_mem subgroupE1(3))
  have "l_coset a H \<subseteq> l_coset b H" 
    by (metis A0 A2 A4 A5 l_coset_absorb4 l_coset_assoc subgroup.sub_mem subsetI)
  also have "l_coset b H \<subseteq> l_coset a H"  
     by (metis A0 A2 A4 A5 l_coset_absorb4 l_coset_assoc subgroup.sub_mem subsetI)
   finally show 
     ?thesis by simp
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
      by (meson A0 A1 group.subgroupE1(3) group_axioms invertible subgroup.sub_mem units_prod)
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
      by (metis A0 A1 h0 h1 invertible subgroup.sub_mem unit_inv_closed units_prod)
    also have "... = a \<cdot> inv h"
      using A1 double_inv by presburger
    finally obtain x3:"a \<cdot> inv h \<in>  l_coset a H" and x4:"inv x = a \<cdot> inv h"
      using h2 by blast
    then obtain x5:"inv (a \<cdot> inv h) = x"
      by (metis A0 A1 double_inv h0 h1 idin inv2_prod inv_ident m_closed rid subgroup.sub_mem)
    then show "x \<in> set_inv (l_coset a H)"
      unfolding set_inv_def  using x3 by blast
  qed
  have B2:"\<And>x. x \<in> set_inv (r_coset H a) \<Longrightarrow> x \<in> l_coset (inv a) H"
  proof-
    fix x assume x0:"x \<in>  set_inv (r_coset H a)"
    then obtain h where h0:"h \<in> H" and h1:"x = inv (h \<cdot> a)"
      unfolding set_inv_def by(auto)
    then obtain "x = inv a \<cdot> inv h" and "inv h \<in> H"
      by (meson A0 A1 group.invertible group.subgroupE1(3) group_axioms subgroup.sub_mem units_prod)
    then show "x \<in> l_coset (inv a) H"
      by blast
  qed
  have B3:"\<And>x.  x \<in> l_coset (inv a) H \<Longrightarrow> x \<in> set_inv (r_coset H a)"
  proof-
    fix x assume x0:"x \<in> l_coset (inv a) H"
    then obtain h where h0:"h \<in> H" and h1:"x = (inv a) \<cdot> h" and h2:"inv h \<in> H"
      by (auto simp add: A0 subgroupE1(3))
    then obtain h3:"h \<in> X" and h4:"inv a \<in> X" and h5:"x \<in> X"
       by (metis A0 A1 h0 h1 idin inv2_prod inv_ident m_closed rid subgroup.sub_mem)
    obtain h6:"inv x = inv h \<cdot> a" and h7:"inv h \<cdot> a \<in> r_coset H a"
      using A1 h1 h2 h3 by auto
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
    then obtain "(x\<cdot>h\<cdot>inv x) \<cdot> x = x \<cdot> h"
      by (metis A0 A1 A4 group.inv_rsolve1 group_axioms magma.closed magma_axioms subgroup.sub_mem) 
    then show "y \<in> r_coset H x"   by (metis A5 B0 r_coset_memI)
  qed
  also have B1:"r_coset H x \<subseteq> l_coset x H"
    by (metis A0 A1 A2 calculation idin inv2_prod inv_ident l_inv_simp lr_coset_assoc r_coset_assoc r_coset_sub rid subgroupE1(1))
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
      using B0 l_coset_eq1 subgroup_axioms by blast
  qed
  also have B2:" inv x \<cdot> y \<in> H \<Longrightarrow> l_coset x H = l_coset y H"
    using l_coset_absorb4 l_coset_rel1 subgroup_axioms subset x0 y0 by presburger
  then show "l_coset x H = l_coset y H \<longleftrightarrow> inv x \<cdot>y \<in> H"
    using calculation by blast
  have B3:"inv x \<cdot> y \<in> H \<Longrightarrow> inv y \<cdot>x \<in> H "
  proof-
    assume "inv x \<cdot> y \<in> H" then obtain "inv (inv x \<cdot> y) \<in> H" and "inv (inv x \<cdot> y) = inv y \<cdot> x"
      by (metis double_inv invertible subgroup.inv_cl subgroup_axioms unit_inv_closed units_prod x0 y0)
    then show "inv y \<cdot> x \<in> H" 
      by auto
  qed
  then show "inv x \<cdot>y \<in> H \<longleftrightarrow> inv y \<cdot>x \<in> H"
    by (metis calculation inv_prod_l_coset1 l_coset_absorb_iff sub_mem subgroup_axioms subset x0 y0)
qed


end

subsection \<open>Quotient Group Locale\<close>
locale quotient_group=
  group X "(\<cdot>)" e +
  equivalence_relation X R
  for X::"'a set" and 
      f::"'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 70) and 
      R::"'a rel" and
      e::"'a"+
  assumes compat:"(x1, x2) \<in> R \<Longrightarrow> (y1, y2) \<in> R \<Longrightarrow> (x1\<cdot>y1 , x2\<cdot>y2) \<in> R"
begin

sublocale quotient_magma X "(\<cdot>)" R
  by (simp add: compat equivalence_relation_axioms magma_axioms quotient_magma.intro quotient_magma_axioms_def)

sublocale quotient_semigroup X "(\<cdot>)" R
  by (simp add: compatible equivalence_relation_axioms quotient_semigroup.intro quotient_semigroup_axioms_def semigroup_axioms)

sublocale quotient_monoid X "(\<cdot>)" R e
  by (simp add: compatible equivalence_relation_axioms monoid_axioms quotient_monoid.intro quotient_monoid_axioms_def)

definition "qinv t \<equiv>  (p (inv (pinv t)))"
lemma id_pair:"(e, e) \<in> R" by auto

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
    using H_def idin by blast
  then obtain "(x \<cdot> e, x \<cdot> (inv x \<cdot> y)) \<in> R"
    using compatible by blast
  then show "(x, y) \<in> R"
    by (simp add: monoid.inv_rcancel monoid_axioms x0 y0)
qed


lemma equivalent_iff:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> (inv x) \<cdot> y \<in> H" 
  by (meson equivalentE1 equivalentI1)
lemma h_memI1:"(e,x) \<in> R \<Longrightarrow> x \<in> H" 
  by (simp add: H_def)
lemma h_memI2:"(x,e) \<in> R \<Longrightarrow> x \<in> H" 
  using h_memI1 local.sym by blast
lemma h_ne_sub:"H \<noteq> {} \<and> H \<subseteq> X"  using H_def by auto 
lemma h_id_mem:"e \<in> H"  using H_def by blast
lemma h_inv_closed:"\<And>x. x \<in> H \<Longrightarrow> inv x \<in> H"
  by (metis H_def double_inv equivalentI1 h_memI2 idin inv2_prod inv_ident p_closed1 rid)

lemma h_iprod_closed:"\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> inv x \<cdot> y \<in> H"
  by (metis H_def equivalentE1 idin p_D1 p_equivalence r_closed)  

lemma h_subgroup:"subgroup H X (\<cdot>) e"  
  using h_iprod_closed h_ne_sub local.subgroupI3 by presburger

lemma quotient_rinv:"x \<in> X \<Longrightarrow> (p x)\<bullet>(p (inv x)) = p e" 
  by (simp add: qlaw3)
lemma quotient_linv:"x \<in> X \<Longrightarrow> (p (inv x))\<bullet>(p x) = p e" 
  by (simp add: qlaw3) 
lemma qinv_closed:"t \<in> X/R \<Longrightarrow> qinv t \<in> X/R"
  using invertible unit_inv_closed p_in_quotient1 qinv_def sec_closed by presburger
lemma quotient_rinv2:"t \<in> X/R \<Longrightarrow> t \<bullet> qinv t = H"  
  by (metis H_def psecE1 qinv_def quotient_rinv sec_closed) 
lemma quotient_linv2:"t \<in> X/R \<Longrightarrow> qinv t \<bullet> t = H "
  by (metis H_def qinv_def psecE1 quotient_linv sec_closed)

lemma quotient_clinv:"t \<in> X/R \<Longrightarrow> quotient.invertible t" 
  using quotient.invertibleI[of "t" "qinv t"] quotient_rinv2[of t] quotient_linv2[of t] qinv_closed by presburger

lemma quotient_elem_inv:"x \<in> X \<Longrightarrow>  quotient.invertible (p x) " 
  using proj.cod quotient_clinv by presburger

lemma quotient_inv_comp:"x \<in> X \<Longrightarrow>  quotient.inv (p x) = p (inv x)"  
  using H_def quotient.inv_eq quotient_linv quotient_rinv by force 

lemma quotient_inv_unique:"t \<in> X/R \<Longrightarrow> qinv t = quotient.inv t" 
  by (metis qinv_closed quotient.inv_eq quotient_linv2 quotient_rinv2)

lemma quotient_is_group:"group (X/R) (\<bullet>) H" 
  apply(rule group.intro)
   apply (simp add:quotient.monoid_axioms)
  by (simp add: group_axioms_def quotient_clinv)

end




context group
begin
lemma subgroup_r_coset_rel:
 assumes A0:"subgroup H X f e" and A1:"t \<in> r_cosets H"
 shows "\<And>x1 x2. \<lbrakk>x1 \<in> t; x2 \<in> t\<rbrakk> \<Longrightarrow> x1 \<cdot> (inv x2) \<in> H"
  using A0 A1 subgroup_r_cosets by blast


lemma subgroup_l_coset_rel:
 assumes A0:"subgroup H X f e" and A1:"t \<in> l_cosets H"
 shows "\<And>x1 x2. \<lbrakk>x1 \<in> t; x2 \<in> t\<rbrakk> \<Longrightarrow> inv x2 \<cdot> x1 \<in> H"
  using A0 A1 subgroup_l_cosets by blast

end




context monoid
begin

primrec pow_nat (infixr "**" 80) where 
 pow_0:"x ** 0=e " | pow_Suc:"x ** Suc n=x \<cdot> (x ** n)"


(*
lemma sanity_check:
  assumes A0:"a \<in> X"
  defines "x \<equiv> (\<lambda>i::nat. a)"
  shows "list_finprod [1,2] x = a**2"
proof-
  have "list_finprod [1::nat,2::nat] x = act_finprod ([1::nat]) x (x (2::nat))"
    unfolding list_finprod_def by simp
  also have "... = f (x 1) (x 2)"
    unfolding act_finprod_def  by simp
  also have "... = f a a "
    by (simp add: x_def)
  also have "... = a**2"
    by (simp add: A0 numeral_2_eq_2)
  finally show ?thesis
    by auto
qed
*)
lemma power_one[simp]:"e ** n=e" 
proof(induct n)   
  case 0 then show ?case 
    by simp  
next   
  case (Suc n)
  then show ?case by simp
qed

lemma power_on_right[simp]:"x\<in>X \<Longrightarrow> x ** 1=x" by simp
lemma power_Suc0_right[simp]:"x\<in>X \<Longrightarrow> x ** Suc 0=x" using power_on_right by auto 
lemma pow_closed[simp]:"x\<in>X \<Longrightarrow> x ** n\<in>X"
proof(induct n)   
  case 0 then show ?case  by simp
next 
  case (Suc n)
  then obtain "x**Suc n=x \<cdot> x**n" and "x**n\<in>X"
    by simp
  then show ?case
    using Suc.prems closed by auto 
qed

lemma power_commutes:"x\<in>X \<Longrightarrow> (x**n) \<cdot> x=x \<cdot> (x**n)"
proof(induct n)
  case 0 then show ?case by simp
next
  case (Suc n) then show ?case
    by (simp add: commutes_assoc)
qed

lemma power_Suc2:"x\<in>X \<Longrightarrow> x**Suc n=x**n \<cdot> x" by (simp add: power_commutes)
lemma power_add: "x\<in>X \<Longrightarrow> x**(m + n)=x**m \<cdot> x**n"
proof(induct m) 
  case 0 then show ?case by simp
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
    by (simp add: A0)  
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
      by (simp add: ymem)
  next   
    case (Suc n) 
    then obtain "x**n \<cdot> y=y \<cdot> x **n"  
      by simp 
    let ?n1="Suc n"  
    have "x**?n1 \<cdot> y=x**n \<cdot> (x \<cdot> y)"
      using asc local.power_Suc2 pow_closed xmem ymem by presburger 
    also have "...=x**n \<cdot> (y \<cdot> x)" 
      by (simp add: comm) 
    also have "...=(x**n \<cdot> y) \<cdot> x"
      by (simp add: asc xmem ymem) 
    also have "...=(y \<cdot> x **n) \<cdot> x"  
      by (simp add: Suc)
    also have "...=y \<cdot> x**?n1"
      using asc local.power_Suc2 pow_closed xmem ymem by presburger  
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
      by (metis commute_pow1 idin pow_0 xmem) 
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
    case 0 then show ?case   by simp
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
lemma commute_invertible:"\<lbrakk>x\<in>X; y\<in>X; invertible x; invertible y; x \<cdot> y=y \<cdot> x\<rbrakk> \<Longrightarrow> inv x \<cdot> inv y=inv y \<cdot> inv x"
  by (metis units_prod) 

lemma fin_prod_ord:
  assumes amem:"a\<in>X" and bmem:"b\<in>X" and commute:"a \<cdot> b=b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0" 
  shows "elem_ord (a \<cdot> b) \<noteq> 0"
proof- 
  let ?m="lcm (elem_ord a) (elem_ord b)" 
  have "(a \<cdot> b)**?m=a**?m \<cdot> b**?m"
    using amem bmem commute commute_pow3 by blast 
  also have "...=e"  
    by (metis amem bmem dvdE dvd_lcm1 dvd_lcm2 elem_ord_exp local.power_mult local.power_one pow_closed rid)
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
    using amem bmem commute commute_pow3 elem_ord_exp pow_closed rid by presburger 
  then have B2:"elem_ord ((a \<cdot> b)**?\<beta>)=elem_ord (a ** ?\<beta>)"
    by simp
  also have B3:"...=?\<alpha> div (gcd ?\<alpha> ?\<beta>)"
    using aford amem bford ord_pow1 by auto
  also have B4:"elem_ord ((a \<cdot> b)**?\<beta>) dvd (elem_ord (a \<cdot> b))" 
    by (metis B0 One_nat_def amem bford bmem m_closed dvd_div_mult_self dvd_mult2 dvd_refl gcd_Suc_0 gcd_dvd1 gcd_le1_nat ord_pow1)  
  then have B5:"?\<alpha> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))"  
    by (simp add: calculation) 
  have B6:"(a \<cdot> b)**?\<alpha>=b ** ?\<alpha>"
    using amem bmem commute monoid.commute_pow3 monoid.elem_ord_exp monoid.lid monoid_axioms by fastforce 
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
notation pow_nat (infixl "**" 75) 


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

lemma nat_pow_inv:
  assumes "x \<in>X" shows "(inv x) ** (i :: nat) = inv (x ** i)"
proof (induction i)
  case 0 thus ?case by simp
next
  case (Suc i)
  have "(inv x) ** Suc i = ((inv x) ** i) \<cdot> inv x" using assms local.power_Suc2 by blast
  also have " ... = (inv (x ** i)) \<cdot> inv x"   by (simp add: Suc.IH Suc.prems)
  also have " ... = inv (x \<cdot> (x ** i))"  by (simp add: assms) 
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
  apply(auto simp add:assms int_pow_def2 inv_lsolve1 inv_rsolve1 nat_add_distrib[symmetric] power_add)
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

lemma inv_mult_group: "\<lbrakk> x \<in> X; y \<in>X\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv y \<cdot> inv x" by simp

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
    by (simp add: x_car) 
  also have "\<dots> = x ** (m - n) \<cdot> x ** n" 
    using False by (simp add: nat_pow_mult x_car)
  also have "\<dots> = x ** (m - n) \<cdot> x ** m"  
    by (simp add: pow_eq)
  finally show ?thesis
    by (metis idin pow_closed r_cancel1 x_car) 
qed simp         



end



context subgroup
begin

lemma assoc_cancel:"a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> (b \<cdot> inv a) \<cdot> (a \<cdot> h) = b \<cdot> h"  using remove_id1 by blast 

lemma lcoset_absorb:"g \<in> G \<Longrightarrow> g \<in> l_coset g H" by (simp add: l_coset_absorb2 subgroup_axioms) 
lemma rcoset_absorb:"g \<in> G \<Longrightarrow> g \<in> r_coset H g" by (simp add: r_coset_absorb2 subgroup_axioms) 
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

lemma lcoset_mem:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> (f (inv x) y \<in> H)  \<longleftrightarrow> (y \<in> (l_coset x H))"
  by (metis group.l_coset_eq2 group_axioms l_coset_eq1 l_coset_equivs(1) subgroup_axioms)

lemma rcoset_mem:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> (f y (inv x) \<in> H)  \<longleftrightarrow> (y \<in> (r_coset H x))"
  by (metis coset_absorb_iff(2) inv_prod_r_coset1 inv_rsolve2 r_coset_memE rcoset_absorb sub_mem subset)

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
  obtain B0:"?c\<in>G"
    using A0 A1 inv2_prod by blast 
  show P0:"inj_on (\<lambda>x. inv (a \<cdot> inv b) \<cdot> x)  (l_coset a H)"
  proof(rule inj_onI)
    fix x y assume A2:"x \<in> l_coset a H" and A3:" y \<in>l_coset a H" and  A4:"?c \<cdot> x = ?c \<cdot> y"
    then show "x = y"
      by (meson A0 B0 l_cancel2 subgroup.l_coset_sub_mem subgroup_axioms) 
  qed
  show P1:"inj_on (\<lambda>x. inv (a \<cdot> inv b) \<cdot> x)  (l_coset b H)"
  proof(rule inj_onI)
    fix x y assume A2:"x \<in> l_coset b H" and A3:" y \<in>l_coset b H" and  A4:"?c \<cdot> x = ?c \<cdot> y"
    then show "x = y"
      by (meson A1 B0 l_cancel1 l_coset_sub_mem) 
  qed
  have B1:"inv (a \<cdot> inv b) = (b \<cdot> inv a)"
    by (simp add: A0 A1) 
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
    then show "x = y"
      by (meson A0 B0 r_cancel1 r_coset_sub_mem)  
  qed
  show "inj_on (\<lambda>x. x \<cdot> (inv b \<cdot> a)) (r_coset H b)"
  proof (rule inj_onI)
    fix x y assume "x \<in> r_coset H b" and "y \<in> r_coset H b" and "x \<cdot> ?c = y \<cdot> ?c"
    then show "x = y"
      by (meson A1 B0 r_cancel1 r_coset_sub_mem) 
  qed
  have B3:"inv (a \<cdot> inv b) = (b \<cdot> inv a)"
    using A0 A1 by auto
  have B4:"(b \<cdot> inv a) \<in> G"   
    by (simp add: A0 A1 magma.closed magma_axioms)
  show "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv a)) (r_coset H a)"
    by (meson A0 B4 inj_onI r_cancel1 r_coset_sub_mem) 
  show "inj_on (\<lambda>x. x \<cdot> (b \<cdot> inv a)) (r_coset H b)"
    by (meson A1 B4 inj_onI r_cancel1 r_coset_sub_mem)
  show "inj_on (\<lambda>x. x \<cdot> (inv a \<cdot> b)) (r_coset H a)"
    by (metis A0 A1 inj_on_multc inv_eq l_inv_ex m_closed r_coset_sub subset_inj_on)
qed
 
lemma coset_bij1: 
  assumes A0:"a \<in> G"
  shows "bij_betw (\<lambda>x. inv x) (l_coset a H) (r_coset H (inv a))"
proof(auto simp add:bij_betw_def)
  show "inj_on inv (l_coset a H)" 
    by (metis A0 inj_onI invertible invertible_inverse_inverse l_coset_sub_mem)
  show "\<And>x. x \<in> (l_coset a H) \<Longrightarrow> inv x \<in> (r_coset H (inv a))"
    by (metis assms l_coset_set_inv(1) l_coset_sub set_inv_memI2 subgroup_axioms)
  show "\<And>x. x \<in> r_coset H( inv a) \<Longrightarrow> x \<in> inv ` (l_coset a H)" 
    by (metis assms imageI inv_cl invertible unit_inv_closed invertible_inverse_inverse prod_inv lcoset_mem r_coset_sub_mem rcoset_mem)
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
      then have "b \<cdot> h = b \<cdot> (inv a \<cdot> a) \<cdot> h"  by (simp add: A0 A1)
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

lemma l_coset_id: "l_coset e H = H" by (simp add: coset_absorb_iff(1))
lemma r_coset_id: "r_coset H e = H" by (simp add: coset_absorb_iff(2))

theorem l_coset_card3:  "x \<in> G \<Longrightarrow> card (l_coset x H) = card H" using idin l_coset_card1 l_coset_id by presburger
theorem r_coset_card3:  "x \<in> G \<Longrightarrow> card (r_coset H x) = card H" using idin r_coset_card1 r_coset_id by presburger


definition l_sub_eq where "l_sub_eq \<equiv> {(x, y) \<in> G \<times> G. (inv x)\<cdot>y \<in> H}" 
definition r_sub_eq where "r_sub_eq \<equiv> {(x, y) \<in> G \<times> G. y\<cdot>(inv x) \<in> H}" 

lemma id_in_l_sub_eq:"(e,e) \<in> l_sub_eq" by (simp add: l_sub_eq_def)
lemma id_in_r_sub_eq:"(e,e) \<in> r_sub_eq" by (simp add: r_sub_eq_def)
lemma l_sub_eq_mem:"x \<in> G \<Longrightarrow> (x,x)\<in> l_sub_eq" using coset_eq_iff(2) l_sub_eq_def by blast
lemma r_sub_eq_mem:"x \<in> G \<Longrightarrow> (x,x)\<in> r_sub_eq" using coset_eq_iff(4) r_sub_eq_def by blast
lemma l_sub_eq_refl:"refl_on G l_sub_eq" apply(simp add:refl_on_def l_sub_eq_def)  using id_mem by blast
lemma r_sub_eq_refl:"refl_on G r_sub_eq" apply(simp add:refl_on_def r_sub_eq_def)  using id_mem by blast
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


subsection \<open>Normal Subgroups\<close>

locale normal_subgroup=subgroup H G "(\<cdot>)" e for H and G and f (infixl "\<cdot>" 70) and e+
      assumes normal:"g \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> g \<cdot> h \<cdot> inv g \<in>  H"
begin
lemma conj_closed:"g \<in> G \<Longrightarrow> h \<in> H \<Longrightarrow> inv g \<cdot> h \<cdot> g \<in> H" 
  by (metis invertible invertible_inverse_inverse monoid.unit_inv_closed monoid_axioms normal)
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
      have "(x \<cdot> (inv g)) \<cdot> g = x"
        by (metis A0 A1 B2 inv_rsolve2 l_coset_sub sub_mem subset_iff)
    then show "x\<in> r_coset H g"
      by (metis B2 r_coset_memI)
    qed
    show "r_coset H g \<subseteq> l_coset g H"
    proof
      fix x assume A1:"x \<in> r_coset H g"
      then obtain h where A2:"h \<in> H" and A3:"x = h \<cdot> g" by blast
      then have B0:"(inv g) \<cdot> x =  (inv g) \<cdot> h \<cdot> g"  by (simp add: A0 asc) 
      also have B1:"... \<in> H"   by (simp add: A0 A2 conj_closed)
      then obtain B2:"(inv g) \<cdot> x \<in> H"  using calculation by presburger
      have "(g \<cdot> (inv g)) \<cdot> x = x"  
        using A0 A1 invertible unit_rinv lid r_coset_sub_mem by presburger
      then show "x\<in> l_coset g H"  
        using A0 A1 B2 lcoset_mem r_coset_sub_mem by blast  
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
  then show "g \<cdot> h \<cdot> inv g \<in> H"
    by (metis \<open>(g::'a) \<in> (G::'a set)\<close> \<open>(h::'a) \<in> (H::'a set)\<close> assms magma.l_coset_memI magma_axioms r_coset_sub_mem subgroup.rcoset_mem subgroup_axioms) 
qed

end

context group
begin


lemma l_coset_cancel:"A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> x \<in> l_coset b A \<Longrightarrow> inv b \<cdot> x \<in> A"  
  using monoid.unit_linv2 monoid_axioms by fastforce

lemma r_coset_cancel:"A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> x \<in> r_coset A b \<Longrightarrow> x \<cdot> inv b \<in> A" 
  by (metis IntD2 closed inf.orderE inv_rsolve2 r_coset_memE)  

lemma l_coset_eq_r_cosetE:"A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> l_coset b A = r_coset A b \<Longrightarrow>  a \<in> A \<Longrightarrow> b \<cdot> a \<cdot> (inv b) \<in> A" 
  using r_coset_cancel by blast

lemma l_coset_sub_r_cosetI:
  assumes A0:"A \<subseteq> X" and A1:"b \<in> X" and A2:"(\<And>a.  a \<in> A \<Longrightarrow> b \<cdot> a \<cdot> (inv b) \<in> A)"
  shows "l_coset b A \<subseteq> r_coset A b"
proof
    fix x assume "x \<in> l_coset b A" then obtain a where "a \<in> A" and "x = b \<cdot> a" by blast
    then obtain "b \<cdot> a \<cdot> (inv b) \<in> A" and "x = b \<cdot> a \<cdot> (inv b) \<cdot> b" 
      using A0 A1 A2 asc closed rid by auto
    then show "x \<in> r_coset A b"
      by blast
qed

lemma r_coset_sub_l_cosetI:
  assumes A0:"A \<subseteq> X" and A1:"b \<in> X" and A2:"(\<And>a.  a \<in> A \<Longrightarrow> (inv b) \<cdot> a \<cdot> b \<in> A)"
  shows "r_coset A b \<subseteq> l_coset b A"
proof
    fix x assume "x \<in> r_coset A b" then obtain a where "a \<in> A" and "x = a \<cdot> b" by blast
    then obtain "(inv b) \<cdot> a \<cdot> b \<in> A" and "x = b \<cdot> ((inv b) \<cdot> a \<cdot> b)" 
      using A0 A1 A2 asc closed inv_rcancel by auto 
    then show "x \<in> l_coset b A" 
      by blast 
qed

definition normalizer where "normalizer A \<equiv> {b \<in> X. l_coset b A = r_coset A b}" 

 
end 


subsection \<open>Group Homomorphism\<close>
locale group_homomorphism=set_morphism f X Y+ dom:group X "(\<cdot>)" e + cod:group Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) and e and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)" 
begin


lemma map_id:"f e = d"
  by (metis cmp cod cod.idin cod.l_cancel1 cod.rid dom.idin dom.rid) 

sublocale monoid_homomorphism f X "(\<cdot>)" e Y "(\<star>)" d
  by (simp add: cmp cod.monoid_axioms dom.monoid_axioms map_id 
      monoid_homomorphism_axioms_def monoid_homomorphism_def set_morphism_axioms) 


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
  also have "... = (f (dom.inv x))\<star>(f x)"
    using assms calculation dom.invertible inverse_image_id2 by presburger 
  finally show "d =  (f (dom.inv x))\<star>(f x)" by blast
qed

lemma map_inv:"x \<in> X \<Longrightarrow> cod.inv (f x) = f (dom.inv x)"  using cod.inv_eq map_inv_id by auto
lemma map_ord1:assumes "x \<in> X" shows " f (dom.pow_nat x n) = cod.pow_nat (f x) n"
proof(induct n)
  case 0 then show ?case  by (simp add: map_id) next
  case (Suc n) then show ?case    by (simp add: assms cmp) 
qed

lemma map_ord2:"x \<in> X \<Longrightarrow> dom.elem_ord x \<noteq> 0 \<Longrightarrow> cod.elem_ord (f x) dvd dom.elem_ord x"
proof-
  assume A0:"x \<in> X" and A1:"dom.elem_ord x \<noteq> 0"
  have "dom.pow_nat x (dom.elem_ord x) = e"  
    by (simp add: dom.elem_ord_exp)
  then have "cod.pow_nat (f x) (dom.elem_ord x) = cod.pow_nat (f e) (dom.elem_ord x)" 
    by (metis A0 cod.power_one map_id map_ord1)
  also have "... = d" 
    by (simp add: map_id)
  finally show "cod.elem_ord (f x) dvd dom.elem_ord x" 
    by (metis (mono_tags, lifting) A0 A1 Collect_empty_eq cod cod.elem_exponents_def cod.elem_ord_def cod.order_divides_exponent gr0I less_irrefl mem_Collect_eq wellorder_Least_lemma(1))
qed

lemma tempker:"x \<in> X \<Longrightarrow> f x = d \<Longrightarrow> y \<in> X \<Longrightarrow> f y = d \<Longrightarrow> f (x \<cdot> y) = d" 
  by (simp add: cmp)

definition Ker where "Ker \<equiv> {x \<in> X. f x = d}"

lemma Ker_equality: "Ker = {x \<in> X. f x = d}" unfolding Ker_def by auto
lemma Ker_closed[intro, simp]:"a \<in> Ker \<Longrightarrow> a \<in>X"  unfolding Ker_def by simp
lemma Ker_image[intro]:"a \<in> Ker \<Longrightarrow> f a = d" unfolding Ker_def by simp
lemma Ker_memI1:"\<lbrakk>f a = d; a\<in>X\<rbrakk> \<Longrightarrow> a \<in> Ker" unfolding Ker_def by simp

lemma Ker_opc:"a \<in> Ker \<Longrightarrow> b \<in> Ker \<Longrightarrow> (a \<cdot> b) \<in> Ker" 
  by (meson Ker_closed Ker_image Ker_memI1 dom.closed tempker)

lemma ker_inc:"a \<in> Ker \<Longrightarrow> dom.inv a \<in> Ker" 
  by (metis Ker_closed Ker_image Ker_memI1 cod.inv_ident dom.invertible dom.unit_inv_closed map_inv)

lemma Ker_memI2:assumes A0:"x \<in> X" and A1:"k \<in> Ker" shows "(dom.inv x) \<cdot> k \<cdot> x \<in> Ker"
  by (metis (full_types) A0 A1 Ker_closed Ker_image Ker_memI1 cmp dom.idin dom.invertible dom.m_closed dom.rid dom.unit_inv_closed map_id map_inv_id(2))

lemma Ker_sub:"subgroup Ker X (\<cdot>) e"
  apply(unfold_locales)
  apply (simp add: subsetI)
  apply (simp add: Ker_opc)
  apply (simp add: Ker_memI1 map_id)
  by (simp add: ker_inc)

lemma injD:"set_monomorphism f X Y \<Longrightarrow> Ker = {e} " 
  apply(auto simp add:set_monomorphism_def inj_locale_def) 
  apply (simp add: Ker_image inj_onD map_id)
  by (simp add: Ker_memI1 map_id)

lemma injI:" Ker = {e}  \<Longrightarrow> set_monomorphism f X Y " 
  apply(auto simp add:set_monomorphism_def inj_locale_def)
  apply (simp add: set_morphism_axioms) 
  apply(auto simp add:inj_on_def)
  by (metis Ker_memI1 cmp dom.closed dom.invertible dom.invertible_def dom.r_cancel1 map_id singletonD)

lemma conj_closed:"\<And>g k. \<lbrakk>g\<in>X;k\<in>Ker\<rbrakk>\<Longrightarrow>g \<cdot> k \<cdot> dom.inv g\<in>Ker" 
  by (metis Ker_memI2 dom.double_inv dom.invertible dom.unit_inv_closed)

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
subsection \<open>Group Isomorphism\<close>
locale group_isomorphism=set_isomorphism f X Y+ dom:group X "(\<cdot>)" e + cod:group Y "(\<star>)" d
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) and e and d+
  assumes cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> f (x \<cdot> y) = (f x) \<star> (f y)"
begin
sublocale group_homomorphism by(unfold_locales,simp add: cmp)
sublocale group_epimorphism by(unfold_locales,simp add: cmp)
sublocale group_monomorphism by(unfold_locales,simp add: cmp)
lemma ker_id:"Ker = {e}" using ker_id by force  
lemma card_eq:"card X = card Y" using bij_betw_same_card by blast
lemma in_set_iso:"f \<in> set_isomorphisms X Y"
  by (simp add: set_iso_mem)
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
  apply (simp)
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
  by (simp add: group_generate group_generated.opc)

lemma cl_monoid: "monoid (cl_group H) (\<cdot>) e"
  unfolding cl_group_def monoid_def semigroup_def magma_def semigroup_axioms_def monoid_axioms_def
  apply(auto)
  using group_generated.opc apply blast
  apply (simp add: asc group_generate)
  apply (simp add: group_generated.idm)
  apply (simp add: group_generate)
  by (simp add: group_generate)

  
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

lemma generate_is_subgroup:
  assumes "H \<subseteq> X" shows "subgroup (cl_group H) X f e" 
  using cl_subgroup by simp

lemma subgroup_imp_group:
  "subgroup H X (\<cdot>) e \<Longrightarrow>  group H (\<cdot>) e"
  by (simp add: subgroup.subgroup_is_group1)

lemma subgroup_pow_equality[simp]:
  assumes A0:"subgroup H X f e" and "x \<in> H"
  shows "monoid.pow_int H f e x n= x^n"
proof-
  have "monoid H (\<cdot>) e"
    by (simp add: A0 group.axioms(1) subgroup_imp_group)
  then show ?thesis
    by (simp add: A0 assms(2) int_pow_def2 monoid.int_pow_def2 monoid.pow_closed)
qed

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

lemma generate_id: "cl_group {e} = {e}" 
  by (meson cl_subgroup group.cl_group_ub group.trivial_subgroup subgroup.subset subgroup_def subgroup_imp_group subset_antisym)
lemma generate_empty: "cl_group {} = {e}" 
  by (metis cl_group_iso cl_subgroup empty_subsetI generate_id group.subgroupE1(2) group_axioms subset_singletonD)


definition cyclic_group where "cyclic_group G \<equiv> (\<exists>x \<in> X. cl_group {x} = G)"
lemma cyclic_group_eq: assumes A0:"G \<subseteq> X" shows "cyclic_group G \<longleftrightarrow> (\<exists>g \<in> X. G =  { pow_int g (k :: int) | k. k \<in> UNIV })" 
  using cyclic_group_def generate_pow by auto
lemma cylic_subgroup_pow:
  assumes A0:"x \<in> X"
  shows "cl_group {x} = cl_group {inv x}"
proof-
  have "cl_group {x} = { pow_int x (k :: int) | k. k \<in> UNIV }" by (simp add: assms generate_pow)
  also have "... = { pow_int x (-(k :: int)) | k. k \<in> UNIV }" by (metis UNIV_I add.inverse_inverse)
  also have "... = {pow_int (inv x) (k :: int)|k. k \<in> UNIV}" using assms int_pow_inv int_pow_neg by presburger
  also have "... = cl_group {inv x}"  using assms generate_pow invertible unit_inv_closed by presburger
  finally show ?thesis by auto
qed

end

subsection \<open>Cyclic Groups\<close>

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
    then show ?thesis  using generate_id  local.cyclic_group_def by auto
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
    have B5:"n > 0" unfolding n_def M_def using B0  
      by (metis (no_types, lifting) LeastI M_def ex_in_conv mem_Collect_eq) 
    have B1:"h \<in> H" unfolding h_def n_def M_def using B0 
      by (metis (mono_tags, lifting) Collect_empty_eq LeastI M_def mem_Collect_eq) 
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
        then obtain B6:"m = n * q + r" and "0 \<le> r" and "r < n" 
          by (metis (no_types, lifting) B0 CollectD LeastI_ex M_def bot_nat_0.extremum ex_in_conv mod_less_divisor mult_div_mod_eq n_def q_def r_def)
        have "x = pow_int g k"  by (simp add: A10)
        also have "... = pow_nat g m" using True int_pow_def2 m_def by auto
        also have "... = pow_nat g (n * q + r)"  by (simp add: B6)
        also have "... = pow_nat g (n * q) \<cdot> (pow_nat g r)" by (simp add: A2 nat_pow_mult)
        finally have B7:"x = pow_nat (pow_nat g n) q \<cdot> (pow_nat g r)"  using A2 nat_pow_pow by auto
        then obtain B8:"pow_int (pow_nat g n) (-(int q)) \<cdot> x = (pow_nat g r)" 
          by (metis A2 A9 group.int_pow_neg group_axioms int_pow_closed int_pow_int inv_lsolve1)
        then have "inv (pow_nat (pow_nat g n) q) \<cdot> x = (pow_nat g r)"  by (simp add: A2 int_pow_neg_int)
        also have "... \<in> H"
          by (metis A1 A8 B1 B8 h_def subgroup.closed subgroup_int_pow_closed)
        then have "r = 0"
          using CollectI M_def \<open>(r::nat) < (n::nat)\<close> n_def not_less_Least by auto 
        then have "n dvd m" 
          by (simp add: mod_eq_0_iff_dvd r_def)
        then have "x \<in> cl_group {h}"
          by (metis A10 A2 B3 B6 \<open>(r::nat) = (0::nat)\<close> \<open>pow_int (g::'a) (k::int) = pow_nat g (m::nat)\<close> add.right_neutral cl_group_extensive cl_subgroup group.subgroup_int_pow_closed group_axioms h_def insert_subset int_pow_int local.power_mult subgroup.subset trivial_subgroup)
        then show ?thesis by auto
      next
        case False
        have B9:"(-k) \<ge> 0"  using False by auto
        define m where "m \<equiv> nat (-k)"
        define q where "q \<equiv> m div n"
        define r where "r \<equiv> m mod n"
        then obtain B6:"m = n * q + r" and "0 \<le> r" and "r < n"  
          by (metis (no_types, lifting) B0 CollectD LeastI_ex M_def bot_nat_0.extremum ex_in_conv mod_less_divisor mult_div_mod_eq n_def q_def r_def)
        have "inv x = pow_int g (-k)"
          using A10 A2 int_pow_neg by presburger
        also have "... = pow_nat g m" 
          using B9 m_def pow_nat by presburger
        also have "... = pow_nat g (n * q + r)"
          by (simp add: B6)
        also have "... = pow_nat g (n * q) \<cdot> (pow_nat g r)" 
          by (simp add: A2 nat_pow_mult)
        finally have B7:"(inv x) = pow_nat (pow_nat g n) q \<cdot> (pow_nat g r)"  
          using A2 local.power_mult by presburger 
        then obtain B8:"pow_int (pow_nat g n) (-(int q)) \<cdot> (inv x) = (pow_nat g r)"    
          by (metis A2 closed int_pow_closed int_pow_int int_pow_neg inv_lsolve1) 
        then have "inv (pow_nat (pow_nat g n) q) \<cdot> (inv x) = (pow_nat g r)"  
          by (simp add: A2 int_pow_neg_int)
        also have "... \<in> H" 
          by (metis A1 A8 B1 B8 group.subgroupE1(3) group_axioms h_def subgroupE1(4) subgroup_int_pow_closed)
        then have "r = 0"
          using CollectI M_def \<open>(r::nat) < (n::nat)\<close> n_def not_less_Least by auto 
        then have "n dvd m" 
          by (simp add: mod_eq_0_iff_dvd r_def)
        then have "inv x \<in> cl_group {h}"
          by (metis B3 B7 \<open>(r::nat) = (0::nat)\<close> cl_group_extensive cl_monoid empty_subsetI h_def insert_subset rid monoid.pow_closed pow_0 pow_closed)
        then obtain "x \<in> cl_group {h}" 
          using A10 A2 inverse_in_cl by fastforce
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
  using assms asc rid apply auto[1]
  by (metis assms closed inv_rsolve2 subset_iff)


end


subsection \<open>Conjugation\<close>
context group
begin

definition rconj where "rconj g x \<equiv> x \<cdot> g \<cdot> inv x"
definition conjugacy_class where "conjugacy_class g \<equiv> {x \<cdot> g \<cdot> inv x|x. x\<in>X}"

lemma rconj_pow:assumes A0:"g\<in>X" and A1:"x\<in>X" shows "(rconj g x)** n=x \<cdot> g **n \<cdot> inv x"
proof(induct n) 
  case 0 then show ?case
    by (simp add: A1)
next
  case (Suc n) then show ?case 
    unfolding rconj_def
    by (simp add: A0 A1 asc inv_lsolve2 m_closed)
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
    by (simp add: A0 A1 asc inv_mult_group m_closed) 
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
    by (simp add: A0 A2 B0 rconj_pow_int) 
  show B2:"\<And>n. h^n=e \<Longrightarrow> g^n=e" 
  proof-   
    fix n assume A4:"h^n=e" then obtain " x \<cdot> g ^n \<cdot> inv x=e"
      by (simp add: A0 A2 B0 rconj_pow_int)  
    then obtain "inv x \<cdot> x \<cdot> g^n \<cdot> inv x \<cdot> x=inv x \<cdot>e \<cdot> x"
      by (metis A0 A2 asc int_pow_closed invertible m_closed monoid.unit_inv_closed monoid_axioms)
    then show "g^n=e"
      by (simp add: A0 A2 asc )
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

lemma commutesI1:"\<lbrakk>a\<in>X; b\<in>X; C[a,b]=e\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a" unfolding elem_commutator_def  using inv_rsolve2 m_closed by force 

lemma commutesI2:"\<lbrakk>a\<in>X; b\<in>X; e=C[a,b]\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a" by (metis commutesI1) 
lemma commutesD1:"\<lbrakk>a\<in>X; b\<in>X; a\<cdot>b=b\<cdot>a\<rbrakk> \<Longrightarrow>C[a,b]=e" unfolding elem_commutator_def  by (metis inv_rsolve1 m_closed r_inv_simp) 
lemma commutesD2:"\<lbrakk>a\<in>X; b\<in>X; a\<cdot>b=b\<cdot>a\<rbrakk> \<Longrightarrow>e=C[a,b]" unfolding elem_commutator_def  using commutesD1 elem_commutator_def by force 
lemma commutes_iff1:"\<lbrakk>a\<in>X; b\<in>X\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a \<longleftrightarrow> C[a,b]=e"  using commutesD1 commutesI1 by blast
lemma commutes_iff2:"\<lbrakk>a\<in>X; b\<in>X\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a \<longleftrightarrow> e=C[a,b]"  using commutesD2 commutesI2 by blast
lemma commutes_inv:"\<lbrakk>a\<in>X; b\<in>X\<rbrakk> \<Longrightarrow> C[b,a]=inv C[a,b]" unfolding elem_commutator_def  by (simp add: asc group.inv_mult_group group_axioms m_closed) 


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
print_facts
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
  assumes A0:"g \<in> X" and A1:"k \<in> Ker"
  shows "g \<cdot> k \<cdot> dom.inv g \<in> Ker"
  using A0 A1 conj_closed by blast

end


context group
begin
lemma subgroup_units:
  assumes A0:"subgroup H X (\<cdot>) e" 
  shows "H \<subseteq> Units"
  by (meson assms invertible mem_UnitsI subgroup.sub_mem subsetI)
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
    by (metis A0 A1 H_def bex_empty equivalence_relation.p_closed2 equivalence_relation.p_self group.top_subgroup p_def subgroup.id_mem)
  have B2:"\<And>a. a \<in> H \<Longrightarrow> (e, a) \<in> R"
    by (metis A0 A1 H_def equivalence_relation.p_D1 group.top_subgroup p_def subgroup.id_mem)
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
    using A0 A2 group.axioms(1) B2 group.invertible group.l_inv_simp l_congD1 monoid.inv_rcancel by fastforce
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
      by (simp add: A0 group.axioms(1) group.inv_mult_group group.invertible group.remove_id1 monoid.unit_inv_closed z0)
    then show "(z \<cdot> x, z \<cdot> y)\<in>R"
      unfolding R_def using zx0 zy0 xy1 by force
  qed
qed
   
context subgroup
begin

definition subgroup_eqr ("R") where "subgroup_eqr \<equiv> {(x, y) \<in> G\<times>G. inv x \<cdot> y \<in> H}"

lemma subgroup_eqr_is_eqr:"equivalence_relation G R"
  apply(unfold_locales)
  apply(auto simp add:subgroup_eqr_def)
  using l_coset_equivs(2) apply blast
  by (metis subgroup.l_coset_equivs(1) subgroup_axioms)


lemma subgroup_eqr_is_cong: "l_cong G (\<cdot>) R"
  using group_axioms quotient_groups_theorem2(2) subgroup_axioms subgroup_eqr_def by fastforce

lemma subgroup_eqrI1:"\<lbrakk>x \<in> G;y \<in> G; h \<in> H; inv x \<cdot> y \<in> H\<rbrakk> \<Longrightarrow> (x, y) \<in>R" 
  by(simp add: subgroup_eqr_def)

lemma subgroup_eqrD1:"(x, y) \<in>R \<Longrightarrow> x \<in> G \<and> y \<in> G" by(simp add: subgroup_eqr_def)

lemma subgroup_eqrD2:"(x, y) \<in>R \<Longrightarrow>  inv x \<cdot> y \<in> H" 
  by(simp add: subgroup_eqr_def)

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


subsection \<open>Group Actions\<close>
context monoid_operating_on_set
begin
definition "transporter \<equiv> (\<lambda>A \<in> Pow E. \<lambda>B \<in> Pow E. {m \<in> M. (\<alpha> m)`A \<subseteq> B})"
definition "strict_transporter \<equiv> (\<lambda>A \<in> Pow E. \<lambda>B \<in> Pow E. {m \<in> M. (\<alpha> m)`A = B})"

definition "stabilizer \<equiv> (\<lambda>A \<in> Pow E. {m \<in> M. (\<alpha> m)`A \<subseteq> A})"
definition "strict_stabilizer \<equiv> (\<lambda>A \<in> Pow E. {m \<in> M. (\<alpha> m)`A = A})"

definition "fixer \<equiv> (\<lambda>A \<in> Pow E. {m \<in> M. \<forall>a. a \<in> A \<longrightarrow> (\<alpha> m) a = a})"

lemma comp_simp:"\<And>x. x \<in> E \<Longrightarrow> m \<in> M \<Longrightarrow> n \<in> M \<Longrightarrow> \<alpha> (m \<cdot> n) x = (\<alpha> m) ((\<alpha> n) x)"
  by (simp add: comp compose_eq)

lemma im_comp_simp:"\<And>x. A \<in> Pow E \<Longrightarrow> m \<in> M \<Longrightarrow> (\<alpha> n)`A \<in> Pow E \<Longrightarrow> n \<in> M \<Longrightarrow> \<alpha> (m \<cdot> n)`A = (\<alpha> m)`((\<alpha> n)`A)"
  by(auto simp add:comp_simp in_mono)

lemma fixer_sub_stric_stab:"fixer A \<subseteq> strict_stabilizer A"
  unfolding fixer_def strict_stabilizer_def by(auto)

lemma stric_stab_sub_stab:"strict_stabilizer A \<subseteq> stabilizer A"
  unfolding stabilizer_def strict_stabilizer_def by(auto)

lemma fixer_sub_stab:"fixer A \<subseteq> stabilizer A"
  using fixer_sub_stric_stab stric_stab_sub_stab by auto

lemma stabilizer_memI:"\<lbrakk>A \<in> Pow E; m \<in> M; (\<And>a. a \<in> A \<Longrightarrow> \<alpha> m a \<in> A)\<rbrakk> \<Longrightarrow> m \<in> stabilizer A"  unfolding stabilizer_def by(auto)

lemma stab_memI:"\<lbrakk>A \<in> Pow E;  m \<in>stabilizer A; n \<in> stabilizer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> stabilizer A"
proof-
  fix A m n assume A0:"A \<in> Pow E"  and m0:"m \<in>stabilizer A" and n0:"n \<in> stabilizer A"
  then obtain m1:"(\<alpha> m)`A \<subseteq> A" and n1:"(\<alpha> n)`A \<subseteq> A" and m2:"m \<in> M" and n2:"n \<in> M"
    unfolding stabilizer_def using A0 by force
  then obtain eq1:"\<alpha> (m \<cdot> n) =  compose E (\<alpha> m) (\<alpha> n)"
    by (simp add: comp)
  then have "\<alpha> (m \<cdot> n)`A = (compose E (\<alpha> m) (\<alpha> n))`A"
    by presburger
  also have "... \<subseteq> A"
    using im_restrict_sub A0 m1 n1 by blast
  finally have "\<alpha> (m \<cdot> n)`A \<subseteq> A"
    by blast
  then show "(m \<cdot> n) \<in> stabilizer A"
    using A0 m2 n2 opposite.closed stabilizer_def by force  
qed

lemma stict_stab_memI:"\<lbrakk>A \<in> Pow E; m \<in>strict_stabilizer A; n \<in> strict_stabilizer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> strict_stabilizer A"
proof-
  fix A m n assume A0:"A \<in> Pow E" and m0:"m \<in>strict_stabilizer A" and n0:"n \<in> strict_stabilizer A"
  then obtain m1:"(\<alpha> m)`A = A" and n1:"(\<alpha> n)`A = A" and m2:"m \<in> M" and n2:"n \<in> M"
    unfolding strict_stabilizer_def using A0 by force
  then obtain eq1:"\<alpha> (m \<cdot> n) =  compose E (\<alpha> m) (\<alpha> n)"
    by (simp add: comp)
  then have "\<alpha> (m \<cdot> n)`A = (compose E (\<alpha> m) (\<alpha> n))`A"
    by presburger
  also have "... = A"
    by (meson A0 im_restrict_eq2 m1 n1)
  finally have "\<alpha> (m \<cdot> n)`A = A"
    by blast
  then show "(m \<cdot> n) \<in> strict_stabilizer A"
    using A0 m2 n2 opposite.closed strict_stabilizer_def by force  
qed

lemma fix_memI:"\<lbrakk>A \<in> Pow E;  m \<in>fixer A; n \<in> fixer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> fixer A"
proof-
  fix A m n assume A0:"A \<in> Pow E" and m0:"m \<in>fixer A" and n0:"n \<in> fixer A"
  then obtain m1:"\<And>a. a \<in> A \<Longrightarrow> (\<alpha> m) a = a" and n1:"\<And>a. a \<in> A \<Longrightarrow> (\<alpha> n) a = a" and m2:"m \<in> M" and n2:"n \<in> M"
    unfolding fixer_def using A0 by force
  then obtain eq1:"\<alpha> (m \<cdot> n) =  compose E (\<alpha> m) (\<alpha> n)"
    by (simp add: comp)
  then have "\<And>a. a \<in> A \<Longrightarrow> \<alpha> (m \<cdot> n) a = (compose E (\<alpha> m) (\<alpha> n)) a"
    by presburger
  then have "\<And>a. a \<in> A \<Longrightarrow> \<alpha> (m \<cdot> n) a = a"
    by (metis A0 PowD compose_eq in_mono m1 n1)
  then show "(m \<cdot> n) \<in>fixer A"
    using A0 m2 n2 opposite.closed fixer_def by force  
qed

lemma id_apply:"A \<in> Pow E \<Longrightarrow> (\<alpha> e)`A = A"
  using unid by auto

lemma stric_stab_inv_cl:"A \<in> Pow E \<Longrightarrow> invertible m \<Longrightarrow> m \<in>strict_stabilizer A  \<Longrightarrow>inv  m \<in> strict_stabilizer A "
proof-
  fix A m assume A0:"A \<in> Pow E" and A1:"invertible m" and A2:"m \<in> strict_stabilizer A"
  then obtain B0:"m \<in> M" and B1:"inv m \<in> M" and B2:"(\<alpha> m)`A=A" and B3:"(\<alpha> m)`A \<in> Pow E"
    by (simp add: strict_stabilizer_def)
  then have "(\<alpha> m)`A=A"
    using A0 A2 strict_stabilizer_def by auto
  also have "... = (\<alpha> e)`A"
    using A0 local.id_apply by auto
  also have "... = (\<alpha> ((inv m) \<cdot> m))`A"
    using A1 B0 unit_linv by presburger
  also have "... = (\<alpha> (inv m))`((\<alpha> m)`A)"
    by (meson A0 B0 B1 B3 im_comp_simp)
  then have "(\<alpha> (inv m))`A = A"
    using B2 calculation by presburger 
  then show "inv m \<in> strict_stabilizer A"
    using A0 B1 strict_stabilizer_def by auto
qed


lemma fix_inv_cl:"A \<in> Pow E \<Longrightarrow> invertible m \<Longrightarrow> m \<in>fixer A  \<Longrightarrow>inv  m \<in> fixer A "
proof-
  fix A m assume A0:"A \<in> Pow E" and A1:"invertible m" and A2:"m \<in> fixer A"
  then obtain B0:"m \<in> M" and B1:"inv m \<in> M" and B2:"\<And>a. a \<in> A \<Longrightarrow> (\<alpha> m) a= a" 
    by (simp add: fixer_def)
  have "\<And>a. a \<in> A \<Longrightarrow> (\<alpha> (inv m)) a = a"
  proof-
    fix a assume A3:"a \<in> A" then obtain A4:"a \<in> E" using A0 by auto
    have "a =(\<alpha> e) a"
      by (metis A0 A3 Pow_iff monoid_operating_on_set.unid monoid_operating_on_set_axioms restrict_apply subsetD)
    also have "... = \<alpha> ((inv m) \<cdot> m) a"
      by (simp add: A1 B0)
    also have "... = (\<alpha> (inv m)) ((\<alpha> m) a) "
      using A4 comp_simp[of a "inv m" m] B0 B1 by auto
    also have "... = (\<alpha> (inv m)) a"
      using A3 B2 by presburger
    finally show "(\<alpha> (inv m)) a = a"
      by simp
  qed
  then show "(inv m) \<in> fixer A"
    using A0 B1 fixer_def by force
qed


lemma b151prop11:
  assumes A0:"A \<in> Pow E"
  shows  "\<And>a. a \<in> A \<Longrightarrow> \<alpha> e a = a" and
         "e \<in> fixer A" and 
         "e \<in> stabilizer A" and
         "e \<in> strict_stabilizer A" and
         "\<And>m n. \<lbrakk>m \<in>stabilizer A; n \<in> stabilizer A\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n)`A \<subseteq> A" and
         "\<And>m n. \<lbrakk>m \<in>stabilizer A; n \<in> stabilizer A\<rbrakk> \<Longrightarrow>(m \<cdot> n) \<in> stabilizer A" and
         "\<And>m n. \<lbrakk>m \<in>strict_stabilizer A; n \<in> strict_stabilizer A\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n)`A =A" and
         "\<And>m n. \<lbrakk>m \<in>strict_stabilizer A; n \<in> strict_stabilizer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> strict_stabilizer A" and
         "\<And>m n. \<lbrakk>m \<in>fixer A; n \<in> fixer A\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n)`A  = A" and
         "\<And>m n. \<lbrakk>m \<in>fixer A; n \<in> fixer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> fixer A" and
         "stabilizer A \<subseteq> M" and "strict_stabilizer A \<subseteq> M" and "fixer A \<subseteq> M" and
         "submonoid (stabilizer A) M (\<cdot>) e" and
         "submonoid (strict_stabilizer A) M (\<cdot>) e" and
         "submonoid (fixer A) M (\<cdot>) e" and
         "\<And>m. invertible m \<Longrightarrow> m \<in> strict_stabilizer A \<Longrightarrow> inv m \<in> strict_stabilizer A" and
         "\<And>m. invertible m \<Longrightarrow> m \<in> fixer A \<Longrightarrow> inv m \<in> fixer A"
proof-
  show P0:"\<And>a. a \<in> A \<Longrightarrow> \<alpha> e a = a"
    using A0 monoid_operating_on_set.unid monoid_operating_on_set_axioms by fastforce
  show P1:"e \<in> fixer A"
    using A0 fixer_def P0 by force
  show P2:"e \<in> stabilizer A"
    using P1 fixer_sub_stab by auto 
  show P3:"e \<in> strict_stabilizer A"
    using P1 fixer_sub_stric_stab by auto 
  show P4:"\<And>m n. \<lbrakk>m \<in>stabilizer A; n \<in> stabilizer A\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n)`A \<subseteq> A"
    using assms stab_memI stabilizer_def by auto
  show P5:"\<And>m n. \<lbrakk>m \<in>stabilizer A; n \<in> stabilizer A\<rbrakk> \<Longrightarrow>(m \<cdot> n) \<in> stabilizer A"
    using assms stab_memI by auto
  show P6:"\<And>m n. \<lbrakk>m \<in>strict_stabilizer A; n \<in> strict_stabilizer A\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n)`A =A"
    using assms stict_stab_memI strict_stabilizer_def by force 
  show P7:"\<And>m n. \<lbrakk>m \<in>strict_stabilizer A; n \<in> strict_stabilizer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> strict_stabilizer A"
    using assms stict_stab_memI by auto 
  show P8:"\<And>m n. \<lbrakk>m \<in>fixer A; n \<in> fixer A\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n)`A  = A" 
    using assms fix_memI fixer_def by auto
  show P9:  "\<And>m n. \<lbrakk>m \<in>fixer A; n \<in> fixer A\<rbrakk> \<Longrightarrow> (m \<cdot> n) \<in> fixer A" 
    using assms fix_memI by auto
  show P10: "stabilizer A \<subseteq> M" 
    using assms stabilizer_def by auto
  show P11:"strict_stabilizer A \<subseteq> M" 
    using assms strict_stabilizer_def by auto
  show P12:"fixer A \<subseteq> M"
    using assms fixer_def by auto
  show P13:"submonoid (stabilizer A) M (\<cdot>) e"
    apply(unfold_locales)
    apply (simp add: P10)
    apply (simp add: P5)
    by (simp add: P2)
  show P13:"submonoid (strict_stabilizer A) M (\<cdot>) e"
    apply(unfold_locales)
    apply (simp add: P11)
    apply (simp add: P7)
    by (simp add: P3)
  show P14:"submonoid (fixer A) M (\<cdot>) e"
    apply(unfold_locales)
    apply (simp add: P12)
    apply (simp add: P9)
    by (simp add: P1)
  show P15: "\<And>m. invertible m \<Longrightarrow> m \<in> strict_stabilizer A \<Longrightarrow> inv m \<in> strict_stabilizer A"
    using assms stric_stab_inv_cl by auto 
  show P16: "\<And>m. invertible m \<Longrightarrow> m \<in> fixer A \<Longrightarrow> inv m \<in> fixer A"
    using assms fix_inv_cl by auto 
qed

lemma singleton_strict_stab_eq_stab:
  assumes A0:"a \<in> E"
  shows "stabilizer {a} = strict_stabilizer {a}" and
        "strict_stabilizer {a} = fixer {a}" and
        "stabilizer {a} = fixer {a}"
proof-
  show P0:"stabilizer {a} = strict_stabilizer {a}"
    using A0 unfolding stabilizer_def strict_stabilizer_def by(auto)
  show P1:"strict_stabilizer {a} = fixer {a}"
    using A0 unfolding strict_stabilizer_def fixer_def by(auto)
  show "stabilizer {a} = fixer {a}"
    using P0 P1 by simp
qed

lemma singleton_stabilizer_memI:"\<lbrakk>x \<in> E;m \<in> M; \<alpha> m x  = x\<rbrakk> \<Longrightarrow>m \<in> stabilizer {x}"  unfolding stabilizer_def by(auto)
lemma singleton_stabilizer_memD:"x \<in> E \<Longrightarrow> m \<in> stabilizer {x} \<Longrightarrow>  \<alpha> m x  = x \<and> m \<in> M"  unfolding stabilizer_def by(auto)
lemma singleton_stabilizer_memD1:"x \<in> E \<Longrightarrow> m \<in> stabilizer {x} \<Longrightarrow>  \<alpha> m x  = x"  unfolding stabilizer_def by(auto)
lemma singleton_stabilizer_memD2:"x \<in> E \<Longrightarrow> m \<in> stabilizer {x} \<Longrightarrow> m \<in> M"  unfolding stabilizer_def by(auto)

end

locale transformations_notation=fixes X::"'a set"
begin
sublocale monoid "(set_morphisms X X)" "(compose X)" "Id X" by (simp add: composition_monoid)

lemma inv_iff_bij_betw:
  "\<sigma> \<in> (set_morphisms X X) \<Longrightarrow> invertible \<sigma> \<longleftrightarrow> bij_betw \<sigma> X X" 
  using set_morphism.bij_betw_iff_has_inverse set_morphismI1 by fastforce

lemma inv_eq_inv:
  assumes A0:"\<sigma> \<in> set_morphisms X X" and A1:"invertible \<sigma>"
  shows "inv \<sigma> = rinv \<sigma> X X"
proof-
  obtain B0:"compose X (rinv \<sigma> X X) \<sigma> = Id X" and B1:"compose X \<sigma> (rinv \<sigma> X X) = Id X"
    by (metis A0 A1 bij_betw_def inv_iff_bij_betw inv_rinv2 rinv_inv) 
  then show ?thesis
    using A0 A1 bij_betw_hom_rev inv_eq inv_iff_bij_betw by blast
qed

lemma Units_bij_betwI [intro, simp]:
  "\<sigma> \<in> Units \<Longrightarrow> bij_betw \<sigma> X X"
  using inv_iff_bij_betw mem_UnitsD by blast


lemma Units_bij_betwD [dest, simp]:
  "\<lbrakk>\<sigma>\<in> set_morphisms X X; bij_betw \<sigma> X X\<rbrakk> \<Longrightarrow> \<sigma> \<in> Units"
  using inv_iff_bij_betw mem_UnitsI by presburger


lemma set_iso_unital1:
  "Units = {\<sigma> \<in> (set_morphisms X X). bij_betw \<sigma> X X}"
  using mem_UnitsD by auto

lemma set_iso_unital2:
  "Units = set_isomorphisms X X"
proof-
  have "Units = {\<sigma> \<in> (set_morphisms X X). bij_betw \<sigma> X X}"
    using set_iso_unital1 by blast
  also have "... \<subseteq> set_isomorphisms X X"
    using set_isomorphism_memI2 by auto
  also have "... \<subseteq> Units"
    using set_isomorphismE2 set_isomorphisms_eq_set_morphisms_inter_bijs by fastforce
  finally show ?thesis
    by auto
qed

sublocale symmetric: group "Units" "compose X" "Id X"
  by (simp add: composition_monoid monoid.group_of_units)

end


locale symmetric_group=transformations_notation X+subgroup G "Units" "compose X" "Id X"  for G and X
begin
lemma closed [intro, simp]:
  "\<lbrakk> \<sigma> \<in> G; x \<in> X \<rbrakk> \<Longrightarrow> \<sigma> x \<in> X"
  using bij_betwE by blast

lemma undef[intro, simp]:
  "\<lbrakk> \<sigma> \<in> G; x \<notin>X \<rbrakk> \<Longrightarrow> \<sigma> x = undefined"
  by (meson hom10 mem_UnitsD subsetD subset)

lemma inv_set_inv:"g \<in> G \<Longrightarrow> inv g = (rinv g X X)"
  using inv_eq_inv mem_UnitsD sub_mem by presburger

end


locale permutation_group=transformations_notation X for X
begin

end

section \<open>Group Operating on a set\<close>
locale group_operating_on_set= group G "(\<cdot>)" e+action G E \<alpha> 
  for G::"'a set" and 
      law::"'a\<Rightarrow>'a\<Rightarrow>'a" (infixl "\<cdot>" 70) and
      unit::"'a" ("e") and
      E::"'b set" and
      \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b" +
  assumes unid[simp]:"\<alpha> e = Id E" and
          comp[simp]:"\<lbrakk>x\<in>G;y\<in>G\<rbrakk> \<Longrightarrow> \<alpha> (x \<cdot> y) = compose E (\<alpha> x) (\<alpha> y)"
begin


sublocale monoid_operating_on_set G "(\<cdot>)" e E \<alpha>
  apply(rule monoid_operating_on_set.intro)
  apply (simp add: monoid_axioms)
  apply (simp add: action_axioms)
  by (simp add: monoid_operating_on_set_axioms.intro)


lemma translation_exist:
  "\<gamma> \<in> \<alpha>`G \<Longrightarrow> \<exists>g \<in> G. \<gamma> = \<alpha> g"
  by auto

lemmas Translations_E [elim] = translation_exist [THEN bexE]


lemma iso_linv:"\<And>g. g \<in> G \<Longrightarrow> compose E (\<alpha> g) (\<alpha> (inv g)) = Id E"
proof-
  fix g assume A0:"g \<in> G"
  show "compose E (\<alpha> g) (\<alpha> (inv g)) = Id E"
    using A0 by (metis comp inv_commute inv_eq l_inv_ex unid) 
qed

lemma iso_rinv:"\<And>g. g \<in> G \<Longrightarrow> compose E (\<alpha> (inv g)) (\<alpha> g) = Id E"
proof-
  fix g assume A0:"g \<in> G"
  show "compose E (\<alpha>(inv g)) (\<alpha> g)  = Id E"
    using A0 by (metis comp inv_eq l_inv_ex unid) 
qed


lemma iso_inj:"\<And>g x y. \<lbrakk>g\<in> G; x\<in> E; y \<in> E;  \<alpha> g x = \<alpha> g y\<rbrakk> \<Longrightarrow> x = y"
proof-
  fix g x y assume A0:"g \<in> G" and A1:" x\<in> E" and A2:" y\<in> E" and A3:"\<alpha> g x = \<alpha> g y"
  then have "x = compose E (\<alpha> (inv g)) (\<alpha> g) x"
    by (simp add: iso_rinv)
  also have "... = compose E (\<alpha> (inv g)) (\<alpha> g) y"
    by (simp add: A1 A2 A3 compose_eq)
  also have "... = y"
    by (simp add: A0 A2 group_operating_on_set.iso_rinv group_operating_on_set_axioms)
  finally show "x=y"
    by blast
qed



lemma iso_ex:" \<And>g x. g \<in> G \<Longrightarrow> x \<in> E \<Longrightarrow> x \<in> (\<alpha> g) ` E"
proof-
  fix g x assume A0:"g \<in> G" and A1:" x\<in> E" 
  define y where"y = (\<alpha> (inv g)) x"
  then obtain B0:"y \<in> E" and B1:"inv g \<in> G"
    using A0 A1 by blast
  have "x = Id E x"
    by (simp add: A1)
  also have "... = compose E (\<alpha> g) (\<alpha> (inv g)) x"
    using A0 iso_linv by presburger
  also have "... \<in> (\<alpha> g)`E"
    by (simp add: A1 B1 compose_eq)
  finally show "x \<in> (\<alpha> g) ` E"
    by blast
qed


sublocale iso:group "(set_isomorphisms E E)" "(compose E)" "(Id E)"
  by (metis composition_monoid monoid.group_of_units transformations_notation.set_iso_unital2)
    
sublocale iso:set_morphism \<alpha> G "set_isomorphisms E E"
  apply(unfold_locales)
  apply(auto simp add:set_isomorphisms_def)
  using iso_inj apply blast
  using iso_ex by blast

sublocale iso:group_homomorphism \<alpha> G "(\<cdot>)" "set_isomorphisms E E" "compose E" e "Id E"
  apply(rule group_homomorphism.intro)
  apply (simp add: iso.set_morphism_axioms)
  apply (simp add: group_axioms)
  apply (simp add: iso.group_axioms)
  by (simp add: group_homomorphism_axioms.intro)


abbreviation "Im \<equiv> \<alpha>`G"

lemma Imsub:"Im \<subseteq> set_isomorphisms E E"
  by blast


sublocale im:monoid Im "(compose E)" "(Algebrah11.Id E)"
    apply(rule monoid.intro)
     apply(rule semigroup.intro)
  apply(rule magma.intro)
      apply (meson iso.im.opsub)
  apply(rule semigroup_axioms.intro)
  using iso.im.sub.asc apply presburger
  apply(rule monoid_axioms.intro)
  using iso.im.sub.idin unid apply argo
  apply blast
  by blast

lemma bozo:"\<And>u::'b \<Rightarrow> 'b. u \<in> Im \<Longrightarrow> im.invertible u"
proof-
  fix u assume A0:"u \<in> Im" 
  then obtain g where g0:"g \<in> G" and g1:"u = \<alpha> g"
    by blast
  then obtain g2:"\<alpha> (inv g) = im.inv u"
    by (metis im.inv_eq image_eqI invertible iso.map_inv_id(2) iso_linv unit_inv_closed)
  then obtain "\<alpha> (inv g) \<in> Im"
    using g0 by blast
  then show "im.invertible u"
    by (metis A0 g0 g1 iso.im.sub.invertibleI iso.map_inv_id(1) iso_rinv unid)
qed

sublocale im:group_homomorphism \<alpha> G "(\<cdot>)" "Im" "compose E" e "Id E"
  apply(rule group_homomorphism.intro)
  apply (simp add: set_morphism.intro)
    apply (simp add: group_axioms)
   apply(rule group.intro)
    apply(rule monoid.intro)
     apply(rule semigroup.intro)
  apply(rule magma.intro)
      apply (meson iso.im.opsub)
  apply(rule semigroup_axioms.intro)
  using iso.im.sub.asc apply presburger
  apply(rule monoid_axioms.intro)
  using iso.im.sub.idin unid apply argo
  apply blast
  apply blast
   apply (rule group_axioms.intro)
  using bozo apply presburger
  by (simp add: group_homomorphism_axioms.intro)

lemma strict_stab_sub:
  assumes A0:"A \<in> Pow E"
  shows "subgroup (strict_stabilizer A) G (\<cdot>) e" 
  apply(rule subgroup.intro)
   apply (simp add: group_axioms)
  apply(rule subgroup_axioms.intro)
  using assms b151prop11(12) apply presburger
  using assms stict_stab_memI apply blast
  using assms b151prop11(4) apply blast
  by (meson assms b151prop11(12) invertible stric_stab_inv_cl subsetD)


lemma fix_sub:
  assumes A0:"A \<in> Pow E"
  shows "subgroup (fixer A) G (\<cdot>) e" 
  apply(rule subgroup.intro)
   apply (simp add: group_axioms)
  apply(rule subgroup_axioms.intro)
  using assms b151prop11(13) apply presburger
  using assms fix_memI apply blast
  using assms b151prop11(2) apply blast
  by (meson assms b151prop11(13) invertible fix_inv_cl subsetD)


lemma fix_sub_strict:
  assumes A0:"A \<in> Pow E"
  shows "subgroup (fixer A) (strict_stabilizer A) (\<cdot>) e" 
   apply(rule subgroup.intro)
  using assms strict_stab_sub subgroup_imp_group apply presburger 
   apply(rule subgroup_axioms.intro)
  apply (simp add: fixer_sub_stric_stab)
  using assms fix_memI apply blast
  using assms b151prop11(2) apply blast
  by (metis assms b151prop11(13) fix_inv_cl fixer_sub_stric_stab invertible strict_stab_sub subgroup_inv_eq subsetD)

lemma fix_norm_sub:
  assumes A0:"A \<in> Pow E" and A1:"g \<in> (strict_stabilizer A)" and A2:"h \<in> fixer A" 
  shows  "g \<cdot> h \<cdot> inv g \<in>  (fixer A)"
proof-
  obtain B0:"g \<in> G" and B1:"(\<alpha> g)`A = A" and B2:"h \<in> G" and B3:"\<And>a. a \<in> A \<Longrightarrow> (\<alpha> h) a = a"
    using A0 A1 A2 unfolding strict_stabilizer_def fixer_def by(auto)
  then obtain B4:"inv g \<in> (strict_stabilizer A)" and B5:"(inv g) \<in> G"
    using A0 A1 invertible strict_stab_sub subgroupE1(3) unit_inv_closed by presburger
  then obtain B6:"(\<alpha> (inv g))`A = A"
     using A0  unfolding strict_stabilizer_def by(auto)
  have B7:"\<And>a. a \<in> A \<Longrightarrow> (\<alpha> (g \<cdot> h \<cdot> inv g)) a = a"
  proof-
    fix a assume A3:"a \<in> A" then obtain A4:"a \<in> E" and B8:"(\<alpha> (inv g)) a \<in> A" using A0 A3 B6 by auto
    then obtain B9:"(\<alpha> h ) ((\<alpha> (inv g)) a) =  (\<alpha> (inv g)) a"
      using B3 by blast
    have "(\<alpha> (g \<cdot> h \<cdot> inv g)) a = (\<alpha> g ) ((\<alpha> h ) ((\<alpha> (inv g)) a))"
      using A4 B0 B2 B5 actsE211 comp_simp opposite.closed by presburger
    also have "(\<alpha> g ) ((\<alpha> h ) ((\<alpha> (inv g)) a)) = (\<alpha> g) ((\<alpha> (inv g)) a)"
     using B9 by presburger
    also have "... = \<alpha> (g \<cdot> (inv g)) a"
     using A4 B0 B5 comp_simp by presburger
    also have "... = (\<alpha> e) a"
     by (simp add: B0)
    also have "... = a"
     by (simp add: A4)
    finally show " (\<alpha> (g \<cdot> h \<cdot> inv g)) a = a"
      by auto
  qed
  have B10:"((g \<cdot> h \<cdot> inv g)) \<in> G"
    using B0 B2 B5 opposite.closed by presburger
  show ?thesis
    unfolding fixer_def using A0 B7 B10 by(auto)
qed

lemma fix_norm_subgroup:
 assumes A0:"A \<in> Pow E"
 shows "normal_subgroup (fixer A) (strict_stabilizer A) (\<cdot>) e" 
  apply(rule normal_subgroup.intro)
  using assms fix_sub_strict apply blast
  apply(rule normal_subgroup_axioms.intro)
  using assms fix_norm_sub strict_stab_sub by auto

end

locale group_acting_on_self=group G "(\<cdot>)" e for G and law (infixl "\<cdot>" 70) and e
begin

sublocale monoid_operating_on_set G "(\<cdot>)" e G l_trans
  apply(rule monoid_operating_on_set.intro)
  apply (simp add: monoid_axioms)
  apply (simp add: l_action.action_axioms)
  by (simp add: ltranslation_comp ltranslation_id monoid_operating_on_set_axioms.intro)

sublocale group_operating_on_set G "(\<cdot>)" e G l_trans
  apply(rule group_operating_on_set.intro)
  apply (simp add: group_axioms)
  apply (simp add: l_action.action_axioms)
  by (simp add: group_operating_on_set_axioms.intro left_trans_comp ltranslation_id)


sublocale im:set_morphism l_trans G "Im"
  using im.set_morphism_axioms by blast

lemma trans_inj:" inj_on l_trans G"
  by (simp add: inj_on_def l_trans_inj1)

sublocale im:set_monomorphism l_trans G "Im"
  apply(unfold_locales)
  by (simp add: trans_inj)

sublocale im:set_epimorphism l_trans G "Im"
  using im.mem_hom set_epiI1 by blast

sublocale im:set_isomorphism l_trans G "Im"
  using im.set_epimorphism_mem im.set_monomorphism_mem set_isomorphism_iff set_isomorphism_memI1 by blast

sublocale im:group_isomorphism l_trans G "(\<cdot>)" "Im" "compose G" e "Id G"
  apply(rule group_isomorphism.intro)
  using im.set_isomorphism_axioms apply blast
  apply (simp add: group_axioms)
  using im.cod.group_axioms apply blast
  by (simp add: group_isomorphism_axioms.intro)

end


context
group_operating_on_set
begin
lemma stabilizer_conj:
  assumes A0:"x \<in> E" and A1:"g \<in> G"
  shows "stabilizer {\<alpha> g x} = {g \<cdot> h \<cdot> (inv g)|h. h \<in> stabilizer {x}}"
proof-
  have P0:"\<alpha> g x \<in> E"
    by (simp add: A0 A1)
  have B0:" {g \<cdot> h \<cdot> (inv g)|h. h \<in> stabilizer {x}} \<subseteq> stabilizer {\<alpha> g x}"
  proof
    fix s assume A2:"s \<in> {g \<cdot> h \<cdot> (inv g)|h. h \<in> stabilizer {x}}"
    then obtain h where B1:"h \<in> stabilizer {x}" and B2:"s = g \<cdot> h \<cdot> (inv g)" 
      by blast
    then obtain B3:"h \<in> G" and B4:"\<alpha> h x = x"
      using B1 A0 unfolding stabilizer_def by auto
    have B5:"g \<cdot> h \<cdot> (inv g) \<in> G"
      using B3 A1 by (simp add: opposite.closed) 
    then have "\<alpha> s (\<alpha> g x) = \<alpha> (g \<cdot> h \<cdot> (inv g)) (\<alpha> g x) "
      using B2 by blast
    also have "... = \<alpha> (g \<cdot> h \<cdot> (inv g) \<cdot> g) x"
      using A0 A1 B5 comp_simp by presburger
    also have "... = \<alpha> (g \<cdot> h) x"
      by (simp add: A1 B3 asc opposite.closed)
    also have "... = \<alpha> g (\<alpha> h x)"
      using A0 A1 B3 comp_simp by presburger
    also have "... = \<alpha> g x"
      using B4 by presburger
    finally obtain B6:"\<alpha> s (\<alpha> g x) = \<alpha> g x"
      by blast
    show "s \<in>  stabilizer {\<alpha> g x}" 
      apply(rule stabilizer_memI)
      apply (simp add:P0)
      using B2 B5 apply blast
      using B6 by fastforce
  qed
  have B2:"x = \<alpha> (inv g) (\<alpha> g x)"
    by (metis A0 A1 actsE211 comp_simp idin inv2_prod inv_ident iso_inj l_inv_simp rid)
  have B3:"{inv g \<cdot> h \<cdot> g|h. h \<in> stabilizer {\<alpha> g x}} \<subseteq> stabilizer {x}"
  proof
    fix k assume A2:"k \<in> {inv g \<cdot> h \<cdot> g|h. h \<in> stabilizer {\<alpha> g x}}" 
    then obtain h where B4:"h \<in> stabilizer {\<alpha> g x}" and B5:"k = inv g \<cdot> h \<cdot> g" 
      by blast
    then obtain B6:"h \<in> G" and B7:"k \<in> G" and B8:"\<alpha> h (\<alpha> g x) = \<alpha> g x"
      using P0 A1 opposite.closed singleton_stabilizer_memD  subgroupE1(3) top_subgroup by presburger
    have "\<alpha> k x = \<alpha> (inv g \<cdot> h \<cdot> g) x"
      using B5 by blast
    also have "... = \<alpha> (inv g) (\<alpha> h (\<alpha> g x))"
      by (metis A0 A1 B6 P0 comp_simp idin inv2_prod inv_ident opposite.closed rid)
    also have "... = \<alpha> (inv g) (\<alpha> g x)"
      using B8 by presburger
    also have "... = x"
      using B2 by presburger
    finally have "\<alpha> k x = x"
      by blast
    then show "k \<in> stabilizer {x}"
      using A0 B7 singleton_stabilizer_memI by blast
  qed
  have B3:"stabilizer {\<alpha> g x} \<subseteq> {g \<cdot> h \<cdot> (inv g)|h. h \<in> stabilizer {x}} "
  proof
    fix s assume A2:"s \<in> stabilizer {\<alpha> g x}"
    then obtain B4:"s \<in> G" and B5:"\<alpha> s (\<alpha> g x) = \<alpha> g x"
      using P0 singleton_stabilizer_memD[of "\<alpha> g x" s] by blast 
    have B6:"inv g \<cdot> s \<cdot> g \<in> stabilizer {x}"
      using A2 B3 by blast
    have B7:"s = g \<cdot> (inv g \<cdot> s \<cdot> g) \<cdot> (inv g)"
      by (metis A1 B4 asc inv2_prod inv_lsolve1 inv_rsolve1 opposite.closed)
    then show "s \<in> {g \<cdot> h \<cdot> (inv g)|h. h \<in> stabilizer {x}}"
      using B6 by auto
  qed
  show "stabilizer {\<alpha> g x} = {g \<cdot> h \<cdot> (inv g)|h. h \<in> stabilizer {x}}"
    using B0 B3 by auto
qed
    
end


locale group_automorphisms=group G "(\<cdot>)" e for G and law (infixl "\<cdot>" 70) and unit ("e")
begin
definition Aut where "Aut \<equiv> {\<phi>. group_isomorphism \<phi> G law G law e e}"
definition Inn where "Inn \<equiv> {(\<lambda>y \<in> G. x \<cdot> y \<cdot> (inv x))|x. x \<in> G}"

sublocale permutations:group "(set_isomorphisms G G)" "(compose G)" "(Algebrah11.Id G)"
  apply(rule group.intro)
  apply (metis group.axioms(1) composition_monoid monoid.group_of_units transformations_notation.set_iso_unital2)
  by (metis group.axioms(2) composition_monoid monoid.group_of_units transformations_notation.set_iso_unital2)


lemma group_iso_sub_set_iso:"group_isomorphism \<phi> G law G law e e \<Longrightarrow> \<phi> \<in> set_isomorphisms G G"
  by (simp add: group_isomorphism.in_set_iso)

  

lemma permuation_inv_eq_inv:
  assumes A0:"\<sigma> \<in> set_isomorphisms G G"
  defines "\<tau> \<equiv> permutations.inv \<sigma>"
  shows "\<tau>  = rinv \<sigma> G G" and 
        "\<tau> \<in> set_isomorphisms G G" 
proof-
  obtain B0:"compose G (rinv \<sigma> G G) \<sigma> = Id G"
    by (simp add: assms inv_rinv2 set_isomorphismE2)
  obtain B1:"compose G \<sigma> (rinv \<sigma> G G) = Id G"
    by (simp add: assms inv_rinv3 set_isomorphismE2)
  have B2:"rinv \<sigma> G G \<in> set_isomorphisms G G"
    by (meson assms bij_betw_hom_rev bij_betw_rinv_into set_isomorphismE2 set_isomorphism_memI2)
  then show B3:"\<tau>  = rinv \<sigma> G G"
    using permutations.inverse_unique B0 A0 permutations.inv_eq \<tau>_def by blast
  then show B4:"\<tau> \<in> set_isomorphisms G G"
    using B2 by force
qed


lemma Aut_sub_bij:"Aut \<subseteq> set_isomorphisms G G"
proof
  fix \<phi> assume A0:"\<phi> \<in> Aut"
  then obtain  B1:"group_isomorphism \<phi> G law G law e e"
    unfolding Aut_def by auto
  then obtain "set_isomorphism \<phi> G G"
    by (simp add: group_isomorphism_def)
  then show "\<phi> \<in> set_isomorphisms G G"
    by (metis set_isomorphismI1)
qed

lemma Aut_comp_hom:
  assumes A0:"a \<in>Aut" and A1:"b \<in> Aut"
  defines "c \<equiv> compose G a b"
  shows "c \<in> set_morphisms G G" and
        "set_isomorphism c G G" and
        "\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> c  (x \<cdot> y) = (c x) \<cdot> (c y)" and
        "group_isomorphism c G law G law e e" and
        "c\<in> Aut"
proof-
  obtain B1:"group_isomorphism a G law G law e e" and
         B3:"group_isomorphism b G law G law e e" 
    using A0 A1 unfolding Aut_def by auto  
  then obtain B4:"set_isomorphism a G G" and B5:"set_isomorphism b G G"
    by (simp add: group_isomorphism_def)
  then obtain B0:"a \<in>  set_morphisms G G" and B2:"b \<in> set_morphisms G G"
    using set_isomorphism_def set_morphism_iff by blast
  have B6:"compose G a b \<in> set_morphisms G G"
    using B0 B2 hom2 by blast 
  have B7:"set_isomorphism (compose G a b ) G G"
      apply(rule set_isomorphism.intro)
     apply (simp add: B6 set_morphismI1)
    apply(rule iso_locale.intro)
    by (meson A0 A1 Aut_sub_bij bij_compose in_mono set_isomorphismE2)
  show  P0:"c \<in> set_morphisms G G"
    by (simp add: B6 c_def)
  show  P1:"set_isomorphism c G G"
    by (simp add: B7 c_def) 
  show P2:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> c  (x \<cdot> y) = (c x) \<cdot> (c y)"
  proof-
    fix x y assume A2:"x \<in> G" and A3:"y \<in> G"
    have "c  (x \<cdot> y) = compose G a b (x \<cdot> y)"
      by (simp add: c_def)
    also have "... = a (b (x \<cdot> y))"
      by (simp add: A2 A3 compose_eq opposite.closed)
    also have "... = a ((b x) \<cdot> (b y))"
      using A2 A3 B3 group_isomorphism.cmp by fastforce
    also have "... = (a (b x)) \<cdot> (a (b y))"
      by (meson A2 A3 B1 B2 group_isomorphism.cmp hom9)
    also have "... =  compose G a b x \<cdot> compose G a b y"
      by (simp add: A2 A3 compose_eq)
    also have "... = (c x)\<cdot>(c y)"
      by (simp add: c_def)
    finally show "c  (x \<cdot> y) = (c x) \<cdot> (c y)"
      by simp
  qed
  show P3:"group_isomorphism c G (\<cdot>) G (\<cdot>) e e"
    apply(rule group_isomorphism.intro)
    apply (simp add: P1)
    apply (simp add: group_axioms)
    apply (simp add: group_axioms)
    apply(rule group_isomorphism_axioms.intro)
    using P2 by auto
  show "c \<in> Aut"
    unfolding Aut_def using P3 by auto
qed

lemma Aut_comp_closed:"\<And>a b. \<lbrakk>a \<in> Aut;b \<in> Aut\<rbrakk> \<Longrightarrow> compose G a b \<in> Aut"
  by (simp add: Aut_comp_hom(5))

lemma Aut_contains_id:"Id G \<in> Aut"
proof-
  have B0:"group_isomorphism (Id G) G law G law e e"
    apply(unfold_locales)
    apply simp
    apply simp
    apply (simp add: bij_betwI')
    by (simp add: opposite.closed)
  then show "Id G \<in> Aut"
    unfolding Aut_def by simp
qed


lemma inv_group_hom:
  assumes A0:"\<sigma> \<in>Aut"
  defines "\<tau> \<equiv> permutations.inv \<sigma>"
  shows "group_isomorphism \<tau>  G law G law e e"
proof-
  have B0:"\<tau>  = rinv \<sigma> G G"
    using A0 Aut_sub_bij \<tau>_def permuation_inv_eq_inv(1) by blast
  have B1:"group_isomorphism \<sigma>  G law G law e e"
    using A0 unfolding Aut_def by simp
  have B2:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> \<tau>  (x \<cdot> y) = (\<tau> x) \<cdot> (\<tau> y)"
  proof-
    fix x y assume A2:"x \<in> G" and A3:"y \<in> G"
    then obtain B3:"\<tau> x \<in> G" and B4:"\<tau> y \<in> G"
      by (metis A0 Aut_sub_bij B0 bij_betw_hom_rev hom9 set_isomorphismE2 subsetD)
    then obtain B5:"(\<tau> x) \<cdot> (\<tau> y) \<in> G"
      by (simp add: opposite.closed)
    have "\<sigma> ((\<tau> x) \<cdot> (\<tau> y)) = (\<sigma> (\<tau> x)) \<cdot> (\<sigma> (\<tau> y)) "
      by (meson B1 B3 B4 group_isomorphism.cmp)
    also have "... = x \<cdot> y"
      by (metis A0 A2 A3 Aut_sub_bij B0 compose_eq id2 inv_rinv3 set_isomorphismE2 subsetD)
    finally have "\<sigma> ((\<tau> x) \<cdot> (\<tau> y))  = x \<cdot> y"
      by simp
    then have "\<tau> (\<sigma> ((\<tau> x) \<cdot> (\<tau> y))) = \<tau> (x \<cdot> y)"
      by auto
    then have "(\<tau> x) \<cdot> (\<tau> y) =  \<tau> (x \<cdot> y)"
      by (metis A0 Aut_sub_bij B5 \<tau>_def compose_eq group.l_inv_simp id2 permutations.group_axioms subsetD)
    then show " \<tau>  (x \<cdot> y) = (\<tau> x) \<cdot> (\<tau> y)"
      by simp
  qed
  show "group_isomorphism \<tau> G law G law e e"
    apply(rule group_isomorphism.intro)
    apply (metis B0 B1 bij_betw_hom_rev bij_betw_rinv_into group_isomorphism.in_set_iso set_isoI1 set_isomorphismE2)
    apply (simp add: group_axioms)
      apply (simp add: group_axioms)
    apply(rule group_isomorphism_axioms.intro)
    by (simp add: B2)
qed


lemma Aut_inv_closed:"a \<in> Aut \<Longrightarrow> permutations.inv  a \<in> Aut"
  using Aut_def inv_group_hom by blast 






lemma Aut_subgroup:
  "subgroup Aut (set_isomorphisms G G) (compose G) (Id G)" 
  apply(rule subgroup.intro)
  apply (metis composition_monoid monoid.group_of_units transformations_notation.set_iso_unital2)
  apply(rule subgroup_axioms.intro)
  apply (simp add: Aut_sub_bij)
    apply (simp add: Aut_comp_closed)
  apply(simp add:Aut_contains_id)
  using Aut_inv_closed by auto



end

thm_deps group_automorphisms.Aut_subgroup
thm_deps group_automorphisms.Aut_comp_hom
thm_deps group_automorphisms.inv_group_hom
thm_deps group_automorphisms.permuation_inv_eq_inv


thm_deps group_automorphisms.permuation_inv_eq_inv
thm_deps monoid_congruence_vimage.epi_then_iso
thm_deps monoid_epimorphism_congruence_image.epi_then_iso
print_locale monoid_epimorphism_congruence_image
thm_deps symmetric_group.inv_set_inv
thm_deps group_operating_on_set.Imsub
end
