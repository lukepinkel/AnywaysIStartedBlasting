theory Algebra12
  imports Main PosetsRel6
begin

declare [[show_consts, show_results, show_types,function_internals,coherent_trace]]
declare [[show_abbrevs=true]]

hide_const map dom partition monoid group inverse
hide_const PosetsRel6.sym PosetsRel6.trans 
no_notation power (infixr "^" 80)
no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)
nitpick_params[show_consts=true,verbose=true]


section \<open>Set Morphisms\<close>

definition maps_to::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "maps_to A B = {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B}"

definition maps_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "maps_on A = {f. \<forall>x. x \<notin> A \<longrightarrow> f x = undefined}" 

definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b" where
  "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"

syntax "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
translations "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"

definition compose::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where
 "compose A g f = (\<lambda>x\<in>A. g (f x))"

definition preimage::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'a set" where
  "preimage f A B \<equiv> {x \<in> A. f x \<in> B}"

abbreviation Id where 
  "Id X \<equiv> (\<lambda>x \<in> X. x)"

abbreviation surj where 
  "surj f A B \<equiv> f`A=B"

abbreviation bij where
  "bij f A B \<equiv> bij_betw f A B"

definition inv::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'a"
  where "inv f A B \<equiv> restrict (inv_into A f) B"

definition set_morphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "set_morphisms A B \<equiv> maps_to A B \<inter> maps_on A"

definition set_epimorphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set "
  where "set_epimorphisms A B \<equiv> {f \<in> set_morphisms A B. surj f A B}"

definition set_monomorphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" 
  where "set_monomorphisms A B \<equiv> {f \<in> set_morphisms A B. inj_on f A}"

definition set_isomorphisms::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  
  where "set_isomorphisms A B \<equiv> {f \<in> set_morphisms A B. bij_betw f A B}"

definition is_eqrel::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" 
  where "is_eqrel X R \<equiv> refl_on X R \<and> sym R \<and> trans_on UNIV R"

definition quotient::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set" (infixl "'/" 75) 
  where "quotient X R \<equiv> (\<Union>x \<in> X. {R``{x}})"

definition eqr_comp::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  where "eqr_comp X R f \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. (x, y) \<in> R \<longrightarrow> f x = f y)"

definition ker_pair::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set" 
  where "ker_pair X f \<equiv> {(x, y) \<in> X \<times> X. f x = f y}"

definition qproj::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "qproj X R  \<equiv> (\<lambda>x \<in> X. {y \<in> X. (x, y) \<in> R})"

definition qsect::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a" 
  where "qsect X R  \<equiv> inv (qproj X R) X (X/R)"

definition qmap::"'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "qmap X R f \<equiv> compose (X/R) f (qsect X R)"

definition magma_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" 
  where "magma_pred X f \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. f x y \<in> X)"

definition assoc_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" 
  where "assoc_pred X f \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. \<forall>z \<in> X. f (f x y) z = f x (f y z))"

definition lid_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" 
  where "lid_pred X f e \<equiv> (\<forall>x \<in> X. f e x = x)"

definition rid_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" 
  where "rid_pred X f e \<equiv> (\<forall>x \<in> X. f x e = x)"

definition id_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" 
  where "id_pred X f e \<equiv> (\<forall>x \<in> X. f x e = x \<and> f e x = x)"

definition op_law_pred :: "'d \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where "op_law_pred X f \<equiv> (\<lambda>x. \<lambda>y. f y x)"

definition commutes_pred::"'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool"
  where  "commutes_pred X f A B \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B. f a  b = f b  a)"

definition centralizer:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "centralizer X f E \<equiv> {x \<in> X. \<forall>y \<in> E. commutes_pred X f {x} {y}}"

definition l_cancel_pred:: "'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> bool"
  where "l_cancel_pred X f a \<equiv>(\<forall>x \<in> X. \<forall>y \<in> X.  f a x = f a y \<longrightarrow> x = y)"

definition r_cancel_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> bool"
  where "r_cancel_pred X f a \<equiv>(\<forall>x \<in> X. \<forall>y \<in> X.  f x a = f y a \<longrightarrow> x = y)"

definition cancel_pred :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where"cancel_pred X f  a \<equiv>(\<forall>x \<in> X. \<forall>y \<in> X.  f x a = f y a \<longrightarrow> x = y) \<and> (\<forall>x \<in> X. \<forall>y \<in> X.  f a x = f a y \<longrightarrow> x = y)"

definition l_trans :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" 
  where "l_trans X f \<equiv> (\<lambda>a \<in> X. \<lambda>x \<in> X. f a  x)"

definition r_trans :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" 
  where "r_trans X f \<equiv> (\<lambda>a \<in> X. \<lambda>x \<in> X. f x a)"

definition r_coset::"'b \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c set \<Rightarrow> 'd \<Rightarrow> 'a set"
  where "r_coset X f H a = (\<Union>h\<in>H. {f h  a})"

definition l_coset::"'b \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'd set \<Rightarrow> 'a set" 
  where "l_coset X f a H = (\<Union>h\<in>H. {f a h})"

definition r_cosets::  "('a \<Rightarrow> 'b \<Rightarrow> 'c) set \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> ('a set \<Rightarrow> 'b \<Rightarrow> 'c set) set"
  where "r_cosets X f H = (\<Union>a\<in>X. {r_coset H a})"

definition l_cosets :: "'d set  \<Rightarrow> 'e \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b set \<Rightarrow> 'c set) set"
  where "l_cosets X f H = (\<Union>a\<in>X. {l_coset a H})"

definition set_prod::"'b \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'a) \<Rightarrow> 'c set \<Rightarrow> 'd set \<Rightarrow> 'a set"
  where "set_prod X f H K = (\<Union>h\<in>H. \<Union>k\<in>K. {f h  k})"

definition l_cong::"'a set\<Rightarrow>('a\<Rightarrow>'b\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where
  "l_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f a x, f a y) \<in> R)"

definition r_cong::"'a set\<Rightarrow>('b\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('b\<times>'b) set \<Rightarrow> bool" where
  "r_cong X f R \<equiv> (\<forall>a \<in> X. \<forall>(x,y)\<in>R.  (f x a, f y a) \<in> R)"

definition cong::"'a set\<Rightarrow>('a\<Rightarrow>'a\<Rightarrow>'a)\<Rightarrow>('a\<times>'a) set \<Rightarrow> bool" where
  "cong X f R \<equiv> (\<forall>(x1, x2) \<in> R. \<forall>(y1, y2) \<in> R.  (f x1 y1, f x2 y2) \<in> R)"

definition quotient_law:: "'a set  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where  "quotient_law X f R \<equiv> (\<lambda>t \<in> X/R. \<lambda>s \<in> X/R. (qproj X R) (f (qsect X R t) ( qsect X R s)))"

definition is_inv_pred:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_inv_pred X f e u \<equiv> (\<exists>v \<in> X. f u v = e \<and> f v  u = e)"

definition inv_pred::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" 
  where "inv_pred X f e i \<equiv> (\<forall>x. x \<in> X \<longrightarrow> i x \<in> X \<and> f (i x) x = e \<and> f x (i x) = e )"

definition op_inv :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a"
  where "op_inv X f e = (\<lambda>u \<in> X. THE v. v \<in>X \<and> f u v = e \<and> f v u = e)"

definition set_inv ::  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'a set"  where
  "set_inv X f e H = (\<Union>h\<in>H. {op_inv X f e h})"

definition Units :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set"  where
  "Units X f e = {u \<in> X. is_inv_pred X f e u}"

definition magma_hom_pred::"'a set\<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" where 
  "magma_hom_pred X f Y g \<phi> \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. \<phi> (f x1 x2) =  g (\<phi> x1) (\<phi> x2))"

definition magma_stable :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "magma_stable X f A \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A. f x y \<in> A) \<and> (A \<subseteq> X)"

definition magma_lattice::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set set" where
  "magma_lattice X f \<equiv> {M. magma_stable X f M}"

lemma maps_toI1:"(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in>maps_to A B"
  by (simp add: maps_to_def)

lemma maps_toI2:"f`A \<subseteq> B \<Longrightarrow> f \<in>maps_to A B"
  by (simp add: image_subset_iff maps_toI1)

lemma maps_toD1:"f \<in> maps_to A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B"
  by (simp add: maps_to_def)

lemma maps_toD2:"f \<in> maps_to A B \<Longrightarrow>f`A \<subseteq> B"
  by (simp add: image_subsetI maps_toD1)

lemma maps_toE1: "f \<in> maps_to A B \<Longrightarrow> (f x \<in> B \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q" (*[elim] *)
  by (auto simp: maps_to_def)

lemma maps_to_comp:"\<lbrakk>f \<in> maps_to A B; g \<in> maps_to B C\<rbrakk> \<Longrightarrow> compose A g f \<in> maps_to A C"
  by (simp add: compose_def maps_to_def restrict_def)

lemma maps_to_assc:"f \<in> maps_to A B \<Longrightarrow> compose A h (compose A g f) = compose A (compose B h g) f"
  unfolding compose_def restrict_def maps_to_def by fastforce

lemma comp_eval:"x \<in> A \<Longrightarrow> compose A g f x = g (f x)"
  by (simp add: compose_def restrict_def)

lemma maps_toI3:"(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> restrict f A \<in> maps_to A B"
  by (simp add: maps_toI1 restrict_def)

lemma restrict_eq1[simp]:"restrict f A x = (if x \<in> A then f x else undefined)"
  by (simp add: restrict_def)

lemma restrict_eq2:"x \<in> A \<Longrightarrow> restrict f A x = f x"
  by simp

lemma restrict_eq3:"(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> restrict f A = restrict g A"
  by (simp add: ext)

lemma restrict_injI1:"inj_on (restrict f A) A \<Longrightarrow> inj_on f A"
  by (simp add: inj_on_def restrict_def)

lemma restrict_injD1:" inj_on f A \<Longrightarrow> inj_on (restrict f A) A "
  by (simp add: inj_on_def restrict_def)

lemma restrict_inj_iff: "A \<subseteq> B \<Longrightarrow> inj_on (restrict f B) A \<longleftrightarrow> inj_on f A"
  by (metis inj_on_cong restrict_def subset_iff)

lemma id_comp1: "f \<in> maps_to A B \<Longrightarrow> f \<in> maps_on A \<Longrightarrow> compose A (Id B) f = f"
  by (auto simp add: compose_def maps_on_def maps_to_def)

lemma id_comp2: "f \<in> maps_to A B \<Longrightarrow> f \<in> maps_on A \<Longrightarrow>x \<in> A \<Longrightarrow> compose A (Id B) f x = f x"
  by (auto simp add: compose_def maps_on_def maps_to_def)

lemma id_comp3: "g \<in> maps_to A B \<Longrightarrow> g \<in> maps_on A \<Longrightarrow> compose A g (Id A) = g"
  by (auto simp add: compose_def maps_on_def maps_to_def)

lemma id_comp4: "g \<in> maps_to A B \<Longrightarrow> g \<in> maps_on A \<Longrightarrow>x \<in> A \<Longrightarrow>compose A g (Id A) x = g x"
  by (auto simp add: compose_def maps_on_def maps_to_def)

lemma im_restrict[simp]: "(restrict f A) ` A = f ` A"
  by (auto simp add: restrict_def)

lemma maps_onI1:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> maps_on A"
  by (simp add: maps_on_def)

lemma maps_onD1:"f \<in> maps_on A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined"
  by (simp add: maps_on_def)

lemma maps_onI2[simp]: "restrict f A \<in> maps_on A"  (*[simp] *)
  by (simp add: restrict_def maps_on_def) 

lemma maps_onI3[simp]: "compose A f g \<in> maps_on A"  (*[simp] *)
  by (simp add: compose_def)

lemma maps_on_eqI:"\<lbrakk>f \<in> maps_on A; g \<in> maps_on A; (\<And>x. x \<in> A \<Longrightarrow> f x = g x)\<rbrakk> \<Longrightarrow> f = g"
  unfolding maps_on_def by fastforce

lemma inv_identity[simp]: "inv (Id A) A A = Id A"
  unfolding inv_def restrict_def inv_into_def by force

lemma sec_maps_to:"surj f A B \<Longrightarrow> inv f A B \<in> maps_to B A"
  unfolding inv_def maps_to_def by (simp add: inv_into_into)

lemma ret_maps_to:"inj_on f A  \<Longrightarrow> inv f A (f`A) \<in> maps_to (f`A) A"
  unfolding inv_def maps_to_def by (simp add: inv_into_into)

lemma bij_left_inv1:"bij_betw f A B \<Longrightarrow> compose A (inv f A B) f = Id A"
  unfolding compose_def inv_def bij_betw_def by auto

lemma bij_left_inv2:"bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow>  (inv f A B) (f x) = x"
  unfolding compose_def inv_def bij_betw_def by auto

lemma left_inv1:"inj_on f A \<Longrightarrow> f \<in> maps_to A B \<Longrightarrow> compose A (inv f A B) f = Id A"
  unfolding compose_def inv_def bij_betw_def maps_to_def by auto

lemma left_inv2:"inj_on f A \<Longrightarrow> f \<in> maps_to A B \<Longrightarrow> x \<in> A \<Longrightarrow>  (inv f A B) (f x) = x"
  unfolding compose_def inv_def bij_betw_def maps_to_def by auto

lemma right_inv1:"surj f A B \<Longrightarrow> y \<in> B \<Longrightarrow> f (inv f A B y) = y "
  by (simp add: inv_def f_inv_into_f)

lemma right_inv2:"surj f A B \<Longrightarrow> compose B f (inv f A B ) = Id B "
  unfolding compose_def  restrict_def using right_inv1[of f A B] by(auto) 

lemma right_inv3:"y \<in> f`A \<Longrightarrow> f (inv f A (f`A) y) = y"
  by (simp add: right_inv1)

lemma retract_injI0:"\<lbrakk>compose A (inv f A B) f = Id A; x \<in> A;y \<in> A; f x =f y\<rbrakk> \<Longrightarrow> x =y"
  by (metis  comp_eval restrict_eq2)

lemma retract_injI:"compose A (inv f A B) f = Id A\<Longrightarrow> inj_on f A" 
  using inj_on_def retract_injI0 by fastforce

lemma retract_cancel[simp]:"inj_on f A \<Longrightarrow> f \<in> maps_to A B \<Longrightarrow> compose A g (compose A (inv f A B) f) = restrict g A "
  unfolding compose_def  using left_inv2 by fastforce 

lemma retract_surj:"inj_on f A \<Longrightarrow> surj (inv f A (f`A)) (f`A) A"
  by (simp add: inv_def)

lemma section_injI0:"\<lbrakk>f \<in> maps_to A B;compose B f (inv f A B) = Id B;x \<in> f`A; y \<in> f`A;inv f A B x = inv f A B y \<rbrakk> \<Longrightarrow> x =y  "
  unfolding restrict_def inv_def  by (meson in_mono inv_into_injective maps_toD2)

lemma section_injI1:"\<lbrakk>f \<in> maps_to A B;compose B f (inv f A B) = Id B\<rbrakk> \<Longrightarrow> inj_on (inv f A B) (f`A)"
  by (simp add: inj_on_def section_injI0)

lemma bij_inv: "bij f A B \<Longrightarrow> bij (inv f A B) B A"
  unfolding inv_def bij_betw_def using inj_on_def by fastforce

lemma maps_onD2:"f \<in> maps_on A \<Longrightarrow> restrict f A = f"
  unfolding restrict_def maps_on_def by fastforce 

lemma set_morphismsI1:"f \<in> maps_on A \<Longrightarrow> f \<in> maps_to A B \<Longrightarrow> f \<in> set_morphisms A B"
  unfolding set_morphisms_def by simp

lemma set_morphismsI2:"\<lbrakk>(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B); (\<And>x. x \<notin> A \<Longrightarrow> f x = undefined)\<rbrakk> \<Longrightarrow> f \<in> set_morphisms A B "
  unfolding set_morphisms_def maps_to_def maps_on_def by simp

lemma set_morphismsD1:"f \<in> set_morphisms A B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" 
  by (simp add:set_morphisms_def maps_on_def)

lemma set_morphismsD2:"f \<in> set_morphisms A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B"
  by (simp add:set_morphisms_def maps_to_def)

lemma set_morphismsE1[elim]: "f \<in> set_morphisms A B \<Longrightarrow> (f x \<in> B \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"
  using set_morphismsD2 by fastforce

lemma set_morphisms_im1:"f \<in> set_morphisms A B \<Longrightarrow> b \<in> f`A \<Longrightarrow> b \<in> B "
  by blast

lemma set_morphisms_im2:"f \<in> set_morphisms A B \<Longrightarrow> b \<in> f`A \<Longrightarrow> (\<exists>a \<in> A. b = f a) "
  by blast

lemma set_morphismsE2[elim]:
  assumes "f \<in> set_morphisms A B"
  obtains "x \<in> A" and "f x \<in> B" | "x \<notin> A" and "f x = undefined"
  using assms set_morphismsD1 by force

lemma set_morphisms_rest[simp]:"f \<in> set_morphisms A B \<Longrightarrow> restrict f A = f"
  by (simp add: maps_onD2 set_morphisms_def)

lemma set_epiI1:"f \<in> set_morphisms A B \<Longrightarrow> surj f A B \<Longrightarrow> f \<in> set_epimorphisms A B"
  by (simp add:set_epimorphisms_def) 

lemma set_epiD1:"f \<in> set_epimorphisms A B \<Longrightarrow> f \<in> set_morphisms A B \<and> surj f A B"
  by (simp add:set_epimorphisms_def) 

lemma set_epi_sub:"set_epimorphisms A B \<subseteq> set_morphisms A B"
  by (simp add:set_epimorphisms_def) 

lemma set_monoI1:"f \<in> set_morphisms A B \<Longrightarrow> inj_on f A \<Longrightarrow> f \<in> set_monomorphisms A B"
  by (simp add:set_monomorphisms_def) 

lemma set_monoD2:"f \<in> set_monomorphisms A B \<Longrightarrow> f \<in> set_morphisms A B \<and> inj_on f A"
  by (simp add:set_monomorphisms_def) 

lemma set_mono_sub:"set_monomorphisms A B \<subseteq> set_morphisms A B"
  by (simp add:set_monomorphisms_def) 

lemma mon_inv1:"f \<in> set_monomorphisms A B \<Longrightarrow> compose A (inv f A B) f = Id A"
  unfolding set_monomorphisms_def set_morphisms_def using left_inv1 by blast

lemma mon_inv2:"f \<in> set_monomorphisms A B \<Longrightarrow> x \<in> A \<Longrightarrow>  (inv f A B) (f x) = x"
  unfolding set_monomorphisms_def set_morphisms_def using left_inv2  by fastforce

lemma epi_inv1:"f \<in> set_epimorphisms A B \<Longrightarrow> y \<in> B \<Longrightarrow>  compose B f (inv f A B) y = y"
  unfolding set_monomorphisms_def set_morphisms_def by (simp add: comp_eval right_inv1 set_epiD1) 

lemma epi_inv2:"f \<in> set_epimorphisms A B \<Longrightarrow> compose B f (inv f A B) = Id B"
  unfolding set_monomorphisms_def set_morphisms_def by (simp add: right_inv2 set_epiD1) 

lemma preimage_eq[simp]:"a \<in> preimage f A B \<longleftrightarrow> a \<in> A \<and> f a \<in> B " 
  unfolding preimage_def by blast

lemma preimage_singleton_eq: "a \<in> preimage f A {b} \<longleftrightarrow> a \<in> A \<and> f a = b"
  by simp

lemma preimageI[intro]: "a \<in> A \<Longrightarrow> f a = b \<Longrightarrow> b \<in> B \<Longrightarrow> a \<in> preimage f A B"
  unfolding preimage_def by blast

lemma preimageE[elim!]: "a \<in> preimage f A B \<Longrightarrow> (\<And>x. a \<in> A \<Longrightarrow> f a = x \<Longrightarrow> x \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding preimage_def by blast

lemma preimageD1:"a \<in> preimage f A B \<Longrightarrow> f a \<in> B"
  unfolding preimage_def by fast

lemma preimageD2:"a \<in> preimage f A B \<Longrightarrow>a \<in> A"
  unfolding preimage_def by fast

lemma preimage_empty1[simp]: "preimage f A {} = {}"
  by blast

lemma preimage_empty2[simp]: "preimage f {} B = {}"
  by blast

lemma preimage_iso: "A \<subseteq> B \<Longrightarrow> preimage f X A  \<subseteq> preimage f X B"
  by blast

lemma image_preimage_subset: "image f (preimage f X A) \<subseteq> A"
  by blast

lemma preimage_image_superset:"A \<subseteq> X \<Longrightarrow> A \<subseteq> preimage f X (image f A)"
  by blast

lemma image_preimage_eq [simp]:"image f (preimage f X A) = A \<inter> (image f X)"
  by blast


lemma mamga_stableI:
  "A \<subseteq> X \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> f x y \<in> A) \<Longrightarrow> magma_stable X f A" 
  by (simp add: magma_stable_def)

lemma magma_stableE1:
  "magma_stable X f A \<Longrightarrow> A \<subseteq> X" 
  by (simp add: magma_stable_def)

lemma magma_stableE2:
  "magma_stable X f A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x y \<in> A" 
  by (simp add:magma_stable_def)

lemma magma_stable_int_closed:
  "(\<And>A. A \<in> \<A> \<Longrightarrow> magma_stable X f A) \<Longrightarrow> \<A> \<noteq> {} \<Longrightarrow> magma_stable X f (\<Inter>\<A>)"
  unfolding magma_stable_def by(blast)

lemma magma_lattice_sub:"magma_lattice X f \<subseteq> Pow X"
  unfolding magma_lattice_def magma_stable_def by(auto)

lemma magma_lattice_top:"magma_stable X f X \<Longrightarrow> X \<in> magma_lattice X f"
  unfolding magma_lattice_def magma_stable_def by(auto)

lemma magma_latticeI:"\<lbrakk>A \<subseteq> X; magma_stable X f A\<rbrakk> \<Longrightarrow> A \<in> magma_lattice X f"
  by (simp add: magma_lattice_def)

lemma magma_latticeD1:"A \<in> magma_lattice X f \<Longrightarrow> A \<subseteq> X"
  by (simp add: magma_lattice_def magma_stableE1)

lemma magma_latticeD2:"A \<in> magma_lattice X f \<Longrightarrow> magma_stable X f A"
  by (simp add: magma_lattice_def magma_stableE1)

lemma submagmas_clr:
  assumes A0:"magma_stable X f X"
  shows "clr (pwr X) (Pow X) (magma_lattice X f)"
proof(rule moore_clI3)
  show "magma_lattice X f \<subseteq> Pow X" 
    using magma_lattice_sub by auto
  show "X \<in> magma_lattice X f"
    using A0 magma_lattice_top by auto
  show "\<And>E. E \<subseteq> magma_lattice X f \<Longrightarrow> E \<noteq> {} \<Longrightarrow> \<Inter> E \<in> magma_lattice X f"
    by (simp add: magma_lattice_def magma_stable_int_closed subset_iff)
qed


locale magma=
  fixes X::"'a set" and f::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) 
  assumes closed:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> X" 
begin

inductive_set magma_generated::"'a set \<Rightarrow> 'a set" for A where
  iso:"a \<in> A \<Longrightarrow> a \<in> magma_generated A"
 |opc:"a \<in> magma_generated A \<Longrightarrow> b \<in> magma_generated A \<Longrightarrow> a\<cdot>b \<in> magma_generated A"

lemma generate_into: "a \<in> magma_generated (X \<inter> A) \<Longrightarrow> a \<in> X"  
  by (induction rule: magma_generated.induct, simp_all add:closed)  

definition cl::"'a set \<Rightarrow> 'a set" 
  where "cl S = magma_generated (X \<inter> S)"

lemma cl_magma_closed:"\<lbrakk>a \<in> cl S; b \<in> cl S\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> cl S"
  by (simp add: cl_def magma_generated.opc)

lemma cl_magma_ext:"S \<subseteq> X \<Longrightarrow>  S \<subseteq> cl S"
  using cl_def magma_generated.iso by auto

lemma cl_magma_sub:"cl H \<subseteq> X" 
  using cl_def generate_into by auto

lemma cl_magma_iso:"A \<subseteq> B \<Longrightarrow> cl A \<subseteq> cl B"
proof-
  assume A0:"A \<subseteq> B"  
  show "cl A \<subseteq> cl B"
  proof
    fix x assume "x \<in> cl A"
    then show "x \<in> cl B" unfolding cl_def
     apply(induction rule: magma_generated.induct)
      using A0 magma_generated.iso apply auto[1]
      using magma_generated.opc by auto
  qed
qed


lemma cl_magma_stable_ub:"\<lbrakk>A \<subseteq> B; magma_stable X f B\<rbrakk> \<Longrightarrow> cl A \<subseteq> B"
  by (metis Int_commute cl_def cl_magma_iso dual_order.trans magma.cl_def magma.cl_magma_sub magma_def magma_stableE2) 

lemma cl_magma_idempotent:
  assumes A0:"A \<subseteq> X" 
  shows "cl A = cl (cl A)"
  by (simp add: cl_magma_closed cl_magma_ext cl_magma_stable_ub cl_magma_sub magma_stable_def subset_antisym)

lemma cl_magma_idempotent2:
  assumes A0:"magma_stable X f A" 
  shows "cl A = A"
  by (meson assms cl_magma_ext cl_magma_stable_ub dual_order.refl magma_stableE1 subset_antisym)

lemma cl_magma_moore0:
  assumes A0:"A \<subseteq> X" 
  shows "cl A = \<Inter>{C. magma_stable X f C \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    by (simp add: le_Inf_iff magma.cl_magma_stable_ub magma_axioms)
next
  show "?RHS \<subseteq> ?LHS"
    by (simp add: Inf_lower assms cl_magma_closed cl_magma_ext cl_magma_sub mamga_stableI)
qed


lemma generated_stable:"magma_stable X f (cl A)"
  by (simp add: cl_magma_closed cl_magma_sub magma_stable_def)  

end

lemma magmaI:"magma_stable X f X \<Longrightarrow> magma X f"
  by(unfold_locales;simp add:magma_stable_def)

lemma magmaE:"magma X f \<Longrightarrow> magma_stable X f X"
  by (simp add: magma_def magma_stable_def)

lemma magma_iff:"magma X f \<longleftrightarrow> magma_stable X f X"
  using magmaE magmaI by blast

lemma magma_hom_predD:"\<lbrakk>magma_hom_pred X f Y g \<phi>; x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> \<phi> (f x1 x2) =  g (\<phi> x1) (\<phi> x2)"
  by (simp add: magma_hom_pred_def)

lemma magma_hom_predI:"(\<And>x1 x2. \<lbrakk>x1 \<in> X;x2 \<in> X\<rbrakk> \<Longrightarrow> \<phi> (f x1 x2) =  g (\<phi> x1) (\<phi> x2)) \<Longrightarrow> magma_hom_pred X f Y g \<phi>"
  by (simp add: magma_hom_pred_def)

locale magma_homomorphism=dom:magma X "(\<cdot>)"+cod:magma Y "(\<star>)" for
    X::"'a set" and
    dom_law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and 
    Y::"'b set" and
    cod_law::"'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<star>" 70) and
    \<phi>::"'a \<Rightarrow> 'b" +
  assumes set_morph:"\<phi> \<in> set_morphisms X Y" and hom:"magma_hom_pred X dom_law Y cod_law \<phi>"
begin

lemma cmp:"\<lbrakk>x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> \<phi> (x \<cdot> y) = (\<phi> x) \<star> (\<phi> y)"
  by (meson hom magma_hom_predD)

lemma image_comp1:"\<lbrakk>magma_stable X (\<cdot>) A; a1 \<in> A;a2 \<in> A\<rbrakk> \<Longrightarrow> \<phi> (a1 \<cdot> a2) = (\<phi> a1) \<star> (\<phi> a2)"
  using cmp magma_stableE1 by blast

lemma imag_comp2:"magma_stable X (\<cdot>) A \<Longrightarrow> x \<in> \<phi> ` A \<Longrightarrow> y \<in> \<phi> ` A \<Longrightarrow> x \<star> y \<in> \<phi> ` A"
proof-
  fix x y assume A0:"magma_stable X (\<cdot>) A" and A1:"x \<in> \<phi> ` A" and A2:"y \<in> \<phi> `A" 
  then obtain a b where A3:"a \<in> A" and  A4:"b \<in> A" and A5:"x = \<phi> a" and A6:"y = \<phi> b"
    by blast
  then obtain A7:"A \<subseteq> X"
    using A0 unfolding magma_stable_def by blast
  then obtain A8:"x \<in> Y" and A9:"y \<in> Y" and A10:"a \<in> X" and A11:"b \<in> X"
    using A3 A4 A5 A6 set_morph by blast 
  obtain A12:"a\<cdot>b \<in> A" and A13:"a \<cdot> b \<in> X"
    using A0 A3 A4 unfolding magma_stable_def by auto
  then obtain A14:"\<phi> (a \<cdot>b) \<in> \<phi> `A" and A15: "\<phi> (a \<cdot> b) = (\<phi> a)\<star>(\<phi> b)"
    using A13 A10 A11 cmp[of a b] by blast
  then show "x \<star> y \<in> \<phi> ` A"
    using A5 A6 by auto
qed

lemma stable_image:
  assumes A0:"magma_stable X (\<cdot>) A"
  shows "magma_stable Y (\<star>) (\<phi>`A)"
proof-
  have B0:"\<phi>`A \<subseteq> Y"
    using assms magma_stableE1 set_morph by fastforce
  have B1:"\<And>x y. x \<in> \<phi>` A \<Longrightarrow> y \<in> \<phi> ` A \<Longrightarrow> x \<star> y \<in> \<phi> ` A"
    using A0 imag_comp2 by(auto)
  show ?thesis 
    using mamga_stableI B0 B1 by auto
qed


lemma magma_stable_vimage:"magma_stable Y (\<star>) B \<Longrightarrow>magma_stable X (\<cdot>) (preimage \<phi> X B)" 
proof-
  assume A0:"magma_stable Y (\<star>) B " 
  show "magma_stable X (\<cdot>) (preimage \<phi> X B)"
    apply(rule mamga_stableI,blast)
    by (metis A0 cmp dom.closed magma_stableE2 preimage_eq)
qed

end


lemma image_of_gen:
  fixes X::"'a set" and dom_law :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<cdot>\<close> 70)  and
        Y::"'b set" and cod_law :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl \<open>\<star>\<close> 70)  and 
        \<phi>::"'a \<Rightarrow> 'b" and A::"'a set"
  assumes A0:"magma_homomorphism X (\<cdot>) Y (\<star>) \<phi>" and A1:"A \<subseteq> X" 
  shows "\<phi>`(magma.cl X (\<cdot>) A) = magma.cl Y (\<star>) (\<phi>`A)"
proof-
  obtain A4:"magma X (\<cdot>)" and A5:"magma Y (\<star>)"
    using A0 magma_homomorphism_def by blast
  have B0:"\<phi>`A \<subseteq> \<phi>`(magma.cl X (\<cdot>) A)"
    by (simp add: A1 A4 image_mono magma.cl_magma_ext)
  have B1:"magma_stable Y (\<star>) (\<phi>`(magma.cl X (\<cdot>) A))"
    using A0 A4 magma.generated_stable magma_homomorphism.stable_image by blast
  then have B2:"magma.cl Y (\<star>) (\<phi>`A) \<subseteq> (\<phi>`(magma.cl X (\<cdot>) A))"
    by (simp add: A5 B0 magma.cl_magma_stable_ub)
  have B3:"magma_stable X (\<cdot>) (preimage \<phi> X (magma.cl Y (\<star>) (\<phi>`A)))"
    using A0 A5 magma.generated_stable magma_homomorphism.magma_stable_vimage by blast
  have B4:"A \<subseteq> (preimage \<phi> X (magma.cl Y (\<star>) (\<phi>`A)))"
    by (meson A1 A5 B0 B1 magma.cl_magma_ext magma_stable_def order.trans preimage_image_superset preimage_iso)
  have B5:"magma.cl X (\<cdot>) A \<subseteq> (preimage \<phi> X (magma.cl Y (\<star>) (\<phi>`A)))"
    using A4 B3 B4 magma.cl_magma_stable_ub by blast
  then have B6:"\<phi>`(magma.cl X (\<cdot>) A) \<subseteq> magma.cl Y (\<star>) (\<phi>`A)"
    by blast
  from B2 B6 show ?thesis
    by blast
qed
    



end