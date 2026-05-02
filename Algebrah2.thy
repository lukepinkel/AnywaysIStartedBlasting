theory Algebrah2
  imports Main
begin

declare [[show_consts, show_results, show_types]]
declare [[show_abbrevs=true]]

hide_const map
hide_const partition

hide_const monoid
hide_const group
hide_const inverse

no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)

definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
  where "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"

syntax
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
translations
  "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"


definition hom :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  where "hom A B \<equiv> {f. ((\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B))}"
lemma hom_memI:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> hom A B" unfolding hom_def by fast
lemma restrict_apply[simp]: "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)" by (simp add: restrict_def)
definition "compose"::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"  where "compose A g f = (\<lambda>x\<in>A. g (f x))"
definition Id where "Id X \<equiv> (\<lambda>x \<in> X. x)"
lemma id1[simp]:"Id X x = (if x \<in> X then x else undefined)" by (simp add:Id_def)
abbreviation comp where "comp X f g \<equiv> compose X f g"

lemma hom1:"hom {} Y = {\<lambda>x. undefined}"  by(auto simp add:hom_def) 
lemma hom2:"f \<in> hom A B \<Longrightarrow> g \<in> hom B C \<Longrightarrow> comp A g f \<in> hom A C" by(auto simp add:hom_def compose_def)
lemma hom3:"f \<in> hom A B \<Longrightarrow> comp A h (comp A g f) = comp A (comp B h g) f" by(auto simp add:hom_def fun_eq_iff compose_def)
lemma fun_eqI:"f \<in> hom A Y \<Longrightarrow> g \<in> hom A Z \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f = g" by(force simp add:fun_eq_iff hom_def)
lemma hom5:"f \<in> hom A B \<Longrightarrow> comp A (Id B) f = f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom6:"f \<in> hom A B  \<Longrightarrow> compose A f (Id A) = f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom7:"(Id A) \<in> hom A A" unfolding hom_def by(auto)
lemma hom8:"A \<subseteq> B \<Longrightarrow> (Id A) \<in> hom A B"  using hom_def by fastforce 
lemma hom9:"f \<in> hom A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B" unfolding hom_def by simp
lemma hom10:"f \<in> hom A B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined" unfolding hom_def by simp
lemma hom11:"f \<in> hom A B \<Longrightarrow> g \<in> hom A C \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = g x" unfolding hom_def by(auto)
lemma hom_agree:"f \<in> hom A B \<Longrightarrow> g \<in> hom A C \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<And>x. f x = g x) " proof- assume a0:"f \<in> hom A B" and a1:"g \<in> hom A C" and agree:"\<And>x. x \<in> A \<Longrightarrow> f x = g x" show "\<And>x. f x = g x"   proof-   fix x  show "f x = g x"  proof(cases "x \<in> A")  case True then show ?thesis  using agree by blast  next  case False then show ?thesis   using a0 a1 hom11[of f A B g C x] by auto  qed qed qed
lemma hom_agree2:"f \<in> hom A B \<Longrightarrow> g \<in> hom A B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow>(\<And>x. f x = g x)" using hom_agree[of f A B g] by(auto)

lemma restrict_apply': "x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x" by simp
lemma restrict_ext: "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)" by (simp add: fun_eq_iff hom_def restrict_def)


locale set_morphism=
  fixes f::"'a \<Rightarrow> 'b" and
        A::"'a set" and
        B::"'b set"
  assumes is_set_morphism[intro,simp]:"f \<in> hom A B"
begin
lemma map_closed[intro, simp]:"x \<in> A \<Longrightarrow> f x \<in> B" using hom9 by fastforce
lemma map_undefined[intro]:"x \<notin> A \<Longrightarrow> f x = undefined" using hom10 by fastforce
end

locale set_epimorphism =set_morphism+assumes 
  is_surj[intro]: "f`A = B"

locale set_monomorphism=set_morphism+assumes
  is_inj[intro, simp]:"inj_on f A"

locale is_set_isomorphism=
  fixes f::"'a \<Rightarrow> 'b" and
        A::"'a set" and
        B::"'b set"
  assumes is_bijective[intro,simp]:"bij_betw f A B"

locale set_isomorphism =set_morphism +is_set_isomorphism
begin
sublocale set_epimorphism by (simp add: bij_betw_imp_surj_on set_epimorphism.intro set_epimorphism_axioms_def set_morphism_axioms) 
sublocale set_monomorphism by (meson bij_betw_def is_bijective set_monomorphism_axioms.intro set_monomorphism_def set_morphism_axioms) 
sublocale inverse: set_morphism "restrict (inv_into A f) B" B A  by (simp add: hom_memI inv_into_into is_surj set_morphism.intro)
sublocale inverse: is_set_isomorphism "restrict (inv_into A f) B" B A  by(unfold_locales, metis bij_betw_cong bij_betw_inv_into is_bijective restrict_apply')
end

end