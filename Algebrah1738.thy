theory Algebrah1738
  imports Posets9
begin

section \<open>Set Morphisms\<close>

definition maps_to::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "maps_to A B \<equiv> {f. (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)}"

lemma maps_to_memI1[intro!]:"(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> maps_to A B"
  by (simp add:maps_to_def)

lemma maps_to_memI2:"f`A \<subseteq> B \<Longrightarrow> f \<in> maps_to A B"
  by (simp add:image_subset_iff maps_to_def)

lemma maps_to_memE1:"\<lbrakk>f \<in> maps_to A B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add:maps_to_def)

lemma maps_to_memE2:"f \<in> maps_to A B \<Longrightarrow> f`A \<subseteq> B"
  by (simp add:image_subsetI maps_to_memE1)

lemma maps_to_iff:"f \<in> maps_to A B \<longleftrightarrow> (\<forall>x\<in>A. f x \<in> B)"
  by (auto simp:maps_to_def)

definition maps_on::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "maps_on A \<equiv> {f. (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined)}"

lemma fun_eqI1:"(\<And>x. f x = g x) \<Longrightarrow> f = g"
  by auto

lemma maps_on_memI1:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> maps_on A"
  by (simp add:maps_on_def)

lemma maps_on_memE1:"\<lbrakk>f \<in> maps_on A; x \<notin> A\<rbrakk> \<Longrightarrow> f x = undefined"
  by (simp add:maps_on_def)

lemma maps_on_eqI1:
  assumes A0:"f \<in> maps_on A" and A1:"g \<in> maps_on A" and A2:"\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows "f = g"
proof(rule fun_eqI1)
  fix x show "f x = g x"
  proof(cases "x \<in> A")
    case True
    then show ?thesis
      by (simp add:A2)
  next
    case False
    then obtain "f x = undefined" and "g x = undefined"
      using A0 A1 maps_on_memE1[of f A x] maps_on_memE1[of g A x] by auto
    then show ?thesis
      by simp
  qed
qed

definition set_mor::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "set_mor A B \<equiv> {f. ((\<forall>x. x \<notin> A \<longrightarrow> f x = undefined) \<and> (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B))}"

lemma set_morphisms_memI1[intro!]:"(\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> set_mor A B"
  by (simp add:set_mor_def)

lemma set_morphisms_memI2:"\<lbrakk>f \<in> maps_to A B; f \<in> maps_on A\<rbrakk> \<Longrightarrow> f \<in> set_mor A B"
  by (simp add:maps_on_def maps_to_def set_mor_def)

lemma set_morphisms_memE1:"\<lbrakk>f \<in> set_mor A B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add:set_mor_def)

lemma set_morphisms_memE2:"f \<in> set_mor A B \<Longrightarrow> f \<in> maps_to A B"
  by (simp add:maps_on_def maps_to_def set_mor_def)

lemma set_morphisms_memE3:"f \<in> set_mor A B \<Longrightarrow> f \<in> maps_on A"
  by (simp add:maps_on_def maps_to_def set_mor_def)

lemma set_morphisms_memE4:"\<lbrakk>f \<in> set_mor A B; x \<notin> A\<rbrakk> \<Longrightarrow> f x = undefined"
  by (simp add:set_mor_def)

lemma set_morphisms_memE5[elim]:"\<lbrakk>f \<in> set_mor A B; \<lbrakk>x \<in> A; f x \<in> B\<rbrakk> \<Longrightarrow> P; \<lbrakk>x \<notin> A; f x = undefined\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:set_mor_def)

lemma set_mor1:"set_mor A B \<subseteq> maps_on A"
  by (simp add:maps_on_def set_mor_def subset_iff)

lemma set_mor2:"set_mor A B \<subseteq> maps_to A B"
  by (simp add:maps_to_def set_mor_def subset_iff)

lemma set_mor_iff:"f \<in> set_mor A B \<longleftrightarrow> f \<in> maps_to A B \<and> f \<in> maps_on A"
  by (auto simp:maps_on_def maps_to_def set_mor_def)

lemma set_mor_eqI:"\<lbrakk>f \<in> set_mor A B; g \<in> set_mor A C; \<And>x. x \<in> A \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> f = g"
  by (rule maps_on_eqI1[OF set_morphisms_memE3 set_morphisms_memE3])

definition set_iso::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "set_iso A B \<equiv> {f \<in> set_mor A B. bij_betw f A B}"

lemma set_iso_memI1:"\<lbrakk>f \<in> set_mor A B; bij_betw f A B\<rbrakk> \<Longrightarrow> f \<in> set_iso A B"
  by (simp add:set_iso_def)

lemma set_iso_memE1:"\<lbrakk>f \<in> set_iso A B; x \<notin> A\<rbrakk> \<Longrightarrow> f x = undefined"
  by (simp add:set_iso_def set_mor_def)

lemma set_iso_memE2:"\<lbrakk>f \<in> set_iso A B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add:set_iso_def set_mor_def)

lemma set_iso_memE3:"f \<in> set_iso A B \<Longrightarrow> inj_on f A"
  by (simp add:set_iso_def bij_betw_def)

lemma set_iso_memE4:"f \<in> set_iso A B \<Longrightarrow> f`A = B"
  by (simp add:set_iso_def bij_betw_def)

lemma set_iso_memE5:"f \<in> set_iso A B \<Longrightarrow> bij_betw f A B"
  by (simp add:set_iso_def)

lemma set_iso1:"set_iso A B \<subseteq> set_mor A B"
  by (auto simp:set_iso_def)

subsection \<open>Restriction\<close>

definition "restrict"::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
  where "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"

syntax "_lam"::"pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
syntax_consts "_lam" \<rightleftharpoons> restrict
translations "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"

lemma restrict_cong:"I = J \<Longrightarrow> (\<And>i. i \<in> J =simp=> f i = g i) \<Longrightarrow> restrict f I = restrict g J"
  by (auto simp:restrict_def fun_eq_iff simp_implies_def)

lemma restrictI2:"(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> maps_to A B"
  by (simp add:maps_to_def restrict_def)

lemma restrict_apply[simp]:"(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"
  by (simp add:restrict_def)

lemma restrict_apply1:"x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x"
  by (simp add:restrict_def)

lemma restrict_ext:"(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
  by (simp add:fun_eq_iff restrict_def)

lemma restrict_maps_on[simp]:"(\<lambda>x\<in>A. f x) \<in> maps_on A"
  by (simp add:maps_on_def restrict_def)

lemma restrict_set_mor_iff[simp]:"(\<lambda>x\<in>A. f x) \<in> set_mor A B \<longleftrightarrow> (\<forall>x\<in>A. f x \<in> B)"
  by (auto simp:set_mor_def restrict_def)

lemma maps_on_restrict:"f \<in> maps_on A \<Longrightarrow> (\<lambda>x\<in>A. f x) = f"
  by (rule maps_on_eqI1[OF restrict_maps_on]) simp_all

lemma set_mor_restrict[simp]:"f \<in> set_mor A B \<Longrightarrow> (\<lambda>x\<in>A. f x) = f"
  by (rule maps_on_restrict[OF set_morphisms_memE3])

lemma image_restrict_eq[simp]:"(\<lambda>x\<in>A. f x) ` A = f ` A"
  by (auto simp:restrict_def)

lemma inj_on_restrict_eq[simp]:"inj_on (\<lambda>x\<in>A. f x) A \<longleftrightarrow> inj_on f A"
  by (simp add:inj_on_def restrict_def)

lemma bij_betw_restrict_eq[simp]:"bij_betw (\<lambda>x\<in>A. f x) A B \<longleftrightarrow> bij_betw f A B"
  by (simp add:bij_betw_def)

subsection \<open>Composition\<close>

definition compose::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "compose A g f = (\<lambda>x\<in>A. g (f x))"

abbreviation Id where "Id X \<equiv> (\<lambda>x\<in>X. x)"

lemma id_maps_on:"Id X \<in> maps_on X"
  by (simp add:maps_on_memI1 restrict_def)

lemma Id_set_mor[simp]:"Id X \<in> set_mor X X"
  by simp

lemma comp_maps_on[simp]:"compose A g f \<in> maps_on A"
  by (simp add:compose_def maps_on_memI1 restrict_def)

lemma is_comp:"\<lbrakk>f \<in> maps_to A B; g \<in> maps_to B C\<rbrakk> \<Longrightarrow> compose A g f \<in> maps_to A C"
  by (simp add:maps_to_def compose_def restrict_def)

lemma comp_set_mor:"\<lbrakk>f \<in> set_mor A B; g \<in> set_mor B C\<rbrakk> \<Longrightarrow> compose A g f \<in> set_mor A C"
  by (auto simp:set_mor_def compose_def restrict_def)

lemma comp_assoc:"f \<in> maps_to A B \<Longrightarrow> compose A h (compose A g f) = compose A (compose B h g) f"
  by (simp add:fun_eq_iff compose_def restrict_def maps_to_def)

lemma comp_eq:"x \<in> A \<Longrightarrow> compose A g f x = g (f x)"
  by (simp add:compose_def restrict_def)

lemma comp_Id:"f \<in> set_mor A B \<Longrightarrow> compose A f (Id A) = f"
  by (auto simp:fun_eq_iff compose_def set_mor_def restrict_def)

lemma Id_comp:"f \<in> set_mor A B \<Longrightarrow> compose A (Id B) f = f"
  by (auto simp:fun_eq_iff compose_def set_mor_def restrict_def)

lemma comp_image:"compose A g f ` A = g ` (f ` A)"
  by (auto simp:compose_def restrict_def)

subsection \<open>Bijections\<close>

lemma bij_betwI2:
  assumes A0:"f \<in> maps_to A B" and A1:"g \<in> maps_to B A"
    and A2:"\<And>x. x \<in> A \<Longrightarrow> g (f x) = x" and A3:"\<And>y. y \<in> B \<Longrightarrow> f (g y) = y"
  shows "bij_betw f A B"
proof(rule bij_betw_imageI)
  show "inj_on f A"
    by (rule inj_onI) (metis A2)
  show "f ` A = B"
  proof
    show "f ` A \<subseteq> B"
      by (rule maps_to_memE2[OF A0])
    show "B \<subseteq> f ` A"
    proof
      fix y assume B0:"y \<in> B"
      have "y = f (g y)"
        by (simp add:A3[OF B0])
      then show "y \<in> f ` A"
        using maps_to_memE1[OF A1 B0] by (rule image_eqI)
    qed
  qed
qed

lemma bij_betw_set_iso:"bij_betw f A B \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> set_iso A B"
  by (auto simp:set_iso_def bij_betw_def)

locale magma =
  fixes X :: "'a set" and mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
  assumes closed [simp, intro]: "\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> X"

locale semigroup = magma +
  assumes assoc: "\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

locale commutative_magma = magma +
  assumes commute: "\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"

locale unital_magma = magma +
  fixes unit :: 'a ("\<one>")
  assumes unit_closed [simp, intro]: "\<one> \<in> X"
    and unit_left [simp]: "x \<in> X \<Longrightarrow> \<one> \<cdot> x = x"
    and unit_right [simp]: "x \<in> X \<Longrightarrow> x \<cdot> \<one> = x"

locale monoid = semigroup + unital_magma

locale commutative_semigroup = semigroup + commutative_magma

locale commutative_monoid = monoid + commutative_semigroup

locale group = monoid +
  assumes inverse_ex: "x \<in> X \<Longrightarrow> \<exists>y\<in>X. y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"

locale commutative_group = group + commutative_monoid

lemma (in unital_magma) unit_unique:
  assumes "u \<in> X" and "\<And>x. x \<in> X \<Longrightarrow> u \<cdot> x = x"
  shows "u = \<one>"
proof -
  have "u = u \<cdot> \<one>" using assms(1) by simp
  also have "\<dots> = \<one>" by (rule assms(2)) simp
  finally show ?thesis .
qed

lemma (in commutative_semigroup) left_commute:
  assumes "x \<in> X" "y \<in> X" "z \<in> X"
  shows "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" using assms by (simp add: assoc)
  also have "\<dots> = (y \<cdot> x) \<cdot> z" using commute[OF assms(1,2)] by simp
  also have "\<dots> = y \<cdot> (x \<cdot> z)" using assms by (simp add: assoc)
  finally show ?thesis .
qed


lemma (in commutative_group)
  "\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  and "\<lbrakk>u \<in> X; \<And>x. x \<in> X \<Longrightarrow> u \<cdot> x = x\<rbrakk> \<Longrightarrow> u = \<one>"
  by (rule left_commute, assumption+) (rule unit_unique)


lemma commutative_monoidI:
  assumes "commutative_semigroup X mul" and "e \<in> X" and "\<And>x. x \<in> X \<Longrightarrow> mul e x = x"
  shows "commutative_monoid X mul e"
proof -
  interpret commutative_semigroup X mul by fact
  show ?thesis
  proof unfold_locales
    show "e \<in> X" by fact
    show "mul e x = x" if "x \<in> X" for x using that by (rule assms(3))
    show "mul x e = x" if "x \<in> X" for x using that assms(2,3) commute[of x e] by simp
  qed
qed


context magma
begin

definition subs :: "'a set set"
  where "subs = {A. A \<subseteq> X \<and> (\<forall>a\<in>A. \<forall>b\<in>A. a \<cdot> b \<in> A)}"

lemma subsI: "\<lbrakk>A \<subseteq> X; \<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A\<rbrakk> \<Longrightarrow> A \<in> subs"
  by (simp add: subs_def)

lemma subsD: assumes "A \<in> subs" shows "A \<subseteq> X" and "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A"
  using assms by (auto simp: subs_def)

lemma sub_magma: "A \<in> subs \<Longrightarrow> magma A (\<cdot>)"
  by unfold_locales (rule subsD)

sublocale sub: moore_family X subs
proof unfold_locales
  show "subs \<subseteq> Pow X" by (auto simp: subs_def)
  show "X \<in> subs" by (rule subsI) auto
  show "\<Inter>E \<in> subs" if "E \<subseteq> subs" "E \<noteq> {}" for E
    using that by (intro subsI) (auto dest: subsD)
qed

lemma join_submagmas: "\<lbrakk>A \<in> subs; B \<in> subs\<rbrakk> \<Longrightarrow> sub.closed.SupIn {A, B} = sub.cl (A \<union> B)"
  using sub.SupIn_closed_eq[of "{A, B}"] by simp

inductive_set gen :: "'a set \<Rightarrow> 'a set" for A :: "'a set"
  where base: "a \<in> A \<Longrightarrow> a \<in> gen A"
  | step: "\<lbrakk>a \<in> gen A; b \<in> gen A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> gen A"

lemma gen_eq_cl: assumes "A \<subseteq> X" shows "gen A = sub.cl A"
proof
  have cl: "sub.cl A \<in> subs" using assms by simp
  show "gen A \<subseteq> sub.cl A"
  proof
    fix a assume "a \<in> gen A"
    then show "a \<in> sub.cl A"
    proof induction
      case (base a)
      then show ?case using sub.cl_extensive[of A] by blast
    next
      case (step a b)
      then show ?case by (intro subsD(2)[OF cl])
    qed
  qed
  have "gen A \<in> subs"
  proof (rule subsI)
    show "gen A \<subseteq> X"
    proof
      fix a assume "a \<in> gen A"
      then show "a \<in> X" using assms by induction auto
    qed
  qed (rule step)
  then show "sub.cl A \<subseteq> gen A" by (rule sub.cl_least) (auto intro: base)
qed

end


context monoid
begin

definition submonoids :: "'a set set"
  where "submonoids = {A \<in> subs. \<one> \<in> A}"

sublocale submon: moore_family X submonoids
proof unfold_locales
  show "submonoids \<subseteq> Pow X" using sub.base by (auto simp: submonoids_def)
  show "X \<in> submonoids" using sub.whole by (simp add: submonoids_def)
  show "\<Inter>E \<in> submonoids" if "E \<subseteq> submonoids" "E \<noteq> {}" for E
    using that sub.Inter_closed[of E] by (auto simp: submonoids_def)
qed

end


locale magma_hom = dom: magma X mul + cod: magma Y mul'
  for X :: "'a set" and mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
    and Y :: "'b set" and mul' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<star>" 70) +
  fixes f :: "'a \<Rightarrow> 'b"
  assumes maps [simp, intro]: "x \<in> X \<Longrightarrow> f x \<in> Y"
    and hom: "\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (x \<cdot> y) = f x \<star> f y"
begin

lemma image_sub: assumes "A \<in> dom.subs" shows "f ` A \<in> cod.subs"
proof (rule cod.subsI)
  note A = dom.subsD[OF assms]
  show "f ` A \<subseteq> Y" using A(1) by auto
  fix a' b' assume "a' \<in> f ` A" "b' \<in> f ` A"
  then obtain a b where ab: "a \<in> A" "b \<in> A" "a' = f a" "b' = f b" by blast
  then have "a' \<star> b' = f (a \<cdot> b)" using A(1) by (simp add: hom subset_iff)
  then show "a' \<star> b' \<in> f ` A" using A(2)[OF ab(1,2)] by simp
qed


lemma vimage_sub: assumes "B \<in> cod.subs" shows "X \<inter> f -` B \<in> dom.subs"
  using cod.subsD[OF assms] by (intro dom.subsI) (auto simp: hom)

lemma image_cl: assumes "A \<subseteq> X" shows "f ` dom.sub.cl A = cod.sub.cl (f ` A)"
proof
  have fA: "f ` A \<subseteq> Y" using assms by auto
  have "dom.sub.cl A \<subseteq> X \<inter> f -` cod.sub.cl (f ` A)"
  proof (rule dom.sub.cl_least)
    show "X \<inter> f -` cod.sub.cl (f ` A) \<in> dom.subs" using fA by (intro vimage_sub) simp
    show "A \<subseteq> X \<inter> f -` cod.sub.cl (f ` A)" using assms cod.sub.cl_extensive[of "f ` A"] by auto
  qed
  then show "f ` dom.sub.cl A \<subseteq> cod.sub.cl (f ` A)" by auto
  show "cod.sub.cl (f ` A) \<subseteq> f ` dom.sub.cl A"
  proof (rule cod.sub.cl_least)
    show "f ` dom.sub.cl A \<in> cod.subs" using assms by (intro image_sub) simp
    show "f ` A \<subseteq> f ` dom.sub.cl A" using dom.sub.cl_extensive[of A] by auto
  qed
qed


lemma surj_semigroup: assumes surj: "f ` X = Y" and "semigroup X (\<cdot>)" shows "semigroup Y (\<star>)"
proof -
  interpret dom: semigroup X "(\<cdot>)" by fact
  show ?thesis
  proof unfold_locales
    fix a b c assume "a \<in> Y" "b \<in> Y" "c \<in> Y"
    then obtain x y z where "x \<in> X" "y \<in> X" "z \<in> X" "a = f x" "b = f y" "c = f z"
      unfolding surj[symmetric] by blast
    then show "(a \<star> b) \<star> c = a \<star> (b \<star> c)" by (simp add: hom[symmetric] dom.assoc)
  qed
qed

lemma surj_commutative:
  assumes surj: "f ` X = Y" and "commutative_magma X (\<cdot>)" shows "commutative_magma Y (\<star>)"
proof -
  interpret dom: commutative_magma X "(\<cdot>)" by fact
  show ?thesis
  proof unfold_locales
    fix a b assume "a \<in> Y" "b \<in> Y"
    then obtain x y where "x \<in> X" "y \<in> X" "a = f x" "b = f y" unfolding surj[symmetric] by blast
    then show "a \<star> b = b \<star> a" using dom.commute[of x y] by (simp add: hom[symmetric])
  qed
qed

lemma surj_monoid: assumes surj: "f ` X = Y" and "monoid X (\<cdot>) e" shows "monoid Y (\<star>) (f e)"
proof -
  interpret dom: monoid X "(\<cdot>)" e by fact
  interpret cod: semigroup Y "(\<star>)" by (rule surj_semigroup[OF surj]) (rule dom.semigroup_axioms)
  show ?thesis
  proof unfold_locales
    show "f e \<in> Y" by simp
    fix a assume "a \<in> Y"
    then obtain x where "x \<in> X" "a = f x" unfolding surj[symmetric] by blast
    then show "f e \<star> a = a" and "a \<star> f e = a" by (simp_all add: hom[symmetric])
  qed
qed

end

locale monoid_hom = magma_hom X mul Y mul' f + dom: monoid X mul e + cod: monoid Y mul' e'
  for X :: "'a set" and mul (infixl "\<cdot>" 70) and e
    and Y :: "'b set" and mul' (infixl "\<star>" 70) and e' and f +
  assumes unit: "f e = e'"

locale magma_iso = magma_hom +
  assumes bij: "bij_betw f X Y"



context magma_hom
begin


lemma factor:
  fixes Q :: "'c set" and qmul :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" (infixl "\<bullet>" 70) and p :: "'a \<Rightarrow> 'c"
  assumes p: "magma_hom X (\<cdot>) Q (\<bullet>) p" and surj: "p ` X = Q"
    and ker: "\<And>x y. \<lbrakk>x \<in> X; y \<in> X; p x = p y\<rbrakk> \<Longrightarrow> f x = f y"
  obtains h where "magma_hom Q (\<bullet>) Y (\<star>) h" and "\<And>x. x \<in> X \<Longrightarrow> h (p x) = f x"
proof -
  interpret p: magma_hom X "(\<cdot>)" Q "(\<bullet>)" p by fact
  define h where "h t = f (SOME x. x \<in> X \<and> p x = t)" for t
  have hp: "h (p x) = f x" if "x \<in> X" for x
  proof -
    have "(SOME x'. x' \<in> X \<and> p x' = p x) \<in> X \<and> p (SOME x'. x' \<in> X \<and> p x' = p x) = p x"
      by (rule someI[of "\<lambda>x'. x' \<in> X \<and> p x' = p x" x]) (simp add: that)
    then show ?thesis unfolding h_def using ker that by blast
  qed
  have "magma_hom Q (\<bullet>) Y (\<star>) h"
  proof unfold_locales
    fix t assume "t \<in> Q"
    then obtain x where "x \<in> X" "t = p x" unfolding surj[symmetric] by blast
    then show "h t \<in> Y" by (simp add: hp)
  next
    fix t s assume "t \<in> Q" "s \<in> Q"
    then obtain x y where xy: "x \<in> X" "y \<in> X" "t = p x" "s = p y"
      unfolding surj[symmetric] by blast
    then have "h (t \<bullet> s) = h (p (x \<cdot> y))" by (simp add: p.hom)
    also have "\<dots> = f x \<star> f y" using xy by (simp add: hp hom)
    finally show "h (t \<bullet> s) = h t \<star> h s" using xy by (simp add: hp)
  qed
  then show thesis using hp by (rule that)
qed


lemma first_iso:
  fixes Q :: "'c set" and qmul :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" (infixl "\<bullet>" 70) and p :: "'a \<Rightarrow> 'c"
  assumes p: "magma_hom X (\<cdot>) Q (\<bullet>) p" and surj: "p ` X = Q"
    and ker: "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> p x = p y \<longleftrightarrow> f x = f y"
  obtains h where "magma_iso Q (\<bullet>) (f ` X) (\<star>) h" and "\<And>x. x \<in> X \<Longrightarrow> h (p x) = f x"
proof -
  obtain h where h: "magma_hom Q (\<bullet>) Y (\<star>) h" and hp: "\<And>x. x \<in> X \<Longrightarrow> h (p x) = f x"
    using factor[OF p surj] ker by blast
  interpret h: magma_hom Q "(\<bullet>)" Y "(\<star>)" h by fact
  interpret im: magma "f ` X" "(\<star>)" by (intro cod.sub_magma image_sub dom.sub.whole)
  have img: "h ` Q = f ` X"
  proof -
    have "h ` Q = (\<lambda>x. h (p x)) ` X" unfolding surj[symmetric] by (simp add: image_image)
    also have "\<dots> = f ` X" by (rule image_cong) (simp_all add: hp)
    finally show ?thesis .
  qed
  have inj: "inj_on h Q"
  proof (rule inj_onI)
    fix t s assume "t \<in> Q" "s \<in> Q" and eq: "h t = h s"
    then obtain x y where xy: "x \<in> X" "y \<in> X" "t = p x" "s = p y"
      unfolding surj[symmetric] by blast
    with eq have "f x = f y" by (simp add: hp)
    with xy show "t = s" by (simp add: ker)
  qed
  have "magma_iso Q (\<bullet>) (f ` X) (\<star>) h"
  proof unfold_locales
    show "h t \<in> f ` X" if "t \<in> Q" for t using that img by blast
    show "h (t \<bullet> s) = h t \<star> h s" if "t \<in> Q" "s \<in> Q" for t s using that by (rule h.hom)
    show "bij_betw h Q (f ` X)" using inj img by (simp add: bij_betw_def)
  qed
  then show thesis using hp by (rule that)
qed

end

locale congruence = magma +
  fixes R :: "'a rel"
  assumes R_carrier: "R \<subseteq> X \<times> X"
    and R_refl: "x \<in> X \<Longrightarrow> (x, x) \<in> R"
    and R_sym: "(x, y) \<in> R \<Longrightarrow> (y, x) \<in> R"
    and R_trans: "\<lbrakk>(x, y) \<in> R; (y, z) \<in> R\<rbrakk> \<Longrightarrow> (x, z) \<in> R"
    and R_compat: "\<lbrakk>(x, x') \<in> R; (y, y') \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> y, x' \<cdot> y') \<in> R"
begin

definition cls :: "'a \<Rightarrow> 'a set"
  where "cls x = R `` {x}"

definition quot :: "'a set set"
  where "quot = cls ` X"

definition qmul :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<bullet>" 70)
  where "A \<bullet> B = (\<Union>a\<in>A. \<Union>b\<in>B. cls (a \<cdot> b))"

lemma cls_eq_iff: assumes "x \<in> X" "y \<in> X" shows "cls x = cls y \<longleftrightarrow> (x, y) \<in> R"
proof
  assume eq: "cls x = cls y"
  have "y \<in> cls y" using assms(2) by (simp add: cls_def R_refl)
  then have "y \<in> cls x" by (simp add: eq)
  then show "(x, y) \<in> R" by (simp add: cls_def)
next
  assume "(x, y) \<in> R"
  then show "cls x = cls y" unfolding cls_def by (blast intro: R_sym R_trans)
qed

lemma qmul_cls: assumes "x \<in> X" "y \<in> X" shows "cls x \<bullet> cls y = cls (x \<cdot> y)"
proof
  have self: "x \<in> cls x" "y \<in> cls y" using assms by (simp_all add: cls_def R_refl)
  show "cls (x \<cdot> y) \<subseteq> cls x \<bullet> cls y" unfolding qmul_def using self by blast
  show "cls x \<bullet> cls y \<subseteq> cls (x \<cdot> y)"
  proof
    fix z assume "z \<in> cls x \<bullet> cls y"
    then obtain a b where ab: "(x, a) \<in> R" "(y, b) \<in> R" and z: "z \<in> cls (a \<cdot> b)"
      by (auto simp: qmul_def cls_def)
    have "(x \<cdot> y, a \<cdot> b) \<in> R" using ab by (rule R_compat)
    moreover have "a \<in> X" "b \<in> X" using ab R_carrier by auto
    ultimately have "cls (x \<cdot> y) = cls (a \<cdot> b)" using assms by (simp add: cls_eq_iff)
    with z show "z \<in> cls (x \<cdot> y)" by simp
  qed
qed

sublocale quotient: magma quot "(\<bullet>)"
proof unfold_locales
  fix A B assume "A \<in> quot" "B \<in> quot"
  then obtain x y where "x \<in> X" "y \<in> X" "A = cls x" "B = cls y" by (auto simp: quot_def)
  then show "A \<bullet> B \<in> quot" by (simp add: qmul_cls quot_def)
qed

lemma proj_hom: "magma_hom X (\<cdot>) quot (\<bullet>) cls"
  by unfold_locales (simp_all add: quot_def qmul_cls)

lemma proj_surj: "cls ` X = quot"
  by (simp add: quot_def)

end

context magma_hom
begin

definition K :: "'a rel"
  where "K = {(x, y). x \<in> X \<and> y \<in> X \<and> f x = f y}"

lemma ker_congruence: "congruence X (\<cdot>) K"
  by unfold_locales (auto simp: K_def hom)

end


sublocale congruence \<subseteq> proj: magma_hom X mul quot qmul cls
  by (rule proj_hom)

lemma (in congruence) quotient_monoid: "monoid X (\<cdot>) e \<Longrightarrow> monoid quot (\<bullet>) (cls e)"
  by (rule proj.surj_monoid[OF proj_surj])

context magma_hom
begin

context
begin

interpretation ker: congruence X "(\<cdot>)" K
  by (rule ker_congruence)

theorem first_iso_quotient:
  obtains h where "magma_iso ker.quot ker.qmul (f ` X) (\<star>) h"
    and "\<And>x. x \<in> X \<Longrightarrow> h (ker.cls x) = f x"
proof (rule first_iso[OF ker.proj_hom ker.proj_surj])
  fix x y assume xy: "x \<in> X" "y \<in> X"
  have "ker.cls x = ker.cls y \<longleftrightarrow> (x, y) \<in> K" using xy by (rule ker.cls_eq_iff)
  also have "\<dots> \<longleftrightarrow> f x = f y" using xy by (simp add: K_def)
  finally show "ker.cls x = ker.cls y \<longleftrightarrow> f x = f y" .
qed (rule that)

end

end

context monoid_hom
begin

context
begin

interpretation ker: congruence X "(\<cdot>)" K
  by (rule ker_congruence)

theorem first_iso_monoid:
  obtains h where "magma_iso ker.quot ker.qmul (f ` X) (\<star>) h"
    and "monoid ker.quot ker.qmul (ker.cls e)" and "h (ker.cls e) = e'"
proof (rule first_iso_quotient)
  fix h assume iso: "magma_iso ker.quot ker.qmul (f ` X) (\<star>) h"
    and h: "\<And>x. x \<in> X \<Longrightarrow> h (ker.cls x) = f x"
  have mon: "monoid ker.quot ker.qmul (ker.cls e)"
    by (rule ker.quotient_monoid) (rule dom.monoid_axioms)
  have "h (ker.cls e) = e'" by (simp add: h unit)
  with iso mon show thesis by (rule that)
qed

end

end

locale magma_u =
  fixes X :: "'a set" and law :: "'a \<times> 'a \<Rightarrow> 'a"
  assumes law_closed: "u \<in> X \<times> X \<Longrightarrow> law u \<in> X"

sublocale magma_u \<subseteq> cur: magma X "\<lambda>x y. law (x, y)"
  rewrites "(\<lambda>u. law (fst u, snd u)) = law"
  by unfold_locales (auto simp: law_closed)

sublocale magma \<subseteq> unc: magma_u X "\<lambda>u. fst u \<cdot> snd u"
  rewrites "(\<lambda>x y. fst (x, y) \<cdot> snd (x, y)) = (\<cdot>)"
  by unfold_locales auto

lemma (in magma_u) "A \<subseteq> X \<Longrightarrow> cur.gen A = cur.sub.cl A"
  by (rule cur.gen_eq_cl)



context congruence
begin

lemma equiv: "equiv X R"
  unfolding equiv_def refl_on_def sym_def trans_def using R_carrier R_refl R_sym R_trans by blast

lemma cls_eq_proj: "cls = Equiv_Relations.proj R"
  by (simp add: fun_eq_iff cls_def Equiv_Relations.proj_def)

lemma quot_eq: "quot = X // R"
  by (auto simp: quot_def cls_def quotient_def)

text \<open>So nothing about quotient sets needs re-proving; for instance:\<close>

lemma "\<Union>quot = X" and "\<lbrakk>t \<in> quot; s \<in> quot\<rbrakk> \<Longrightarrow> t = s \<or> t \<inter> s = {}"
  using Union_quotient[OF equiv] quotient_disj[OF equiv] by (simp_all add: quot_eq)

end


context congruence
begin

theorem factor_set:
  assumes compat: "\<And>x y. (x, y) \<in> R \<Longrightarrow> g x = g y"
  obtains h where "\<And>x. x \<in> X \<Longrightarrow> h (cls x) = g x"
    and "\<And>h' t. \<lbrakk>\<And>x. x \<in> X \<Longrightarrow> h' (cls x) = g x; t \<in> quot\<rbrakk> \<Longrightarrow> h' t = h t"
proof -
  define h where "h t = g (SOME x. x \<in> X \<and> cls x = t)" for t
  have hp: "h (cls x) = g x" if x: "x \<in> X" for x
  proof -
    let ?x' = "SOME x'. x' \<in> X \<and> cls x' = cls x"
    have 1: "?x' \<in> X \<and> cls ?x' = cls x" by (rule someI[of _ x]) (simp add: x)
    have "(?x', x) \<in> R"
      by (rule cls_eq_iff[OF conjunct1[OF 1] x, THEN iffD1]) (rule conjunct2[OF 1])
    then show ?thesis unfolding h_def by (rule compat)
  qed
  show thesis
  proof (rule that[OF hp])
    fix h' t assume h': "\<And>x. x \<in> X \<Longrightarrow> h' (cls x) = g x" and "t \<in> quot"
    then obtain x where "x \<in> X" "t = cls x" by (auto simp: quot_def)
    then show "h' t = h t" by (simp add: h' hp)
  qed
qed

end




context magma
begin

definition congs :: "'a rel set"
  where "congs = {R. congruence X (\<cdot>) R}"

lemma congsI: "congruence X (\<cdot>) R \<Longrightarrow> R \<in> congs"
  and congsD: "R \<in> congs \<Longrightarrow> congruence X (\<cdot>) R"
  by (simp_all add: congs_def)

lemma total_cong: "congruence X (\<cdot>) (X \<times> X)"
  by unfold_locales auto

lemma Inter_cong:
  assumes E: "E \<subseteq> congs" "E \<noteq> {}"
  shows "congruence X (\<cdot>) (\<Inter>E)"
proof -
  have c: "congruence X (\<cdot>) S" if "S \<in> E" for S using E(1) that by (auto simp: congs_def)
  obtain S0 where S0: "S0 \<in> E" using E(2) by blast
  show ?thesis
  proof (rule congruence.intro[OF magma_axioms], unfold_locales)
    show "\<Inter>E \<subseteq> X \<times> X" using congruence.R_carrier[OF c[OF S0]] S0 by blast
    show "(x, x) \<in> \<Inter>E" if "x \<in> X" for x using congruence.R_refl[OF c] that by blast
    show "(y, x) \<in> \<Inter>E" if "(x, y) \<in> \<Inter>E" for x y using congruence.R_sym[OF c] that by blast
    show "(x, z) \<in> \<Inter>E" if "(x, y) \<in> \<Inter>E" "(y, z) \<in> \<Inter>E" for x y z
      using congruence.R_trans[OF c] that by blast
    show "(x \<cdot> y, x' \<cdot> y') \<in> \<Inter>E" if "(x, x') \<in> \<Inter>E" "(y, y') \<in> \<Inter>E" for x x' y y'
      using congruence.R_compat[OF c] that by blast
  qed
qed

sublocale cong: moore_family "X \<times> X" congs
proof unfold_locales
  show "congs \<subseteq> Pow (X \<times> X)" using congruence.R_carrier by (auto simp: congs_def)
  show "X \<times> X \<in> congs" by (rule congsI[OF total_cong])
  show "\<Inter>E \<in> congs" if "E \<subseteq> congs" "E \<noteq> {}" for E by (rule congsI[OF Inter_cong[OF that]])
qed


lemma congruence_lattice: "complete_lattice_on subset_order congs"
  by (rule cong.cs.cr.closed_complete)

lemma cong_join: "\<lbrakk>S \<in> congs; T \<in> congs\<rbrakk> \<Longrightarrow> cong.closed.SupIn {S, T} = cong.cl (S \<union> T)"
  using cong.SupIn_closed_eq[of "{S, T}"] by simp

lemma cong_meet: "\<lbrakk>S \<in> congs; T \<in> congs\<rbrakk> \<Longrightarrow> cong.closed.InfIn {S, T} = S \<inter> T"
  using cong.InfIn_closed_eq[of "{S, T}"] by simp

end

lemma (in magma_hom) K_cong: "K \<in> dom.congs"
  by (rule dom.congsI[OF ker_congruence])


context magma
begin

definition commutes::"'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "commutes A B \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>B. a \<cdot> b = b \<cdot> a)"

definition centralizer::"'a set \<Rightarrow> 'a set"
  where "centralizer E = {x \<in> X. \<forall>y\<in>E. x \<cdot> y = y \<cdot> x}"

definition center::"'a set"
  where "center = centralizer X"

abbreviation bicentralizer::"'a set \<Rightarrow> 'a set"
  where "bicentralizer \<equiv> centralizer \<circ> centralizer"

lemma commutesI:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a) \<Longrightarrow> commutes A B"
  and commutesD:"\<lbrakk>commutes A B; a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"
  unfolding commutes_def by blast+

lemma commutes_sym:"commutes A B \<Longrightarrow> commutes B A"
  by (auto simp:commutes_def)

lemma commutes_mono:"\<lbrakk>commutes A B; A' \<subseteq> A; B' \<subseteq> B\<rbrakk> \<Longrightarrow> commutes A' B'"
  by (auto simp:commutes_def)

lemma commutes_Un:"commutes (A \<union> A') B \<longleftrightarrow> commutes A B \<and> commutes A' B"
  by (auto simp:commutes_def)

lemma centralizer_memI1:"\<lbrakk>x \<in> X; \<And>y. y \<in> E \<Longrightarrow> commutes {x} {y}\<rbrakk> \<Longrightarrow> x \<in> centralizer E"
  by (simp add:centralizer_def commutes_def)

lemma centralizer_memI2:"\<lbrakk>x \<in> X; \<And>y. y \<in> E \<Longrightarrow> x \<cdot> y = y \<cdot> x\<rbrakk> \<Longrightarrow> x \<in> centralizer E"
  by (simp add:centralizer_def)

lemma centralizer_memI3:"\<lbrakk>x \<in> X; \<And>y. y \<in> E \<Longrightarrow> y \<cdot> x = x \<cdot> y\<rbrakk> \<Longrightarrow> x \<in> centralizer E"
  by (simp add:centralizer_def)

lemma centralizer_memD:"\<lbrakk>x \<in> centralizer E; a \<in> E\<rbrakk> \<Longrightarrow> a \<cdot> x = x \<cdot> a"
  by (simp add:centralizer_def)

lemma centralizer_mem_iff:"x \<in> centralizer E \<longleftrightarrow> x \<in> X \<and> commutes {x} E"
  by (simp add:centralizer_def commutes_def)

lemma center_memI1:"\<lbrakk>x \<in> X; \<And>y. y \<in> X \<Longrightarrow> commutes {x} {y}\<rbrakk> \<Longrightarrow> x \<in> center"
  by (simp add:center_def centralizer_memI1)

lemma center_memI2:"\<lbrakk>x \<in> X; \<And>y. y \<in> X \<Longrightarrow> x \<cdot> y = y \<cdot> x\<rbrakk> \<Longrightarrow> x \<in> center"
  by (simp add:center_def centralizer_memI2)

lemma center_memI3:"\<lbrakk>x \<in> X; \<And>y. y \<in> X \<Longrightarrow> y \<cdot> x = x \<cdot> y\<rbrakk> \<Longrightarrow> x \<in> center"
  by (simp add:center_def centralizer_memI3)

lemma center_memD:"\<lbrakk>x \<in> center; a \<in> X\<rbrakk> \<Longrightarrow> a \<cdot> x = x \<cdot> a"
  unfolding center_def by (rule centralizer_memD)

lemma center_mem_iff:"x \<in> center \<longleftrightarrow> x \<in> X \<and> (\<forall>y\<in>X. x \<cdot> y = y \<cdot> x)"
  by (simp add:center_def centralizer_def)

lemma centralizer_sub:"centralizer E \<subseteq> X"
  by (auto simp:centralizer_def)

lemma centralizer_antitone:"A \<subseteq> B \<Longrightarrow> centralizer B \<subseteq> centralizer A"
  by (auto simp:centralizer_def)

lemma centralizer_galois:"\<lbrakk>A \<subseteq> X; B \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> centralizer B \<longleftrightarrow> B \<subseteq> centralizer A"
  by (auto simp:centralizer_def subset_iff)

lemma centralizer_commutes1:"commutes A (centralizer A)"
  by (auto simp:commutes_def centralizer_def)

lemma centralizer_commutes2:"commutes (centralizer A) A"
  by (auto simp:commutes_def centralizer_def)

lemma commutes_sub_centralizer1:"\<lbrakk>B \<subseteq> X; commutes A B\<rbrakk> \<Longrightarrow> B \<subseteq> centralizer A"
  by (auto simp:commutes_def centralizer_def)

lemma commutes_sub_centralizer2:"\<lbrakk>B \<subseteq> X; commutes B A\<rbrakk> \<Longrightarrow> B \<subseteq> centralizer A"
  by (auto simp:commutes_def centralizer_def)

lemma commutes_iff_sub_centralizer:"B \<subseteq> X \<Longrightarrow> commutes A B \<longleftrightarrow> B \<subseteq> centralizer A"
  by (auto simp:commutes_def centralizer_def)

lemma center_sub:"center \<subseteq> X"
  by (simp add:center_def centralizer_sub)

lemma center_commutes:"commutes center X"
  by (simp add:center_def centralizer_commutes2)

lemma center_sub_centralizer:"A \<subseteq> X \<Longrightarrow> center \<subseteq> centralizer A"
  by (simp add:center_def centralizer_antitone)

lemma commutative_iff_center:"commutative_magma X (\<cdot>) \<longleftrightarrow> center = X"
proof
  assume "commutative_magma X (\<cdot>)"
  then show "center = X"
    using center_sub by (auto simp:commutative_magma_def commutative_magma_axioms_def center_mem_iff)
next
  assume A0:"center = X"
  show "commutative_magma X (\<cdot>)"
  proof(unfold_locales)
    fix x y assume "x \<in> X" and "y \<in> X"
    then show "x \<cdot> y = y \<cdot> x"
      using A0 center_memD[of x y] by simp
  qed
qed

end

sublocale magma \<subseteq> centralizer:galois_conn subset_order "Pow X" subset_order "Pow X" centralizer centralizer
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
proof-
  show "galois_conn subset_order (Pow X) subset_order (Pow X) centralizer centralizer"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset)
    show "\<And>A. A \<in> Pow X \<Longrightarrow> centralizer A \<in> Pow X"
      using centralizer_sub by blast
    show "\<And>A. A \<in> Pow X \<Longrightarrow> centralizer A \<in> Pow X"
      using centralizer_sub by blast
    show "\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (A, centralizer B) \<in> subset_order \<longleftrightarrow> (B, centralizer A) \<in> subset_order"
      by (simp add:centralizer_galois)
  qed
qed simp

context magma
begin

lemma centralizer_comp_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> centralizer (centralizer A)"
  using centralizer.ext_f[of A] by simp

lemma bicentralizer_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> bicentralizer A"
  by (simp add:centralizer_comp_extensive)

lemma bicentralizer_isotone:"A \<subseteq> B \<Longrightarrow> bicentralizer A \<subseteq> bicentralizer B"
  using centralizer_antitone[OF centralizer_antitone[of A B]] by simp

lemma bicentralizer_idempotent:"bicentralizer (bicentralizer A) = bicentralizer A"
  using centralizer.idem_f[of "centralizer A"] centralizer_sub[of A] by simp

lemma bicentralizer_closure:"closure_op subset_order (Pow X) bicentralizer"
  by (rule centralizer.closure.closure_op_axioms)

lemma bicentralizer_sub:"bicentralizer A \<subseteq> X"
  by (simp add:centralizer_sub)

lemma bicentralizer_commutes1:"commutes (centralizer A) (bicentralizer A)"
  using centralizer_commutes1[of "centralizer A"] by simp

lemma bicentralizer_commutes2:"commutes (bicentralizer A) (centralizer A)"
  using centralizer_commutes2[of "centralizer A"] by simp

lemma bicentralizer_mem_iff:
  "\<lbrakk>A \<subseteq> X; y \<in> X\<rbrakk> \<Longrightarrow> y \<in> bicentralizer A \<longleftrightarrow> (\<forall>x\<in>X. (\<forall>a\<in>A. x \<cdot> a = a \<cdot> x) \<longrightarrow> x \<cdot> y = y \<cdot> x)"
  by (auto simp:centralizer_def)

lemma centralizer_bicentralizer:
  assumes A0:"A \<subseteq> X"
  shows "centralizer (bicentralizer A) = centralizer A"
proof
  show "centralizer (bicentralizer A) \<subseteq> centralizer A"
    using centralizer_antitone[OF centralizer_comp_extensive[OF A0]] by simp
  show "centralizer A \<subseteq> centralizer (bicentralizer A)"
    using centralizer_comp_extensive[OF centralizer_sub[of A]] by simp
qed

end


context magma
begin

definition l_identity::"'a \<Rightarrow> bool"
  where "l_identity e \<longleftrightarrow> (\<forall>x\<in>X. e \<cdot> x = x)"

definition r_identity::"'a \<Rightarrow> bool"
  where "r_identity e \<longleftrightarrow> (\<forall>x\<in>X. x \<cdot> e = x)"

definition id_elem::"'a \<Rightarrow> bool"
  where "id_elem e \<longleftrightarrow> l_identity e \<and> r_identity e"

lemma id_elemI1:"\<lbrakk>\<And>x. x \<in> X \<Longrightarrow> x \<cdot> e = x; \<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x\<rbrakk> \<Longrightarrow> id_elem e"
  by (simp add:id_elem_def l_identity_def r_identity_def)

lemma id_elemI2:"(\<And>x. x \<in> X \<Longrightarrow> x \<cdot> e = x \<and> e \<cdot> x = x) \<Longrightarrow> id_elem e"
  by (simp add:id_elem_def l_identity_def r_identity_def)

lemma id_elemI3:"\<lbrakk>l_identity e; r_identity e\<rbrakk> \<Longrightarrow> id_elem e"
  by (simp add:id_elem_def)

lemma id_elemE1:"\<lbrakk>id_elem e; x \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> e = x"
  by (simp add:id_elem_def r_identity_def)

lemma id_elemE2:"\<lbrakk>id_elem e; x \<in> X\<rbrakk> \<Longrightarrow> e \<cdot> x = x"
  by (simp add:id_elem_def l_identity_def)

lemma id_elem_iff:"id_elem e \<longleftrightarrow> (\<forall>x\<in>X. e \<cdot> x = x \<and> x \<cdot> e = x)"
  by (auto simp:id_elem_def l_identity_def r_identity_def)

lemma l_r_identity_eq:"\<lbrakk>l_identity e; r_identity d; e \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> e = d"
proof-
  assume A0:"l_identity e" and A1:"r_identity d" and A2:"e \<in> X" and A3:"d \<in> X"
  have "e = e \<cdot> d"
    using A1 A2 by (simp add:r_identity_def)
  also have "\<dots> = d"
    using A0 A3 by (simp add:l_identity_def)
  finally show "e = d" .
qed

lemma id_elem_unique:"\<lbrakk>id_elem e1; id_elem e2; e1 \<in> X; e2 \<in> X\<rbrakk> \<Longrightarrow> e1 = e2"
  using l_r_identity_eq[of e1 e2] by (simp add:id_elem_def)

lemma id_commutes:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> commutes {e} X"
  by (auto simp:commutes_def id_elem_iff)

lemma id_elem_center:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> e \<in> center"
  by (simp add:center_mem_iff id_elem_iff)

lemma unital_magma_iff:"unital_magma X (\<cdot>) e \<longleftrightarrow> e \<in> X \<and> id_elem e"
  by (auto simp:unital_magma_def unital_magma_axioms_def magma_axioms id_elem_iff)

end

lemma (in unital_magma) unit_id_elem:"id_elem \<one>"
  by (simp add:id_elem_iff)

lemma (in unital_magma) id_elem_unit:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> e = \<one>"
  by (rule id_elem_unique[OF _ unit_id_elem _ unit_closed])

lemma (in unital_magma) unit_center:"\<one> \<in> center"
  by (rule id_elem_center[OF unit_id_elem unit_closed])


context magma
begin

definition l_trans::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "l_trans = (\<lambda>a\<in>X. \<lambda>x\<in>X. a \<cdot> x)"

definition r_trans::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "r_trans = (\<lambda>a\<in>X. \<lambda>x\<in>X. x \<cdot> a)"

lemma l_trans_app:"\<lbrakk>a \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> l_trans a x = a \<cdot> x"
  and r_trans_app:"\<lbrakk>a \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> r_trans a x = x \<cdot> a"
  by (simp_all add:l_trans_def r_trans_def)

lemma l_trans_und:"a \<notin> X \<Longrightarrow> l_trans a = undefined"
  and r_trans_und:"a \<notin> X \<Longrightarrow> r_trans a = undefined"
  by (simp_all add:l_trans_def r_trans_def)

lemma l_trans_und2:"\<lbrakk>a \<in> X; x \<notin> X\<rbrakk> \<Longrightarrow> l_trans a x = undefined"
  and r_trans_und2:"\<lbrakk>a \<in> X; x \<notin> X\<rbrakk> \<Longrightarrow> r_trans a x = undefined"
  by (simp_all add:l_trans_def r_trans_def)

lemma l_trans_maps:"a \<in> X \<Longrightarrow> l_trans a \<in> set_mor X X"
  and r_trans_maps:"a \<in> X \<Longrightarrow> r_trans a \<in> set_mor X X"
  by (auto simp:l_trans_def r_trans_def)

lemma l_trans_mem:"l_trans \<in> set_mor X (set_mor X X)"
  and r_trans_mem:"r_trans \<in> set_mor X (set_mor X X)"
  by (auto simp:l_trans_def r_trans_def)

lemma l_trans_r_trans:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> l_trans x y = r_trans y x"
  by (simp add:l_trans_def r_trans_def)

lemma id_elem_l_trans:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> l_trans e = Id X"
proof-
  assume A0:"id_elem e" and A1:"e \<in> X"
  have "l_trans e = (\<lambda>x\<in>X. e \<cdot> x)"
    using A1 by (simp add:l_trans_def)
  also have "\<dots> = Id X"
    by (rule restrict_ext) (simp add:id_elemE2[OF A0])
  finally show ?thesis .
qed

lemma id_elem_r_trans:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> r_trans e = Id X"
proof-
  assume A0:"id_elem e" and A1:"e \<in> X"
  have "r_trans e = (\<lambda>x\<in>X. x \<cdot> e)"
    using A1 by (simp add:r_trans_def)
  also have "\<dots> = Id X"
    by (rule restrict_ext) (simp add:id_elemE1[OF A0])
  finally show ?thesis .
qed

lemma id_elem_linj:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> inj_on (l_trans e) X"
  and id_elem_rinj:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> inj_on (r_trans e) X"
  by (simp_all add:id_elem_l_trans id_elem_r_trans)

definition l_cancellable::"'a \<Rightarrow> bool"
  where "l_cancellable a \<longleftrightarrow> a \<in> X \<and> (\<forall>x\<in>X. \<forall>y\<in>X. a \<cdot> x = a \<cdot> y \<longrightarrow> x = y)"

definition r_cancellable::"'a \<Rightarrow> bool"
  where "r_cancellable a \<longleftrightarrow> a \<in> X \<and> (\<forall>x\<in>X. \<forall>y\<in>X. x \<cdot> a = y \<cdot> a \<longrightarrow> x = y)"

definition cancellable::"'a \<Rightarrow> bool"
  where "cancellable a \<longleftrightarrow> l_cancellable a \<and> r_cancellable a"

lemma l_cancellableI1:"\<lbrakk>a \<in> X; \<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<cdot> x = a \<cdot> y\<rbrakk> \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> l_cancellable a"
  unfolding l_cancellable_def by blast

lemma r_cancellableI1:"\<lbrakk>a \<in> X; \<And>x y. \<lbrakk>x \<in> X; y \<in> X; x \<cdot> a = y \<cdot> a\<rbrakk> \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> r_cancellable a"
  unfolding r_cancellable_def by blast

lemma cancellableI1:
  "\<lbrakk>a \<in> X; \<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<cdot> x = a \<cdot> y\<rbrakk> \<Longrightarrow> x = y; \<And>x y. \<lbrakk>x \<in> X; y \<in> X; x \<cdot> a = y \<cdot> a\<rbrakk> \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> cancellable a"
  unfolding cancellable_def l_cancellable_def r_cancellable_def by blast

lemma cancellableI3:"\<lbrakk>l_cancellable a; r_cancellable a\<rbrakk> \<Longrightarrow> cancellable a"
  by (simp add:cancellable_def)

lemma l_cancellableD1:"l_cancellable a \<Longrightarrow> a \<in> X"
  and l_cancellableD2:"\<lbrakk>l_cancellable a; x \<in> X; y \<in> X; a \<cdot> x = a \<cdot> y\<rbrakk> \<Longrightarrow> x = y"
  unfolding l_cancellable_def by blast+

lemma r_cancellableD1:"r_cancellable a \<Longrightarrow> a \<in> X"
  and r_cancellableD2:"\<lbrakk>r_cancellable a; x \<in> X; y \<in> X; x \<cdot> a = y \<cdot> a\<rbrakk> \<Longrightarrow> x = y"
  unfolding r_cancellable_def by blast+

lemma cancellableD1:"cancellable a \<Longrightarrow> l_cancellable a"
  and cancellableD2:"cancellable a \<Longrightarrow> r_cancellable a"
  and cancellableD3:"cancellable a \<Longrightarrow> a \<in> X"
  by (simp_all add:cancellable_def l_cancellable_def)

lemma l_cancellable_iff_l_trans_inj:"a \<in> X \<Longrightarrow> l_cancellable a \<longleftrightarrow> inj_on (l_trans a) X"
  by (simp add:l_cancellable_def l_trans_def inj_on_def)

lemma r_cancellable_iff_r_trans_inj:"a \<in> X \<Longrightarrow> r_cancellable a \<longleftrightarrow> inj_on (r_trans a) X"
  by (simp add:r_cancellable_def r_trans_def inj_on_def)

lemma cancellable_iff_trans_inj:"a \<in> X \<Longrightarrow> cancellable a \<longleftrightarrow> inj_on (l_trans a) X \<and> inj_on (r_trans a) X"
  by (simp add:cancellable_def l_cancellable_iff_l_trans_inj r_cancellable_iff_r_trans_inj)

lemma l_cancellableI2:"\<lbrakk>a \<in> X; inj_on (l_trans a) X\<rbrakk> \<Longrightarrow> l_cancellable a"
  by (simp add:l_cancellable_iff_l_trans_inj)

lemma r_cancellableI2:"\<lbrakk>a \<in> X; inj_on (r_trans a) X\<rbrakk> \<Longrightarrow> r_cancellable a"
  by (simp add:r_cancellable_iff_r_trans_inj)

lemma cancellableI2:"\<lbrakk>a \<in> X; inj_on (l_trans a) X; inj_on (r_trans a) X\<rbrakk> \<Longrightarrow> cancellable a"
  by (simp add:cancellable_iff_trans_inj)

lemma l_cancellableD3:"l_cancellable a \<Longrightarrow> inj_on (l_trans a) X"
proof-
  assume A0:"l_cancellable a"
  then show "inj_on (l_trans a) X"
    using l_cancellable_iff_l_trans_inj[OF l_cancellableD1[OF A0]] by simp
qed

lemma r_cancellableD3:"r_cancellable a \<Longrightarrow> inj_on (r_trans a) X"
proof-
  assume A0:"r_cancellable a"
  then show "inj_on (r_trans a) X"
    using r_cancellable_iff_r_trans_inj[OF r_cancellableD1[OF A0]] by simp
qed

lemma id_elem_cancellable:"\<lbrakk>id_elem e; e \<in> X\<rbrakk> \<Longrightarrow> cancellable e"
  by (simp add:cancellable_iff_trans_inj id_elem_linj id_elem_rinj)

end

lemma (in unital_magma) unit_cancellable:"cancellable \<one>"
  by (rule id_elem_cancellable[OF unit_id_elem unit_closed])

lemma (in unital_magma) unit_l_trans:"l_trans \<one> = Id X"
  and unit_r_trans:"r_trans \<one> = Id X"
  by (simp_all add:id_elem_l_trans id_elem_r_trans unit_id_elem)


context magma
begin

definition r_coset::"'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "r_coset H a = (\<Union>h\<in>H. {h \<cdot> a})"

definition l_coset::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "l_coset a H = (\<Union>h\<in>H. {a \<cdot> h})"

definition r_cosets::"'a set \<Rightarrow> 'a set set"
  where "r_cosets H = (\<Union>a\<in>X. {r_coset H a})"

definition l_cosets::"'a set \<Rightarrow> 'a set set"
  where "l_cosets H = (\<Union>a\<in>X. {l_coset a H})"

definition set_prod::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "set_prod H K = (\<Union>h\<in>H. \<Union>k\<in>K. {h \<cdot> k})"

lemma r_coset_iff:"x \<in> r_coset H a \<longleftrightarrow> (\<exists>h\<in>H. x = h \<cdot> a)"
  and l_coset_iff:"x \<in> l_coset a H \<longleftrightarrow> (\<exists>h\<in>H. x = a \<cdot> h)"
  and set_prod_iff:"x \<in> set_prod H K \<longleftrightarrow> (\<exists>h\<in>H. \<exists>k\<in>K. x = h \<cdot> k)"
  by (auto simp:r_coset_def l_coset_def set_prod_def)

lemma r_coset_memI1:"\<exists>h\<in>H. x = h \<cdot> a \<Longrightarrow> x \<in> r_coset H a"
  and r_coset_memI2:"\<lbrakk>h \<in> H; x = h \<cdot> a\<rbrakk> \<Longrightarrow> x \<in> r_coset H a"
  and l_coset_memI1:"\<exists>h\<in>H. x = a \<cdot> h \<Longrightarrow> x \<in> l_coset a H"
  and l_coset_memI2:"\<lbrakk>h \<in> H; x = a \<cdot> h\<rbrakk> \<Longrightarrow> x \<in> l_coset a H"
  by (auto simp:r_coset_def l_coset_def)

lemma r_coset_memI[intro]:"h \<in> H \<Longrightarrow> h \<cdot> x \<in> r_coset H x"
  and l_coset_memI[intro]:"h \<in> H \<Longrightarrow> x \<cdot> h \<in> l_coset x H"
  and set_prod_memI[intro]:"\<lbrakk>h \<in> H; k \<in> K\<rbrakk> \<Longrightarrow> h \<cdot> k \<in> set_prod H K"
  by (auto simp:r_coset_def l_coset_def set_prod_def)

lemma r_coset_memE[elim]:"\<lbrakk>a \<in> r_coset H x; \<And>h. \<lbrakk>h \<in> H; a = h \<cdot> x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and l_coset_memE[elim]:"\<lbrakk>a \<in> l_coset x H; \<And>h. \<lbrakk>h \<in> H; a = x \<cdot> h\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and set_prod_memE[elim]:"\<lbrakk>a \<in> set_prod H K; \<And>h k. \<lbrakk>h \<in> H; k \<in> K; a = h \<cdot> k\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:r_coset_def l_coset_def set_prod_def)

lemma r_coset_singleton_prod:"r_coset H a = set_prod H {a}"
  and l_coset_singleton_prod:"l_coset a H = set_prod {a} H"
  by (auto simp:r_coset_def l_coset_def set_prod_def)

lemma set_prod_closed:"\<lbrakk>A \<subseteq> X; B \<subseteq> X\<rbrakk> \<Longrightarrow> set_prod A B \<subseteq> X"
  by (auto simp:set_prod_def)

lemma r_coset_sub:"\<lbrakk>A \<subseteq> X; x \<in> X\<rbrakk> \<Longrightarrow> r_coset A x \<subseteq> X"
  and l_coset_sub:"\<lbrakk>A \<subseteq> X; x \<in> X\<rbrakk> \<Longrightarrow> l_coset x A \<subseteq> X"
  by (auto simp:r_coset_def l_coset_def)

lemma r_cosets_memI:"a \<in> X \<Longrightarrow> r_coset H a \<in> r_cosets H"
  and l_cosets_memI:"a \<in> X \<Longrightarrow> l_coset a H \<in> l_cosets H"
  by (auto simp:r_cosets_def l_cosets_def)

lemma r_cosets_memE:"\<lbrakk>C \<in> r_cosets H; \<And>a. \<lbrakk>a \<in> X; C = r_coset H a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and l_cosets_memE:"\<lbrakk>C \<in> l_cosets H; \<And>a. \<lbrakk>a \<in> X; C = l_coset a H\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:r_cosets_def l_cosets_def)

lemma r_cosets_sub:"A \<subseteq> X \<Longrightarrow> r_cosets A \<subseteq> Pow X"
  and l_cosets_sub:"A \<subseteq> X \<Longrightarrow> l_cosets A \<subseteq> Pow X"
  by (auto simp:r_cosets_def l_cosets_def r_coset_sub l_coset_sub)

lemma set_prod_mono:"\<lbrakk>A \<subseteq> A'; B \<subseteq> B'\<rbrakk> \<Longrightarrow> set_prod A B \<subseteq> set_prod A' B'"
  by (auto simp:set_prod_def)

lemma set_prod_Un1:"set_prod (A \<union> A') B = set_prod A B \<union> set_prod A' B"
  and set_prod_Un2:"set_prod A (B \<union> B') = set_prod A B \<union> set_prod A B'"
  by (auto simp:set_prod_def)

lemma set_prod_UN1:"set_prod (\<Union>\<A>) B = (\<Union>A\<in>\<A>. set_prod A B)"
  and set_prod_UN2:"set_prod A (\<Union>\<B>) = (\<Union>B\<in>\<B>. set_prod A B)"
  by (auto simp:set_prod_def)

lemma set_prod_empty:"set_prod {} B = {}" and set_prod_empty2:"set_prod A {} = {}"
  by (simp_all add:set_prod_def)

lemma subs_iff_set_prod:"A \<in> subs \<longleftrightarrow> A \<subseteq> X \<and> set_prod A A \<subseteq> A"
  by (auto simp:subs_def set_prod_def)

lemma set_prod_lcosets:"set_prod A B = (\<Union>a\<in>A. l_coset a B)"
  and set_prod_rcosets:"set_prod A B = (\<Union>b\<in>B. r_coset A b)"
  by (auto simp:set_prod_def l_coset_def r_coset_def)

lemma l_coset_l_trans:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> l_coset a H = l_trans a ` H"
  and r_coset_r_trans:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> r_coset H a = r_trans a ` H"
  by (auto simp:l_coset_def r_coset_def l_trans_def r_trans_def)

end


context magma
begin

definition l_cong::"'a rel \<Rightarrow> bool"
  where "l_cong R \<longleftrightarrow> (\<forall>a\<in>X. \<forall>(x, y)\<in>R. (a \<cdot> x, a \<cdot> y) \<in> R)"

definition r_cong::"'a rel \<Rightarrow> bool"
  where "r_cong R \<longleftrightarrow> (\<forall>a\<in>X. \<forall>(x, y)\<in>R. (x \<cdot> a, y \<cdot> a) \<in> R)"

definition cong::"'a rel \<Rightarrow> bool"
  where "cong R \<longleftrightarrow> (\<forall>(x1, x2)\<in>R. \<forall>(y1, y2)\<in>R. (x1 \<cdot> y1, x2 \<cdot> y2) \<in> R)"

lemma l_congI1:"(\<And>a x y. \<lbrakk>a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (a \<cdot> x, a \<cdot> y) \<in> R) \<Longrightarrow> l_cong R"
  by (auto simp:l_cong_def)

lemma r_congI1:"(\<And>a x y. \<lbrakk>a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> a, y \<cdot> a) \<in> R) \<Longrightarrow> r_cong R"
  by (auto simp:r_cong_def)

lemma congI1:"(\<And>x1 x2 y1 y2. \<lbrakk>(x1, x2) \<in> R; (y1, y2) \<in> R\<rbrakk> \<Longrightarrow> (x1 \<cdot> y1, x2 \<cdot> y2) \<in> R) \<Longrightarrow> cong R"
  by (auto simp:cong_def)

lemma congD1:"\<lbrakk>cong R; (x1, x2) \<in> R; (y1, y2) \<in> R\<rbrakk> \<Longrightarrow> (x1 \<cdot> y1, x2 \<cdot> y2) \<in> R"
  by (auto simp:cong_def)

lemma l_congD1:"\<lbrakk>l_cong R; a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (a \<cdot> x, a \<cdot> y) \<in> R"
  by (auto simp:l_cong_def)

lemma r_congD1:"\<lbrakk>r_cong R; a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> a, y \<cdot> a) \<in> R"
  by (auto simp:r_cong_def)

lemma congDL:"\<lbrakk>refl_on X R; cong R; a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (a \<cdot> x, a \<cdot> y) \<in> R"
  using congD1[of R a a x y] by (auto simp:refl_on_def)

lemma congDR:"\<lbrakk>refl_on X R; cong R; a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> a, y \<cdot> a) \<in> R"
  using congD1[of R x y a a] by (auto simp:refl_on_def)

lemma l_congI2:"\<lbrakk>refl_on X R; cong R\<rbrakk> \<Longrightarrow> l_cong R"
  by (rule l_congI1, rule congDL)

lemma r_congI2:"\<lbrakk>refl_on X R; cong R\<rbrakk> \<Longrightarrow> r_cong R"
  by (rule r_congI1, rule congDR)

lemma congI2:"\<lbrakk>equiv X R; l_cong R; r_cong R\<rbrakk> \<Longrightarrow> cong R"
proof(rule congI1)
  fix x1 x2 y1 y2 assume A0:"equiv X R" and A1:"l_cong R" and A2:"r_cong R" and A3:"(x1, x2) \<in> R" and A4:"(y1, y2) \<in> R"
  have B0:"R \<subseteq> X \<times> X" and B1:"\<And>x y z. \<lbrakk>(x, y) \<in> R; (y, z) \<in> R\<rbrakk> \<Longrightarrow> (x, z) \<in> R"
    using A0 unfolding equiv_def refl_on_def trans_def by blast+
  have B2:"x1 \<in> X" and B3:"y2 \<in> X"
    using A3 A4 B0 by auto
  have "(x1 \<cdot> y1, x1 \<cdot> y2) \<in> R"
    by (rule l_congD1[OF A1 B2 A4])
  moreover have "(x1 \<cdot> y2, x2 \<cdot> y2) \<in> R"
    by (rule r_congD1[OF A2 B3 A3])
  ultimately show "(x1 \<cdot> y1, x2 \<cdot> y2) \<in> R"
    by (rule B1)
qed

lemma congruenceI:
  assumes A0:"equiv X R" and A1:"l_cong R" and A2:"r_cong R"
  shows "congruence X (\<cdot>) R"
proof-
  have B0:"R \<subseteq> X \<times> X" and B1:"\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> R" and B2:"\<And>x y. (x, y) \<in> R \<Longrightarrow> (y, x) \<in> R" and
       B3:"\<And>x y z. \<lbrakk>(x, y) \<in> R; (y, z) \<in> R\<rbrakk> \<Longrightarrow> (x, z) \<in> R"
    using A0 unfolding equiv_def refl_on_def sym_def trans_def by blast+
  have B4:"cong R"
    by (rule congI2[OF A0 A1 A2])
  show ?thesis
  proof(unfold_locales)
    show "R \<subseteq> X \<times> X" by (rule B0)
    show "\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> R" by (rule B1)
    show "\<And>x y. (x, y) \<in> R \<Longrightarrow> (y, x) \<in> R" by (rule B2)
    show "\<And>x y z. \<lbrakk>(x, y) \<in> R; (y, z) \<in> R\<rbrakk> \<Longrightarrow> (x, z) \<in> R" by (rule B3)
    show "\<And>x x' y y'. \<lbrakk>(x, x') \<in> R; (y, y') \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> y, x' \<cdot> y') \<in> R" by (rule congD1[OF B4])
  qed
qed

lemma congruence_iff:"congruence X (\<cdot>) R \<longleftrightarrow> equiv X R \<and> cong R"
proof
  assume "congruence X (\<cdot>) R"
  then interpret congruence X "(\<cdot>)" R .
  show "equiv X R \<and> cong R"
    using equiv by (auto simp:cong_def R_compat)
next
  assume A0:"equiv X R \<and> cong R"
  then have B0:"refl_on X R"
    by (simp add:equiv_def)
  show "congruence X (\<cdot>) R"
    using A0 by (intro congruenceI l_congI2[OF B0] r_congI2[OF B0]) simp_all
qed

lemma congs_iff:"R \<in> congs \<longleftrightarrow> equiv X R \<and> cong R"
  by (simp add:congs_def congruence_iff)

lemma congs_sub_equivs:"congs \<subseteq> equivs X"
  by (auto simp:congs_iff equivs_def)

theorem liftable_iff_congruence:
  assumes A0:"equiv X R"
  shows "(\<exists>q. magma_hom X (\<cdot>) (X // R) q (Equiv_Relations.proj R)) \<longleftrightarrow> congruence X (\<cdot>) R"
proof
  assume "\<exists>q. magma_hom X (\<cdot>) (X // R) q (Equiv_Relations.proj R)"
  then obtain q where B0:"magma_hom X (\<cdot>) (X // R) q (Equiv_Relations.proj R)"
    by blast
  have B1:"R \<subseteq> X \<times> X"
    using A0 unfolding equiv_def refl_on_def by blast
  have B2:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Equiv_Relations.proj R x = Equiv_Relations.proj R y \<longleftrightarrow> (x, y) \<in> R"
    by (simp add:proj_iff[OF A0])
  show "congruence X (\<cdot>) R"
  proof(rule congruenceI[OF A0])
    show "l_cong R"
    proof(rule l_congI1)
      fix a x y assume C0:"a \<in> X" and C1:"(x, y) \<in> R"
      have C2:"x \<in> X" "y \<in> X"
        using B1 C1 by auto
      have "Equiv_Relations.proj R (a \<cdot> x) = q (Equiv_Relations.proj R a) (Equiv_Relations.proj R x)"
        by (rule magma_hom.hom[OF B0 C0 C2(1)])
      also have "\<dots> = q (Equiv_Relations.proj R a) (Equiv_Relations.proj R y)"
        using B2[OF C2] C1 by simp
      also have "\<dots> = Equiv_Relations.proj R (a \<cdot> y)"
        by (rule magma_hom.hom[OF B0 C0 C2(2), symmetric])
      finally show "(a \<cdot> x, a \<cdot> y) \<in> R"
        using B2[OF closed[OF C0 C2(1)] closed[OF C0 C2(2)]] by simp
    qed
    show "r_cong R"
    proof(rule r_congI1)
      fix a x y assume C0:"a \<in> X" and C1:"(x, y) \<in> R"
      have C2:"x \<in> X" "y \<in> X"
        using B1 C1 by auto
      have "Equiv_Relations.proj R (x \<cdot> a) = q (Equiv_Relations.proj R x) (Equiv_Relations.proj R a)"
        by (rule magma_hom.hom[OF B0 C2(1) C0])
      also have "\<dots> = q (Equiv_Relations.proj R y) (Equiv_Relations.proj R a)"
        using B2[OF C2] C1 by simp
      also have "\<dots> = Equiv_Relations.proj R (y \<cdot> a)"
        by (rule magma_hom.hom[OF B0 C2(2) C0, symmetric])
      finally show "(x \<cdot> a, y \<cdot> a) \<in> R"
        using B2[OF closed[OF C2(1) C0] closed[OF C2(2) C0]] by simp
    qed
  qed
next
  assume "congruence X (\<cdot>) R"
  then interpret congruence X "(\<cdot>)" R .
  have "magma_hom X (\<cdot>) (X // R) (\<bullet>) (Equiv_Relations.proj R)"
    using proj_hom by (simp add:quot_eq cls_eq_proj)
  then show "\<exists>q. magma_hom X (\<cdot>) (X // R) q (Equiv_Relations.proj R)"
    by blast
qed

end


context congruence
begin

lemma l_compat:"\<lbrakk>a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (a \<cdot> x, a \<cdot> y) \<in> R"
  by (intro R_compat R_refl)

lemma r_compat:"\<lbrakk>a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> a, y \<cdot> a) \<in> R"
  by (intro R_compat R_refl)

lemma R_l_cong:"l_cong R"
  by (rule l_congI1) (rule l_compat)

lemma R_r_cong:"r_cong R"
  by (rule r_congI1) (rule r_compat)

lemma R_cong:"cong R"
  by (rule congI1) (rule R_compat)

lemma l_trans_compat:"\<lbrakk>a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (l_trans a x, l_trans a y) \<in> R"
  and r_trans_compat:"\<lbrakk>a \<in> X; (x, y) \<in> R\<rbrakk> \<Longrightarrow> (r_trans a x, r_trans a y) \<in> R"
  using R_carrier by (auto simp:l_trans_def r_trans_def l_compat r_compat)

lemma cls_mem:"x \<in> X \<Longrightarrow> x \<in> cls x"
  by (simp add:cls_def R_refl)

lemma cls_sub:"cls x \<subseteq> X"
  using R_carrier by (auto simp:cls_def)

lemma quot_sub:"quot \<subseteq> Pow X"
  using cls_sub by (auto simp:quot_def)

lemma cls_set_prod:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> set_prod (cls x) (cls y) \<subseteq> cls (x \<cdot> y)"
proof
  fix z assume A0:"x \<in> X" and A1:"y \<in> X" and A2:"z \<in> set_prod (cls x) (cls y)"
  obtain a b where B0:"a \<in> cls x" and B1:"b \<in> cls y" and B2:"z = a \<cdot> b"
    using A2 by (rule set_prod_memE)
  have "(x \<cdot> y, a \<cdot> b) \<in> R"
    using B0 B1 by (intro R_compat) (simp_all add:cls_def)
  then show "z \<in> cls (x \<cdot> y)"
    by (simp add:cls_def B2)
qed

lemma qmul_set_prod:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> cls x \<bullet> cls y = \<Union>(cls ` set_prod (cls x) (cls y))"
  by (auto simp:qmul_def set_prod_def)

lemma opp_congruence:"congruence X (\<lambda>x y. y \<cdot> x) R"
proof(unfold_locales)
  show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> y \<cdot> x \<in> X" by simp
  show "R \<subseteq> X \<times> X" by (rule R_carrier)
  show "\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> R" by (rule R_refl)
  show "\<And>x y. (x, y) \<in> R \<Longrightarrow> (y, x) \<in> R" by (rule R_sym)
  show "\<And>x y z. \<lbrakk>(x, y) \<in> R; (y, z) \<in> R\<rbrakk> \<Longrightarrow> (x, z) \<in> R" by (rule R_trans)
  show "\<And>x x' y y'. \<lbrakk>(x, x') \<in> R; (y, y') \<in> R\<rbrakk> \<Longrightarrow> (y \<cdot> x, y' \<cdot> x') \<in> R" by (rule R_compat)
qed

end

lemma (in magma) opp_congruence_iff:"congruence X (\<lambda>x y. y \<cdot> x) R \<longleftrightarrow> congruence X (\<cdot>) R"
proof
  assume "congruence X (\<lambda>x y. y \<cdot> x) R"
  then interpret o:congruence X "\<lambda>x y. y \<cdot> x" R .
  show "congruence X (\<cdot>) R"
    by (rule o.opp_congruence)
qed (rule congruence.opp_congruence)


locale action =
  fixes \<Omega>::"'a set" and E::"'b set" and \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes act_closed[simp, intro]:"\<lbrakk>\<omega> \<in> \<Omega>; x \<in> E\<rbrakk> \<Longrightarrow> \<alpha> \<omega> x \<in> E"
begin

definition l_law::"'a \<Rightarrow> 'b \<Rightarrow> 'b"
  where "l_law = (\<lambda>\<omega>\<in>\<Omega>. \<lambda>x\<in>E. \<alpha> \<omega> x)"

definition r_law::"'b \<Rightarrow> 'a \<Rightarrow> 'b"
  where "r_law = (\<lambda>x\<in>E. \<lambda>\<omega>\<in>\<Omega>. \<alpha> \<omega> x)"

lemma l_law_app:"\<lbrakk>\<omega> \<in> \<Omega>; x \<in> E\<rbrakk> \<Longrightarrow> l_law \<omega> x = \<alpha> \<omega> x"
  and r_law_app:"\<lbrakk>\<omega> \<in> \<Omega>; x \<in> E\<rbrakk> \<Longrightarrow> r_law x \<omega> = \<alpha> \<omega> x"
  by (simp_all add:l_law_def r_law_def)

lemma l_law_und:"\<omega> \<notin> \<Omega> \<Longrightarrow> l_law \<omega> = undefined"
  and r_law_und:"x \<notin> E \<Longrightarrow> r_law x = undefined"
  by (simp_all add:l_law_def r_law_def)

lemma l_law_maps:"\<omega> \<in> \<Omega> \<Longrightarrow> l_law \<omega> \<in> set_mor E E"
  and r_law_maps:"x \<in> E \<Longrightarrow> r_law x \<in> set_mor \<Omega> E"
  by (auto simp:l_law_def r_law_def)

lemma l_law_mem:"l_law \<in> set_mor \<Omega> (set_mor E E)"
  and r_law_mem:"r_law \<in> set_mor E (set_mor \<Omega> E)"
  by (auto simp:l_law_def r_law_def)

definition orbit::"'b \<Rightarrow> 'b set"
  where "orbit x = (\<Union>\<omega>\<in>\<Omega>. {\<alpha> \<omega> x})"

definition stabilizer::"'b \<Rightarrow> 'a set"
  where "stabilizer x = {\<omega> \<in> \<Omega>. \<alpha> \<omega> x = x}"

definition fixed_points::"'b set"
  where "fixed_points = {x \<in> E. \<forall>\<omega>\<in>\<Omega>. \<alpha> \<omega> x = x}"

definition invariant::"'b set \<Rightarrow> bool"
  where "invariant A \<longleftrightarrow> A \<subseteq> E \<and> (\<forall>\<omega>\<in>\<Omega>. \<forall>x\<in>A. \<alpha> \<omega> x \<in> A)"

lemma orbit_iff:"y \<in> orbit x \<longleftrightarrow> (\<exists>\<omega>\<in>\<Omega>. y = \<alpha> \<omega> x)"
  by (auto simp:orbit_def)

lemma orbit_sub:"x \<in> E \<Longrightarrow> orbit x \<subseteq> E"
  by (auto simp:orbit_def)

lemma stabilizer_sub:"stabilizer x \<subseteq> \<Omega>"
  by (auto simp:stabilizer_def)

lemma fixed_points_sub:"fixed_points \<subseteq> E"
  by (auto simp:fixed_points_def)

lemma invariantI:"\<lbrakk>A \<subseteq> E; \<And>\<omega> x. \<lbrakk>\<omega> \<in> \<Omega>; x \<in> A\<rbrakk> \<Longrightarrow> \<alpha> \<omega> x \<in> A\<rbrakk> \<Longrightarrow> invariant A"
  and invariantD1:"invariant A \<Longrightarrow> A \<subseteq> E"
  and invariantD2:"\<lbrakk>invariant A; \<omega> \<in> \<Omega>; x \<in> A\<rbrakk> \<Longrightarrow> \<alpha> \<omega> x \<in> A"
  by (auto simp:invariant_def)

lemma invariant_whole:"invariant E"
  by (auto simp:invariant_def)

lemma invariant_Inter:
  assumes A0:"\<A> \<subseteq> {A. invariant A}" and A1:"\<A> \<noteq> {}"
  shows "invariant (\<Inter>\<A>)"
proof(rule invariantI)
  obtain A where B0:"A \<in> \<A>"
    using A1 by blast
  then have "A \<subseteq> E"
    using A0 by (auto simp:invariant_def)
  then show "\<Inter>\<A> \<subseteq> E"
    using B0 by blast
  fix \<omega> x assume C0:"\<omega> \<in> \<Omega>" and C1:"x \<in> \<Inter>\<A>"
  show "\<alpha> \<omega> x \<in> \<Inter>\<A>"
  proof
    fix B assume "B \<in> \<A>"
    then have "invariant B" and "x \<in> B"
      using A0 C1 by auto
    then show "\<alpha> \<omega> x \<in> B"
      using C0 by (simp add:invariant_def)
  qed
qed

lemma invariant_Union:
  assumes A0:"\<A> \<subseteq> {A. invariant A}"
  shows "invariant (\<Union>\<A>)"
proof(rule invariantI)
  show "\<Union>\<A> \<subseteq> E"
    using A0 by (auto simp:invariant_def)
  fix \<omega> x assume C0:"\<omega> \<in> \<Omega>" and C1:"x \<in> \<Union>\<A>"
  then obtain B where B0:"B \<in> \<A>" and B1:"x \<in> B"
    by blast
  then have "\<alpha> \<omega> x \<in> B"
    using A0 C0 by (auto simp:invariant_def)
  then show "\<alpha> \<omega> x \<in> \<Union>\<A>"
    using B0 by blast
qed

lemma invariant_orbit:"invariant A \<longleftrightarrow> A \<subseteq> E \<and> (\<forall>x\<in>A. orbit x \<subseteq> A)"
  by (auto simp:invariant_def orbit_def)

lemma invariants_moore:"moore_family E {A. invariant A}"
proof(unfold_locales)
  show "{A. invariant A} \<subseteq> Pow E"
    by (auto simp:invariant_def)
  show "E \<in> {A. invariant A}"
    by (simp add:invariant_whole)
  show "\<And>\<A>. \<lbrakk>\<A> \<subseteq> {A. invariant A}; \<A> \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>\<A> \<in> {A. invariant A}"
    by (simp add:invariant_Inter)
qed

lemma sub_action:"invariant A \<Longrightarrow> action \<Omega> A \<alpha>"
  by unfold_locales (simp add:invariantD2)

end


sublocale magma \<subseteq> l_action:action X X "(\<cdot>)"
  by unfold_locales simp

sublocale magma \<subseteq> r_action:action X X "\<lambda>a x. x \<cdot> a"
  by unfold_locales simp

context magma
begin

lemma l_trans_l_law:"l_trans = l_action.l_law"
  and r_trans_r_law:"r_trans = l_action.r_law"
  and r_trans_l_law:"r_trans = r_action.l_law"
  and l_trans_r_law:"l_trans = r_action.r_law"
  by (simp_all add:l_trans_def r_trans_def l_action.l_law_def l_action.r_law_def r_action.l_law_def r_action.r_law_def)

lemma l_action_orbit:"x \<in> X \<Longrightarrow> l_action.orbit x = r_coset X x"
  and r_action_orbit:"x \<in> X \<Longrightarrow> r_action.orbit x = l_coset x X"
  by (auto simp:l_action.orbit_def r_action.orbit_def r_coset_def l_coset_def)

lemma l_action_invariant:"l_action.invariant A \<longleftrightarrow> A \<subseteq> X \<and> set_prod X A \<subseteq> A"
  and r_action_invariant:"r_action.invariant A \<longleftrightarrow> A \<subseteq> X \<and> set_prod A X \<subseteq> A"
  by (auto simp:l_action.invariant_def r_action.invariant_def set_prod_def)

end


sublocale magma \<subseteq> opp:magma X "\<lambda>x y. y \<cdot> x"
  by unfold_locales simp

context magma
begin

lemma opp_subs:"opp.subs = subs"
  by (auto simp:opp.subs_def subs_def)

lemma opp_congs:"opp.congs = congs"
  by (simp add:opp.congs_def congs_def opp_congruence_iff)

lemma opp_commutes:"opp.commutes A B \<longleftrightarrow> commutes B A"
  by (auto simp:opp.commutes_def commutes_def)

lemma opp_centralizer:"opp.centralizer E = centralizer E"
  by (auto simp:opp.centralizer_def centralizer_def)

lemma opp_center:"opp.center = center"
  by (simp add:opp.center_def center_def opp_centralizer)

lemma opp_l_identity:"opp.l_identity e \<longleftrightarrow> r_identity e"
  and opp_r_identity:"opp.r_identity e \<longleftrightarrow> l_identity e"
  and opp_id_elem:"opp.id_elem e \<longleftrightarrow> id_elem e"
  by (auto simp:opp.l_identity_def opp.r_identity_def opp.id_elem_def l_identity_def r_identity_def id_elem_def)

lemma opp_l_trans:"opp.l_trans = r_trans"
  and opp_r_trans:"opp.r_trans = l_trans"
  by (simp_all add:opp.l_trans_def opp.r_trans_def l_trans_def r_trans_def)

lemma opp_l_cancellable:"opp.l_cancellable a \<longleftrightarrow> r_cancellable a"
  and opp_r_cancellable:"opp.r_cancellable a \<longleftrightarrow> l_cancellable a"
  and opp_cancellable:"opp.cancellable a \<longleftrightarrow> cancellable a"
  by (auto simp:opp.l_cancellable_def opp.r_cancellable_def opp.cancellable_def l_cancellable_def r_cancellable_def cancellable_def)

lemma opp_l_coset:"opp.l_coset a H = r_coset H a"
  and opp_r_coset:"opp.r_coset H a = l_coset a H"
  and opp_set_prod:"opp.set_prod A B = set_prod B A"
  by (auto simp:opp.l_coset_def opp.r_coset_def opp.set_prod_def l_coset_def r_coset_def set_prod_def)

lemma opp_l_cosets:"opp.l_cosets H = r_cosets H"
  and opp_r_cosets:"opp.r_cosets H = l_cosets H"
  by (simp_all add:opp.l_cosets_def opp.r_cosets_def l_cosets_def r_cosets_def opp_l_coset opp_r_coset)

end


context magma_hom
begin

lemma im_sub:"f ` X \<in> cod.subs"
  by (rule image_sub[OF dom.sub.whole])

lemma im_closed:"\<lbrakk>y1 \<in> f ` X; y2 \<in> f ` X\<rbrakk> \<Longrightarrow> y1 \<star> y2 \<in> f ` X"
  by (rule cod.subsD(2)[OF im_sub])

lemma im_magma:"magma (f ` X) (\<star>)"
  by (rule cod.sub_magma[OF im_sub])

lemma unit_image_idempotent:"\<lbrakk>e \<in> X; dom.id_elem e\<rbrakk> \<Longrightarrow> f e \<star> f e = f e"
  using hom[of e e] dom.id_elemE1[of e e] by simp

lemma unit_image_cancellable:
  assumes A0:"e \<in> X" and A1:"dom.id_elem e" and A2:"d \<in> Y" and A3:"cod.id_elem d" and A4:"cod.l_cancellable (f e)"
  shows "f e = d"
proof-
  have B0:"f e \<star> f e = f e \<star> d"
    using unit_image_idempotent[OF A0 A1] cod.id_elemE1[OF A3 maps[OF A0]] by simp
  then show "f e = d"
    by (rule cod.l_cancellableD2[OF A4 maps[OF A0] A2])
qed

lemma unit_image_surj:
  assumes A0:"e \<in> X" and A1:"dom.id_elem e" and A2:"f ` X = Y"
  shows "cod.id_elem (f e)"
proof(rule cod.id_elemI1)
  fix b assume "b \<in> Y"
  then obtain x where B0:"x \<in> X" and B1:"b = f x"
    using A2 by blast
  show "b \<star> f e = b"
    using hom[OF B0 A0] dom.id_elemE1[OF A1 B0] B1 by simp
  show "f e \<star> b = b"
    using hom[OF A0 B0] dom.id_elemE2[OF A1 B0] B1 by simp
qed

lemma commutes_image:
  assumes A0:"A \<subseteq> X" and A1:"B \<subseteq> X" and A2:"dom.commutes A B"
  shows "cod.commutes (f ` A) (f ` B)"
proof(rule cod.commutesI)
  fix a' b' assume "a' \<in> f ` A" and "b' \<in> f ` B"
  then obtain a b where B0:"a \<in> A" and B1:"b \<in> B" and B2:"a' = f a" and B3:"b' = f b"
    by blast
  have B4:"a \<in> X" and B5:"b \<in> X"
    using A0 A1 B0 B1 by auto
  show "a' \<star> b' = b' \<star> a'"
    using hom[OF B4 B5] hom[OF B5 B4] dom.commutesD[OF A2 B0 B1] by (simp add:B2 B3)
qed

lemma centralizer_image:
  assumes A0:"A \<subseteq> X"
  shows "f ` dom.centralizer A \<subseteq> cod.centralizer (f ` A)"
proof(rule cod.commutes_sub_centralizer1)
  show "f ` dom.centralizer A \<subseteq> Y"
    using dom.centralizer_sub by auto
  show "cod.commutes (f ` A) (f ` dom.centralizer A)"
    by (rule commutes_image[OF A0 dom.centralizer_sub dom.centralizer_commutes1])
qed

lemma hom_set_prod:"\<lbrakk>A \<subseteq> X; B \<subseteq> X\<rbrakk> \<Longrightarrow> f ` dom.set_prod A B = cod.set_prod (f ` A) (f ` B)"
proof
  assume A0:"A \<subseteq> X" and A1:"B \<subseteq> X"
  show "f ` dom.set_prod A B \<subseteq> cod.set_prod (f ` A) (f ` B)"
  proof
    fix y assume "y \<in> f ` dom.set_prod A B"
    then obtain a b where B0:"a \<in> A" "b \<in> B" "y = f (a \<cdot> b)"
      by blast
    then show "y \<in> cod.set_prod (f ` A) (f ` B)"
      using A0 A1 by (auto simp:hom subset_iff)
  qed
  show "cod.set_prod (f ` A) (f ` B) \<subseteq> f ` dom.set_prod A B"
  proof
    fix y assume "y \<in> cod.set_prod (f ` A) (f ` B)"
    then obtain a b where B0:"a \<in> A" "b \<in> B" "y = f a \<star> f b"
      by blast
    then have "y = f (a \<cdot> b)"
      using A0 A1 by (auto simp:hom subset_iff)
    then show "y \<in> f ` dom.set_prod A B"
      using B0 by blast
  qed
qed

lemma hom_l_coset:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> f ` dom.l_coset a H = cod.l_coset (f a) (f ` H)"
  and hom_r_coset:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> f ` dom.r_coset H a = cod.r_coset (f ` H) (f a)"
  by (simp_all add:dom.l_coset_singleton_prod cod.l_coset_singleton_prod dom.r_coset_singleton_prod cod.r_coset_singleton_prod hom_set_prod)

end


lemma magma_hom_compose:
  assumes A0:"magma_hom X mul Y mul' f" and A1:"magma_hom Y mul' Z mul'' g"
  shows "magma_hom X mul Z mul'' (g \<circ> f)"
proof-
  interpret f:magma_hom X mul Y mul' f by (rule A0)
  interpret g:magma_hom Y mul' Z mul'' g by (rule A1)
  show ?thesis
    by unfold_locales (simp_all add:f.hom g.hom)
qed

lemma magma_hom_id:"magma X mul \<Longrightarrow> magma_hom X mul X mul id"
proof-
  assume "magma X mul"
  then interpret magma X mul .
  show ?thesis
    by unfold_locales simp_all
qed

context magma_hom
begin

lemma factor_mono:
  fixes Z::"'c set" and zmul::"'c \<Rightarrow> 'c \<Rightarrow> 'c" (infixl "\<bullet>" 70) and g::"'c \<Rightarrow> 'b"
  assumes A0:"magma_hom Z (\<bullet>) Y (\<star>) g" and A1:"inj_on g Z" and A2:"f ` X \<subseteq> g ` Z"
  obtains h where "magma_hom X (\<cdot>) Z (\<bullet>) h" and "\<And>x. x \<in> X \<Longrightarrow> g (h x) = f x"
proof-
  interpret g:magma_hom Z "(\<bullet>)" Y "(\<star>)" g by (rule A0)
  define h where "h x = inv_into Z g (f x)" for x
  have B0:"\<And>x. x \<in> X \<Longrightarrow> h x \<in> Z"
  proof-
    fix x assume "x \<in> X"
    then have "f x \<in> g ` Z"
      using A2 by blast
    then show "h x \<in> Z"
      unfolding h_def by (rule inv_into_into)
  qed
  have B1:"\<And>x. x \<in> X \<Longrightarrow> g (h x) = f x"
  proof-
    fix x assume "x \<in> X"
    then have "f x \<in> g ` Z"
      using A2 by blast
    then show "g (h x) = f x"
      unfolding h_def by (rule f_inv_into_f)
  qed
  have B2:"magma_hom X (\<cdot>) Z (\<bullet>) h"
  proof(unfold_locales)
    show "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Z"
      by (rule B0)
    fix x y assume C0:"x \<in> X" and C1:"y \<in> X"
    have "g (h (x \<cdot> y)) = f (x \<cdot> y)"
      by (rule B1[OF dom.closed[OF C0 C1]])
    also have "\<dots> = f x \<star> f y"
      by (rule hom[OF C0 C1])
    also have "\<dots> = g (h x) \<star> g (h y)"
      by (simp add:B1[OF C0] B1[OF C1])
    also have "\<dots> = g (h x \<bullet> h y)"
      by (rule g.hom[OF B0[OF C0] B0[OF C1], symmetric])
    finally have D:"g (h (x \<cdot> y)) = g (h x \<bullet> h y)" .
    show "h (x \<cdot> y) = h x \<bullet> h y"
      by (rule inj_onD[OF A1 D B0[OF dom.closed[OF C0 C1]] g.dom.closed[OF B0[OF C0] B0[OF C1]]])
  qed
  show thesis
    using B2 B1 by (rule that)
qed

end

context magma_iso
begin

lemma surj:"f ` X = Y" and inj:"inj_on f X"
  using bij by (simp_all add:bij_betw_def)

lemma inv_f:"x \<in> X \<Longrightarrow> inv_into X f (f x) = x"
  and f_inv:"y \<in> Y \<Longrightarrow> f (inv_into X f y) = y"
  and inv_maps:"y \<in> Y \<Longrightarrow> inv_into X f y \<in> X"
  apply (simp add: inj)
  apply (simp add: f_inv_into_f surj)
  by (simp add: inv_into_into surj)

lemma inv_iso:"magma_iso Y (\<star>) X (\<cdot>) (inv_into X f)"
proof(unfold_locales)
  show "\<And>y. y \<in> Y \<Longrightarrow> inv_into X f y \<in> X"
    by (rule inv_maps)
  show "bij_betw (inv_into X f) Y X"
    by (rule bij_betw_inv_into[OF bij])
  fix y1 y2 assume A0:"y1 \<in> Y" and A1:"y2 \<in> Y"
  obtain x1 x2 where B0:"x1 \<in> X" "x2 \<in> X" "y1 = f x1" "y2 = f x2"
    using surj A0 A1 by blast
  then have "y1 \<star> y2 = f (x1 \<cdot> x2)"
    by (simp add:hom)
  then show "inv_into X f (y1 \<star> y2) = inv_into X f y1 \<cdot> inv_into X f y2"
    using B0 by (simp add:inv_f)
qed

end

lemma magma_iso_compose:
  assumes A0:"magma_iso X mul Y mul' f" and A1:"magma_iso Y mul' Z mul'' g"
  shows "magma_iso X mul Z mul'' (g \<circ> f)"
proof-
  interpret f:magma_iso X mul Y mul' f by (rule A0)
  interpret g:magma_iso Y mul' Z mul'' g by (rule A1)
  interpret gf:magma_hom X mul Z mul'' "g \<circ> f"
    by (rule magma_hom_compose[OF f.magma_hom_axioms g.magma_hom_axioms])
  show ?thesis
    by unfold_locales (rule bij_betw_trans[OF f.bij g.bij])
qed


context magma_hom
begin

definition vimage_cong::"'b rel \<Rightarrow> 'a rel"
  where "vimage_cong S = {(x, y). x \<in> X \<and> y \<in> X \<and> (f x, f y) \<in> S}"

definition image_cong::"'a rel \<Rightarrow> 'b rel"
  where "image_cong R = {(f x, f y)|x y. (x, y) \<in> R}"

lemma vimage_cong_iff:"(x, y) \<in> vimage_cong S \<longleftrightarrow> x \<in> X \<and> y \<in> X \<and> (f x, f y) \<in> S"
  by (simp add:vimage_cong_def)

lemma image_cong_iff:"(b, b') \<in> image_cong R \<longleftrightarrow> (\<exists>x y. (x, y) \<in> R \<and> b = f x \<and> b' = f y)"
  by (auto simp:image_cong_def)

lemma image_congI:"(x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> image_cong R"
  by (auto simp:image_cong_def)

lemma image_congE:"\<lbrakk>(b, b') \<in> image_cong R; \<And>x y. \<lbrakk>(x, y) \<in> R; b = f x; b' = f y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:image_cong_def)

lemma vimage_cong_mono:"S \<subseteq> T \<Longrightarrow> vimage_cong S \<subseteq> vimage_cong T"
  and image_cong_mono:"R \<subseteq> Q \<Longrightarrow> image_cong R \<subseteq> image_cong Q"
  by (auto simp:vimage_cong_def image_cong_def)

lemma vimage_cong_K:"vimage_cong (Id_on Y) = K"
  by (auto simp:vimage_cong_def K_def)

lemma vimage_cong_congruence:
  assumes A0:"congruence Y (\<star>) S"
  shows "congruence X (\<cdot>) (vimage_cong S)"
proof-
  interpret S:congruence Y "(\<star>)" S by (rule A0)
  show ?thesis
  proof(unfold_locales)
    show "vimage_cong S \<subseteq> X \<times> X"
      by (auto simp:vimage_cong_def)
    show "\<And>x. x \<in> X \<Longrightarrow> (x, x) \<in> vimage_cong S"
      by (simp add:vimage_cong_def S.R_refl)
    show "\<And>x y. (x, y) \<in> vimage_cong S \<Longrightarrow> (y, x) \<in> vimage_cong S"
      by (simp add:vimage_cong_def S.R_sym)
    show "\<And>x y z. \<lbrakk>(x, y) \<in> vimage_cong S; (y, z) \<in> vimage_cong S\<rbrakk> \<Longrightarrow> (x, z) \<in> vimage_cong S"
      unfolding vimage_cong_def using S.R_trans by blast
    show "\<And>x x' y y'. \<lbrakk>(x, x') \<in> vimage_cong S; (y, y') \<in> vimage_cong S\<rbrakk> \<Longrightarrow> (x \<cdot> y, x' \<cdot> y') \<in> vimage_cong S"
      by (auto simp:vimage_cong_def hom intro:S.R_compat)
  qed
qed

lemma K_sub_vimage_cong:
  assumes A0:"congruence Y (\<star>) S"
  shows "K \<subseteq> vimage_cong S"
proof-
  interpret S:congruence Y "(\<star>)" S by (rule A0)
  show ?thesis
    by (auto simp:K_def vimage_cong_def S.R_refl)
qed

lemma image_cong_congruence:
  assumes A0:"congruence X (\<cdot>) R" and A1:"K \<subseteq> R" and A2:"f ` X = Y"
  shows "congruence Y (\<star>) (image_cong R)"
proof-
  interpret R:congruence X "(\<cdot>)" R by (rule A0)
  show ?thesis
  proof(unfold_locales)
    show "image_cong R \<subseteq> Y \<times> Y"
      using R.R_carrier by (auto simp:image_cong_def)
    show "\<And>b. b \<in> Y \<Longrightarrow> (b, b) \<in> image_cong R"
    proof-
      fix b assume "b \<in> Y"
      then obtain x where "x \<in> X" and "b = f x"
        using A2 by blast
      then show "(b, b) \<in> image_cong R"
        by (simp add:image_congI R.R_refl)
    qed
    show "\<And>b b'. (b, b') \<in> image_cong R \<Longrightarrow> (b', b) \<in> image_cong R"
    proof-
      fix b b' assume "(b, b') \<in> image_cong R"
      then obtain x y where "(x, y) \<in> R" and "b = f x" and "b' = f y"
        by (rule image_congE)
      then show "(b', b) \<in> image_cong R"
        by (simp add:image_congI R.R_sym)
    qed
    show "\<And>b b' b''. \<lbrakk>(b, b') \<in> image_cong R; (b', b'') \<in> image_cong R\<rbrakk> \<Longrightarrow> (b, b'') \<in> image_cong R"
    proof-
      fix b b' b'' assume C0:"(b, b') \<in> image_cong R" and C1:"(b', b'') \<in> image_cong R"
      obtain x y where C2:"(x, y) \<in> R" and C3:"b = f x" and C4:"b' = f y"
        using C0 by (rule image_congE)
      obtain y' z where C5:"(y', z) \<in> R" and C6:"b' = f y'" and C7:"b'' = f z"
        using C1 by (rule image_congE)
      have C8:"y \<in> X" and C9:"y' \<in> X"
        using C2 C5 R.R_carrier by auto
      have "f y = f y'"
        using C4 C6 by simp
      then have "(y, y') \<in> K"
        using C8 C9 by (simp add:K_def)
      then have "(y, y') \<in> R"
        using A1 by blast
      then have "(x, z) \<in> R"
        using C2 C5 R.R_trans by blast
      then show "(b, b'') \<in> image_cong R"
        by (simp add:C3 C7 image_congI)
    qed
    show "\<And>b b' c c'. \<lbrakk>(b, b') \<in> image_cong R; (c, c') \<in> image_cong R\<rbrakk> \<Longrightarrow> (b \<star> c, b' \<star> c') \<in> image_cong R"
    proof-
      fix b b' c c' assume C0:"(b, b') \<in> image_cong R" and C1:"(c, c') \<in> image_cong R"
      obtain x x' where C2:"(x, x') \<in> R" and C3:"b = f x" and C4:"b' = f x'"
        using C0 by (rule image_congE)
      obtain y y' where C5:"(y, y') \<in> R" and C6:"c = f y" and C7:"c' = f y'"
        using C1 by (rule image_congE)
      have C8:"x \<in> X" "x' \<in> X" "y \<in> X" "y' \<in> X"
        using C2 C5 R.R_carrier by auto
      have "(f (x \<cdot> y), f (x' \<cdot> y')) \<in> image_cong R"
        by (rule image_congI[OF R.R_compat[OF C2 C5]])
      then show "(b \<star> c, b' \<star> c') \<in> image_cong R"
        using C8 by (simp add:C3 C4 C6 C7 hom)
    qed
  qed
qed

lemma vimage_cong_image_cong:
  assumes A0:"congruence X (\<cdot>) R" and A1:"K \<subseteq> R" and A2:"f ` X = Y"
  shows "vimage_cong (image_cong R) = R"
proof-
  interpret R:congruence X "(\<cdot>)" R by (rule A0)
  show ?thesis
  proof
    show "vimage_cong (image_cong R) \<subseteq> R"
    proof
      fix p assume "p \<in> vimage_cong (image_cong R)"
      then obtain x y where B0:"p = (x, y)" and B1:"x \<in> X" and B2:"y \<in> X" and B3:"(f x, f y) \<in> image_cong R"
        by (cases p) (auto simp:vimage_cong_def)
      obtain x' y' where B4:"(x', y') \<in> R" and B5:"f x = f x'" and B6:"f y = f y'"
        using B3 by (rule image_congE)
      have B7:"x' \<in> X" and B8:"y' \<in> X"
        using B4 R.R_carrier by auto
      have "(x, x') \<in> K" and "(y', y) \<in> K"
        using B1 B2 B5 B6 B7 B8 by (simp_all add:K_def)
      then have "(x, x') \<in> R" and "(y', y) \<in> R"
        using A1 by blast+
      then show "p \<in> R"
        using B0 B4 R.R_trans by blast
    qed
    show "R \<subseteq> vimage_cong (image_cong R)"
      using R.R_carrier by (auto simp:vimage_cong_def image_congI)
  qed
qed

lemma image_cong_vimage_cong:
  assumes A0:"congruence Y (\<star>) S" and A1:"f ` X = Y"
  shows "image_cong (vimage_cong S) = S"
proof-
  interpret S:congruence Y "(\<star>)" S by (rule A0)
  show ?thesis
  proof
    show "image_cong (vimage_cong S) \<subseteq> S"
      by (auto simp:image_cong_def vimage_cong_def)
    show "S \<subseteq> image_cong (vimage_cong S)"
    proof
      fix p assume "p \<in> S"
      then obtain b b' where B0:"p = (b, b')" and B1:"b \<in> Y" and B2:"b' \<in> Y" and B3:"(b, b') \<in> S"
        using S.R_carrier by (cases p) auto
      obtain x x' where B4:"x \<in> X" and B5:"x' \<in> X" and B6:"b = f x" and B7:"b' = f x'"
        using A1 B1 B2 by blast
      have "(x, x') \<in> vimage_cong S"
        using B3 B4 B5 B6 B7 by (simp add:vimage_cong_def)
      then show "p \<in> image_cong (vimage_cong S)"
        using B0 B6 B7 by (simp add:image_congI)
    qed
  qed
qed

theorem cong_correspondence:
  assumes A0:"f ` X = Y"
  shows "order_iso subset_order {R \<in> dom.congs. K \<subseteq> R} subset_order cod.congs image_cong"
proof(rule order_isoI)
  show "image_cong ` {R \<in> dom.congs. K \<subseteq> R} = cod.congs"
  proof
    show "image_cong ` {R \<in> dom.congs. K \<subseteq> R} \<subseteq> cod.congs"
      by (auto simp:dom.congs_def cod.congs_def intro:image_cong_congruence[OF _ _ A0])
    show "cod.congs \<subseteq> image_cong ` {R \<in> dom.congs. K \<subseteq> R}"
    proof
      fix S assume "S \<in> cod.congs"
      then have B0:"congruence Y (\<star>) S"
        by (rule cod.congsD)
      have "vimage_cong S \<in> {R \<in> dom.congs. K \<subseteq> R}"
        using vimage_cong_congruence[OF B0] K_sub_vimage_cong[OF B0] by (simp add:dom.congs_def)
      then show "S \<in> image_cong ` {R \<in> dom.congs. K \<subseteq> R}"
        by (rule rev_image_eqI) (rule image_cong_vimage_cong[OF B0 A0, symmetric])
    qed
  qed
  fix R T assume "R \<in> {R \<in> dom.congs. K \<subseteq> R}" and "T \<in> {R \<in> dom.congs. K \<subseteq> R}"
  then have B0:"congruence X (\<cdot>) R" and B1:"K \<subseteq> R" and B2:"congruence X (\<cdot>) T" and B3:"K \<subseteq> T"
    by (auto simp:dom.congs_def)
  show "(R, T) \<in> subset_order \<longleftrightarrow> (image_cong R, image_cong T) \<in> subset_order"
  proof
    assume "(R, T) \<in> subset_order"
    then show "(image_cong R, image_cong T) \<in> subset_order"
      by (simp add:image_cong_mono)
  next
    assume "(image_cong R, image_cong T) \<in> subset_order"
    then have "vimage_cong (image_cong R) \<subseteq> vimage_cong (image_cong T)"
      by (simp add:vimage_cong_mono)
    then show "(R, T) \<in> subset_order"
      by (simp add:vimage_cong_image_cong[OF B0 B1 A0] vimage_cong_image_cong[OF B2 B3 A0])
  qed
qed

context
  fixes S assumes S:"congruence Y (\<star>) S"
begin

interpretation S:congruence Y "(\<star>)" S
  by (rule S)

interpretation Q:congruence X "(\<cdot>)" "vimage_cong S"
  by (rule vimage_cong_congruence[OF S])

lemma vimage_cong_proj_hom:"magma_hom X (\<cdot>) S.quot S.qmul (S.cls \<circ> f)"
  by (rule magma_hom_compose[OF magma_hom_axioms S.proj_hom])

lemma vimage_cong_proj_surj:"f ` X = Y \<Longrightarrow> (S.cls \<circ> f) ` X = S.quot"
  by (simp only:image_comp[symmetric]) (simp add:S.proj_surj)

lemma vimage_cong_ker:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Q.cls x = Q.cls y \<longleftrightarrow> (S.cls \<circ> f) x = (S.cls \<circ> f) y"
  by (simp add:Q.cls_eq_iff vimage_cong_iff S.cls_eq_iff)

theorem vimage_cong_iso:
  assumes A0:"f ` X = Y"
  obtains h where "magma_iso Q.quot Q.qmul S.quot S.qmul h" and "\<And>x. x \<in> X \<Longrightarrow> h (Q.cls x) = S.cls (f x)"
proof-
  interpret g:magma_hom X "(\<cdot>)" S.quot S.qmul "S.cls \<circ> f"
    by (rule vimage_cong_proj_hom)
  obtain h where B0:"magma_iso Q.quot Q.qmul ((S.cls \<circ> f) ` X) S.qmul h" and B1:"\<And>x. x \<in> X \<Longrightarrow> h (Q.cls x) = (S.cls \<circ> f) x"
    using g.first_iso[OF Q.proj_hom Q.proj_surj] vimage_cong_ker by blast
  show thesis
  proof(rule that)
    show "magma_iso Q.quot Q.qmul S.quot S.qmul h"
      using B0 vimage_cong_proj_surj[OF A0] by simp
    show "\<And>x. x \<in> X \<Longrightarrow> h (Q.cls x) = S.cls (f x)"
      using B1 by simp
  qed
qed

end

theorem image_cong_iso:
  assumes A0:"congruence X (\<cdot>) R" and A1:"K \<subseteq> R" and A2:"f ` X = Y"
  obtains h where "magma_iso (congruence.quot X R) (congruence.qmul (\<cdot>) R) (congruence.quot Y (image_cong R)) (congruence.qmul (\<star>) (image_cong R)) h"
    and "\<And>x. x \<in> X \<Longrightarrow> h (congruence.cls R x) = congruence.cls (image_cong R) (f x)"
proof(rule vimage_cong_iso[OF image_cong_congruence[OF A0 A1 A2] A2])
  have B0:"vimage_cong (image_cong R) = R"
    by (rule vimage_cong_image_cong[OF A0 A1 A2])
  fix h
  assume C0:"magma_iso (congruence.quot X (vimage_cong (image_cong R))) (congruence.qmul (\<cdot>) (vimage_cong (image_cong R))) (congruence.quot Y (image_cong R)) (congruence.qmul (\<star>) (image_cong R)) h"
    and C1:"\<And>x. x \<in> X \<Longrightarrow> h (congruence.cls (vimage_cong (image_cong R)) x) = congruence.cls (image_cong R) (f x)"
  show thesis
    by (rule that[OF C0[unfolded B0] C1[unfolded B0]])
qed

end


locale set_endomorphisms =
  fixes E::"'a set"

sublocale set_endomorphisms \<subseteq> monoid "set_mor E E" "compose E" "Id E"
proof(unfold_locales)
  show "\<And>f g. \<lbrakk>f \<in> set_mor E E; g \<in> set_mor E E\<rbrakk> \<Longrightarrow> compose E f g \<in> set_mor E E"
  proof-
    fix f g assume A0:"f \<in> set_mor E E" and A1:"g \<in> set_mor E E"
    show "compose E f g \<in> set_mor E E"
      by (rule comp_set_mor[OF A1 A0])
  qed
  show "\<And>f g h. \<lbrakk>f \<in> set_mor E E; g \<in> set_mor E E; h \<in> set_mor E E\<rbrakk> \<Longrightarrow> compose E (compose E f g) h = compose E f (compose E g h)"
  proof-
    fix f g h assume "f \<in> set_mor E E" and "g \<in> set_mor E E" and "h \<in> set_mor E E"
    then have "h \<in> maps_to E E"
      by (simp add:set_morphisms_memE2)
    then show "compose E (compose E f g) h = compose E f (compose E g h)"
      by (rule comp_assoc[symmetric])
  qed
  show "Id E \<in> set_mor E E"
    by (rule Id_set_mor)
  show "\<And>f. f \<in> set_mor E E \<Longrightarrow> compose E (Id E) f = f"
    by (rule Id_comp)
  show "\<And>f. f \<in> set_mor E E \<Longrightarrow> compose E f (Id E) = f"
    by (rule comp_Id)
qed

context set_endomorphisms
begin

lemma id_lid:"l_identity (Id E)"
  and id_rid:"r_identity (Id E)"
  and id_id:"id_elem (Id E)"
  using unit_id_elem by (simp_all add:id_elem_def)

lemma endo_action:"action (set_mor E E) E (\<lambda>f x. f x)"
proof(unfold_locales)
  fix f x assume "f \<in> set_mor E E" and "x \<in> E"
  then show "f x \<in> E"
    by (rule set_morphisms_memE1)
qed

end

sublocale semigroup \<subseteq> opp:semigroup X "\<lambda>x y. y \<cdot> x"
  by unfold_locales (simp add:assoc)

context semigroup
begin

lemma assoc4:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> (c \<cdot> d) = a \<cdot> (b \<cdot> c) \<cdot> d"
  by (simp add:assoc)

lemma associate3:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"z \<in> X" and A3:"x \<cdot> y = y \<cdot> x"
  shows "x \<cdot> (y \<cdot> z) = (y \<cdot> x) \<cdot> z"
proof-
  have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
    using A0 A1 A2 by (simp add:assoc)
  also have "\<dots> = (y \<cdot> x) \<cdot> z"
    by (simp add:A3)
  finally show ?thesis .
qed

lemma commute_prod1:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"z \<in> X" and A3:"x \<cdot> y = y \<cdot> x" and A4:"x \<cdot> z = z \<cdot> x"
  shows "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x"
proof-
  have "x \<cdot> (y \<cdot> z) = (y \<cdot> x) \<cdot> z"
    by (rule associate3[OF A0 A1 A2 A3])
  also have "\<dots> = y \<cdot> (z \<cdot> x)"
    using A0 A1 A2 by (simp add:assoc A4)
  also have "\<dots> = (y \<cdot> z) \<cdot> x"
    using A0 A1 A2 by (simp add:assoc)
  finally show ?thesis .
qed

lemma commute_prod2:
  "\<lbrakk>x \<in> X; y \<in> X; z \<in> X; x \<cdot> y = y \<cdot> x; x \<cdot> z = z \<cdot> x\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = (y \<cdot> z) \<cdot> x"
  using commute_prod1[of x y z] by (simp add:assoc)

lemma commute_prod3:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"z \<in> X" and A3:"commutes {x} {y, z}"
  shows "commutes {x} {y \<cdot> z}"
proof(rule commutesI)
  fix a b assume B0:"a \<in> {x}" and B1:"b \<in> {y \<cdot> z}"
  have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x"
    by (rule commute_prod1[OF A0 A1 A2 commutesD[OF A3] commutesD[OF A3]]) simp_all
  then show "a \<cdot> b = b \<cdot> a"
    using B0 B1 by simp
qed

lemma centralizer_sub_closed:
  assumes A0:"A \<subseteq> X"
  shows "centralizer A \<in> subs"
proof(rule subsI)
  show "centralizer A \<subseteq> X"
    by (rule centralizer_sub)
  fix x y assume B0:"x \<in> centralizer A" and B1:"y \<in> centralizer A"
  have B2:"x \<in> X" and B3:"y \<in> X"
    using B0 B1 centralizer_sub by auto
  show "x \<cdot> y \<in> centralizer A"
  proof(rule centralizer_memI2)
    show "x \<cdot> y \<in> X"
      using B2 B3 by simp
    fix a assume C0:"a \<in> A"
    then have C1:"a \<in> X" and C2:"x \<cdot> a = a \<cdot> x" and C3:"y \<cdot> a = a \<cdot> y"
      using A0 centralizer_memD[OF B0 C0] centralizer_memD[OF B1 C0] by auto
    have "(x \<cdot> y) \<cdot> a = x \<cdot> (y \<cdot> a)"
      by (rule assoc[OF B2 B3 C1])
    also have "\<dots> = x \<cdot> (a \<cdot> y)"
      by (simp add:C3)
    also have "\<dots> = (x \<cdot> a) \<cdot> y"
      by (rule assoc[OF B2 C1 B3, symmetric])
    also have "\<dots> = (a \<cdot> x) \<cdot> y"
      by (simp add:C2)
    also have "\<dots> = a \<cdot> (x \<cdot> y)"
      by (rule assoc[OF C1 B2 B3])
    finally show "(x \<cdot> y) \<cdot> a = a \<cdot> (x \<cdot> y)" .
  qed
qed

lemma bicentralizer_sub_closed:"A \<subseteq> X \<Longrightarrow> bicentralizer A \<in> subs"
  using centralizer_sub_closed[OF centralizer_sub[of A]] by simp

lemma center_sub_closed:"center \<in> subs"
  by (simp add:center_def centralizer_sub_closed)

lemma center_semigroup:"commutative_semigroup center (\<cdot>)"
proof-
  interpret c:magma center "(\<cdot>)"
    by (rule sub_magma[OF center_sub_closed])
  show ?thesis
  proof(intro commutative_semigroup.intro semigroup.intro c.magma_axioms semigroup_axioms.intro
              commutative_magma.intro commutative_magma_axioms.intro)
    show "\<And>x y z. \<lbrakk>x \<in> center; y \<in> center; z \<in> center\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    proof-
      fix x y z assume "x \<in> center" and "y \<in> center" and "z \<in> center"
      then have "x \<in> X" and "y \<in> X" and "z \<in> X"
        using center_sub by auto
      then show "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
        by (rule assoc)
    qed
    show "\<And>x y. \<lbrakk>x \<in> center; y \<in> center\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
    proof-
      fix x y assume "x \<in> center" and "y \<in> center"
      then have "y \<in> X"
        using center_sub by auto
      then show "x \<cdot> y = y \<cdot> x"
        using center_memD[OF \<open>x \<in> center\<close>] by simp
    qed
  qed
qed

lemma centralizer_cl:
  assumes A0:"A \<subseteq> X" and A1:"B \<subseteq> X" and A2:"commutes A B"
  shows "commutes (sub.cl A) (sub.cl B)"
proof-
  have B0:"sub.cl B \<in> subs" and B1:"sub.cl A \<in> subs"
    using A0 A1 by simp_all
  have B2:"sub.cl B \<subseteq> X" and B3:"sub.cl A \<subseteq> X"
    using subsD(1)[OF B0] subsD(1)[OF B1] by simp_all
  have "sub.cl B \<subseteq> centralizer A"
    by (rule sub.cl_least[OF centralizer_sub_closed[OF A0] commutes_sub_centralizer1[OF A1 A2]])
  then have B4:"commutes A (sub.cl B)"
    by (simp add:commutes_iff_sub_centralizer[OF B2])
  have "sub.cl A \<subseteq> centralizer (sub.cl B)"
    by (rule sub.cl_least[OF centralizer_sub_closed[OF B2] commutes_sub_centralizer2[OF A0 B4]])
  then have "commutes (sub.cl B) (sub.cl A)"
    by (simp add:commutes_iff_sub_centralizer[OF B3])
  then show ?thesis
    by (rule commutes_sym)
qed

lemma l_trans_comp:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "l_trans (x \<cdot> y) = compose X (l_trans x) (l_trans y)"
proof-
  have "l_trans (x \<cdot> y) = (\<lambda>z\<in>X. (x \<cdot> y) \<cdot> z)"
    using A0 A1 by (simp add:l_trans_def)
  also have "\<dots> = (\<lambda>z\<in>X. x \<cdot> (y \<cdot> z))"
    by (rule restrict_ext) (simp add:assoc A0 A1)
  also have "\<dots> = compose X (l_trans x) (l_trans y)"
    unfolding compose_def by (rule restrict_ext) (simp add:l_trans_app A0 A1)
  finally show ?thesis .
qed

lemma r_trans_comp:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "r_trans (x \<cdot> y) = compose X (r_trans y) (r_trans x)"
proof-
  have "r_trans (x \<cdot> y) = (\<lambda>z\<in>X. z \<cdot> (x \<cdot> y))"
    using A0 A1 by (simp add:r_trans_def)
  also have "\<dots> = (\<lambda>z\<in>X. (z \<cdot> x) \<cdot> y)"
    by (rule restrict_ext) (simp add:assoc A0 A1)
  also have "\<dots> = compose X (r_trans y) (r_trans x)"
    unfolding compose_def by (rule restrict_ext) (simp add:r_trans_app A0 A1)
  finally show ?thesis .
qed

lemma l_trans_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> l_trans (x \<cdot> y) z = l_trans x (l_trans y z)"
  by (simp add:l_trans_comp comp_eq)

lemma r_trans_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> r_trans (x \<cdot> y) z = r_trans y (r_trans x z)"
  by (simp add:r_trans_comp comp_eq)

lemma l_trans_hom:"magma_hom X (\<cdot>) (set_mor X X) (compose X) l_trans"
proof-
  interpret endo:set_endomorphisms X .
  show ?thesis
  proof(intro magma_hom.intro magma_hom_axioms.intro magma_axioms endo.magma_axioms)
    show "\<And>x. x \<in> X \<Longrightarrow> l_trans x \<in> set_mor X X"
      by (rule l_trans_maps)
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> l_trans (x \<cdot> y) = compose X (l_trans x) (l_trans y)"
      by (rule l_trans_comp)
  qed
qed

lemma r_trans_hom:"magma_hom X (\<lambda>x y. y \<cdot> x) (set_mor X X) (compose X) r_trans"
proof-
  interpret endo:set_endomorphisms X .
  show ?thesis
  proof(intro magma_hom.intro magma_hom_axioms.intro opp.magma_axioms endo.magma_axioms)
    show "\<And>x. x \<in> X \<Longrightarrow> r_trans x \<in> set_mor X X"
      by (rule r_trans_maps)
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> r_trans (y \<cdot> x) = compose X (r_trans x) (r_trans y)"
      by (rule r_trans_comp)
  qed
qed

lemma l_cancellable_prod:
  assumes A0:"l_cancellable x" and A1:"l_cancellable y" and A2:"a \<in> X" and A3:"b \<in> X" and A4:"x \<cdot> y \<cdot> a = x \<cdot> y \<cdot> b"
  shows "a = b"
proof-
  have B0:"x \<in> X" and B1:"y \<in> X"
    using A0 A1 by (simp_all add:l_cancellableD1)
  have "x \<cdot> (y \<cdot> a) = (x \<cdot> y) \<cdot> a"
    by (rule assoc[symmetric]) (simp_all add:B0 B1 A2)
  also have "\<dots> = (x \<cdot> y) \<cdot> b"
    by (rule A4)
  also have "\<dots> = x \<cdot> (y \<cdot> b)"
    by (rule assoc) (simp_all add:B0 B1 A3)
  finally have C:"x \<cdot> (y \<cdot> a) = x \<cdot> (y \<cdot> b)" .
  have "y \<cdot> a = y \<cdot> b"
    by (rule l_cancellableD2[OF A0 _ _ C]) (simp_all add:B1 A2 A3)
  then show "a = b"
    by (rule l_cancellableD2[OF A1 A2 A3])
qed

lemma r_cancellable_prod:
  assumes A0:"r_cancellable x" and A1:"r_cancellable y" and A2:"a \<in> X" and A3:"b \<in> X" and A4:"a \<cdot> (x \<cdot> y) = b \<cdot> (x \<cdot> y)"
  shows "a = b"
proof-
  have B0:"x \<in> X" and B1:"y \<in> X"
    using A0 A1 by (simp_all add:r_cancellableD1)
  have "(a \<cdot> x) \<cdot> y = a \<cdot> (x \<cdot> y)"
    by (rule assoc) (simp_all add:B0 B1 A2)
  also have "\<dots> = b \<cdot> (x \<cdot> y)"
    by (rule A4)
  also have "\<dots> = (b \<cdot> x) \<cdot> y"
    by (rule assoc[symmetric]) (simp_all add:B0 B1 A3)
  finally have C:"(a \<cdot> x) \<cdot> y = (b \<cdot> x) \<cdot> y" .
  have "a \<cdot> x = b \<cdot> x"
    by (rule r_cancellableD2[OF A1 _ _ C]) (simp_all add:B0 A2 A3)
  then show "a = b"
    by (rule r_cancellableD2[OF A0 A2 A3])
qed

lemma l_cancellable_prod_closed:
  assumes A0:"l_cancellable x" and A1:"l_cancellable y"
  shows "l_cancellable (x \<cdot> y)"
proof(rule l_cancellableI1)
  show "x \<cdot> y \<in> X"
    using A0 A1 by (simp add:l_cancellableD1)
  fix a b assume "a \<in> X" and "b \<in> X" and "x \<cdot> y \<cdot> a = x \<cdot> y \<cdot> b"
  then show "a = b"
    by (rule l_cancellable_prod[OF A0 A1])
qed

lemma r_cancellable_prod_closed:
  assumes A0:"r_cancellable x" and A1:"r_cancellable y"
  shows "r_cancellable (x \<cdot> y)"
proof(rule r_cancellableI1)
  show "x \<cdot> y \<in> X"
    using A0 A1 by (simp add:r_cancellableD1)
  fix a b assume "a \<in> X" and "b \<in> X" and "a \<cdot> (x \<cdot> y) = b \<cdot> (x \<cdot> y)"
  then show "a = b"
    by (rule r_cancellable_prod[OF A0 A1])
qed

lemma cancellable_prod_closed:"\<lbrakk>cancellable x; cancellable y\<rbrakk> \<Longrightarrow> cancellable (x \<cdot> y)"
  by (simp add:cancellable_def l_cancellable_prod_closed r_cancellable_prod_closed)

lemma l_cancellables_sub:"{x. l_cancellable x} \<in> subs"
proof(rule subsI)
  show "{x. l_cancellable x} \<subseteq> X"
    using l_cancellableD1 by auto
  fix a b assume "a \<in> {x. l_cancellable x}" and "b \<in> {x. l_cancellable x}"
  then show "a \<cdot> b \<in> {x. l_cancellable x}"
    by (simp add:l_cancellable_prod_closed)
qed

lemma r_cancellables_sub:"{x. r_cancellable x} \<in> subs"
proof(rule subsI)
  show "{x. r_cancellable x} \<subseteq> X"
    using r_cancellableD1 by auto
  fix a b assume "a \<in> {x. r_cancellable x}" and "b \<in> {x. r_cancellable x}"
  then show "a \<cdot> b \<in> {x. r_cancellable x}"
    by (simp add:r_cancellable_prod_closed)
qed

lemma cancellables_sub:"{x. cancellable x} \<in> subs"
proof(rule subsI)
  show "{x. cancellable x} \<subseteq> X"
    using cancellableD3 by auto
  fix a b assume "a \<in> {x. cancellable x}" and "b \<in> {x. cancellable x}"
  then show "a \<cdot> b \<in> {x. cancellable x}"
    by (simp add:cancellable_prod_closed)
qed

lemma set_prod_singleton:"set_prod {a} {b} = {a \<cdot> b}"
  by (simp add:set_prod_def)

lemma set_prod_assoc:
  assumes A0:"A \<subseteq> X" and A1:"B \<subseteq> X" and A2:"C \<subseteq> X"
  shows "set_prod (set_prod A B) C = set_prod A (set_prod B C)"
proof
  show "set_prod (set_prod A B) C \<subseteq> set_prod A (set_prod B C)"
  proof
    fix z assume "z \<in> set_prod (set_prod A B) C"
    then obtain p c where B0:"p \<in> set_prod A B" and B1:"c \<in> C" and B2:"z = p \<cdot> c"
      by (rule set_prod_memE)
    obtain a b where B3:"a \<in> A" and B4:"b \<in> B" and B5:"p = a \<cdot> b"
      using B0 by (rule set_prod_memE)
    have "z = a \<cdot> (b \<cdot> c)"
      using A0 A1 A2 B1 B3 B4 by (simp add:B2 B5 assoc subset_iff)
    then show "z \<in> set_prod A (set_prod B C)"
      using B1 B3 B4 by (simp add:set_prod_memI)
  qed
  show "set_prod A (set_prod B C) \<subseteq> set_prod (set_prod A B) C"
  proof
    fix z assume "z \<in> set_prod A (set_prod B C)"
    then obtain a p where B0:"a \<in> A" and B1:"p \<in> set_prod B C" and B2:"z = a \<cdot> p"
      by (rule set_prod_memE)
    obtain b c where B3:"b \<in> B" and B4:"c \<in> C" and B5:"p = b \<cdot> c"
      using B1 by (rule set_prod_memE)
    have "z = (a \<cdot> b) \<cdot> c"
      using A0 A1 A2 B0 B3 B4 by (simp add:B2 B5 assoc subset_iff)
    then show "z \<in> set_prod (set_prod A B) C"
      using B0 B3 B4 by (simp add:set_prod_memI)
  qed
qed

lemma r_coset_assoc:"\<lbrakk>E \<subseteq> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> r_coset (r_coset E a) b = r_coset E (a \<cdot> b)"
  unfolding r_coset_singleton_prod by (simp add:set_prod_assoc set_prod_singleton)

lemma l_coset_assoc:"\<lbrakk>E \<subseteq> X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> l_coset a (l_coset b E) = l_coset (a \<cdot> b) E"
  unfolding l_coset_singleton_prod by (simp add:set_prod_assoc[symmetric] set_prod_singleton)

lemma lr_coset_assoc:"\<lbrakk>x \<in> X; y \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> l_coset x (r_coset H y) = r_coset (l_coset x H) y"
  unfolding l_coset_singleton_prod r_coset_singleton_prod by (simp add:set_prod_assoc)

lemma sub_semigroup:
  assumes A0:"A \<in> subs"
  shows "semigroup A (\<cdot>)"
proof(rule semigroup.intro[OF sub_magma[OF A0]])
  show "semigroup_axioms A (\<cdot>)"
  proof(rule semigroup_axioms.intro)
    fix x y z assume "x \<in> A" and "y \<in> A" and "z \<in> A"
    then have "x \<in> X" and "y \<in> X" and "z \<in> X"
      using subsD(1)[OF A0] by auto
    then show "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
      by (rule assoc)
  qed
qed

lemma group_if_right:
  assumes A0:"e \<in> X" and A1:"r_identity e" and A2:"\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. x \<cdot> y = e"
  shows "group X (\<cdot>) e"
proof-
  have B0:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X; x \<cdot> y = e\<rbrakk> \<Longrightarrow> y \<cdot> x = e"
  proof-
    fix x y assume C0:"x \<in> X" and C1:"y \<in> X" and C2:"x \<cdot> y = e"
    obtain z where C3:"z \<in> X" and C4:"y \<cdot> z = e"
      using A2[OF C1] by blast
    have "y \<cdot> x = (y \<cdot> x) \<cdot> e"
      using A1 C0 C1 by (simp add:r_identity_def)
    also have "\<dots> = (y \<cdot> x) \<cdot> (y \<cdot> z)"
      by (simp add:C4)
    also have "\<dots> = y \<cdot> (x \<cdot> y) \<cdot> z"
      by (rule assoc4[OF C1 C0 C1 C3])
    also have "\<dots> = y \<cdot> z"
      using A1 C1 by (simp add:C2 r_identity_def)
    finally show "y \<cdot> x = e"
      by (simp add:C4)
  qed
  have B1:"\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x"
  proof-
    fix x assume C0:"x \<in> X"
    obtain y where C1:"y \<in> X" and C2:"x \<cdot> y = e"
      using A2[OF C0] by blast
    have "e \<cdot> x = (x \<cdot> y) \<cdot> x"
      by (simp add:C2)
    also have "\<dots> = x \<cdot> (y \<cdot> x)"
      using C0 C1 by (simp add:assoc)
    also have "\<dots> = x \<cdot> e"
      by (simp add:B0[OF C0 C1 C2])
    finally show "e \<cdot> x = x"
      using A1 C0 by (simp add:r_identity_def)
  qed
  show ?thesis
  proof(unfold_locales)
    show "e \<in> X"
      by (rule A0)
    show "\<And>x. x \<in> X \<Longrightarrow> e \<cdot> x = x"
      by (rule B1)
    show "\<And>x. x \<in> X \<Longrightarrow> x \<cdot> e = x"
      using A1 by (simp add:r_identity_def)
    show "\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. y \<cdot> x = e \<and> x \<cdot> y = e"
    proof-
      fix x assume C0:"x \<in> X"
      obtain y where C1:"y \<in> X" and C2:"x \<cdot> y = e"
        using A2[OF C0] by blast
      then show "\<exists>y\<in>X. y \<cdot> x = e \<and> x \<cdot> y = e"
        using B0[OF C0 C1 C2] by blast
    qed
  qed
qed

end

lemma (in congruence) quotient_semigroup:"semigroup X (\<cdot>) \<Longrightarrow> semigroup quot (\<bullet>)"
  by (rule proj.surj_semigroup[OF proj_surj])

lemma (in congruence) quotient_commutative:"commutative_magma X (\<cdot>) \<Longrightarrow> commutative_magma quot (\<bullet>)"
  by (rule proj.surj_commutative[OF proj_surj])


sublocale monoid \<subseteq> opp:monoid X "\<lambda>x y. y \<cdot> x" \<one>
  by unfold_locales simp_all

lemma (in group) opp_group:"group X (\<lambda>x y. y \<cdot> x) \<one>"
proof(rule group.intro[OF opp.monoid_axioms], rule group_axioms.intro)
  fix x assume "x \<in> X"
  then show "\<exists>y\<in>X. (\<lambda>x y. y \<cdot> x) y x = \<one> \<and> (\<lambda>x y. y \<cdot> x) x y = \<one>"
    using inverse_ex[of x] by auto
qed

lemma (in semigroup) group_if_left:
  assumes A0:"e \<in> X" and A1:"l_identity e" and A2:"\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. y \<cdot> x = e"
  shows "group X (\<cdot>) e"
proof-
  have "group X (\<lambda>x y. y \<cdot> x) e"
    by (rule opp.group_if_right) (simp_all add:A0 A1 A2 opp_r_identity)
  then show ?thesis
    using group.opp_group[of X "\<lambda>x y. y \<cdot> x" e] by simp
qed


context monoid
begin

definition invertible::"'a \<Rightarrow> bool"
  where "invertible u \<longleftrightarrow> (\<exists>v\<in>X. u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>)"

definition inv::"'a \<Rightarrow> 'a"
  where "inv u = (THE v. v \<in> X \<and> v \<cdot> u = \<one> \<and> u \<cdot> v = \<one>)"

definition Units::"'a set"
  where "Units = {u \<in> X. invertible u}"

lemma invertibleI[intro]:"\<lbrakk>u \<cdot> v = \<one>; v \<cdot> u = \<one>; v \<in> X\<rbrakk> \<Longrightarrow> invertible u"
  by (auto simp:invertible_def)

lemma invertibleE[elim]:"\<lbrakk>invertible u; \<And>v. \<lbrakk>u \<cdot> v = \<one>; v \<cdot> u = \<one>; v \<in> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp:invertible_def)

lemma mem_UnitsI:"\<lbrakk>invertible u; u \<in> X\<rbrakk> \<Longrightarrow> u \<in> Units"
  and mem_UnitsD:"u \<in> Units \<Longrightarrow> invertible u \<and> u \<in> X"
  and Units_sub:"Units \<subseteq> X"
  by (auto simp:Units_def)

lemma inverse_unique:
  assumes A0:"u \<cdot> v' = \<one>" and A1:"v \<cdot> u = \<one>" and A2:"u \<in> X" and A3:"v \<in> X" and A4:"v' \<in> X"
  shows "v = v'"
proof-
  have "v = v \<cdot> (u \<cdot> v')"
    using A0 A3 by simp
  also have "\<dots> = (v \<cdot> u) \<cdot> v'"
    using A2 A3 A4 by (simp add:assoc)
  also have "\<dots> = v'"
    using A1 A4 by simp
  finally show ?thesis .
qed

lemma inv_eq:
  assumes A0:"u \<cdot> v = \<one>" and A1:"v \<cdot> u = \<one>" and A2:"u \<in> X" and A3:"v \<in> X"
  shows "inv u = v"
  unfolding inv_def
proof(rule the_equality)
  show "v \<in> X \<and> v \<cdot> u = \<one> \<and> u \<cdot> v = \<one>"
    using A0 A1 A3 by simp
  fix w assume B0:"w \<in> X \<and> w \<cdot> u = \<one> \<and> u \<cdot> w = \<one>"
  show "w = v"
    by (rule inverse_unique[OF A0 _ A2 _ A3]) (simp_all add:B0)
qed

lemma unit_inv_props:
  assumes A0:"invertible u" and A1:"u \<in> X"
  shows unit_inv_closed[simp, intro]:"inv u \<in> X"
    and unit_linv[simp]:"inv u \<cdot> u = \<one>"
    and unit_rinv[simp]:"u \<cdot> inv u = \<one>"
proof-
  obtain v where B0:"u \<cdot> v = \<one>" and B1:"v \<cdot> u = \<one>" and B2:"v \<in> X"
    using A0 by (rule invertibleE)
  have "inv u = v"
    by (rule inv_eq[OF B0 B1 A1 B2])
  then show "inv u \<in> X" and "inv u \<cdot> u = \<one>" and "u \<cdot> inv u = \<one>"
    by (simp_all add:B0 B1 B2)
qed

lemma invertible_left_cancel[simp]:
  assumes A0:"invertible x" and A1:"x \<in> X" and A2:"y \<in> X" and A3:"z \<in> X"
  shows "x \<cdot> y = x \<cdot> z \<longleftrightarrow> y = z"
proof
  assume B0:"x \<cdot> y = x \<cdot> z"
  have "y = (inv x \<cdot> x) \<cdot> y"
    using A0 A1 A2 by simp
  also have "\<dots> = inv x \<cdot> (x \<cdot> y)"
    by (rule assoc) (simp_all add:A0 A1 A2)
  also have "\<dots> = inv x \<cdot> (x \<cdot> z)"
    by (simp add:B0)
  also have "\<dots> = (inv x \<cdot> x) \<cdot> z"
    by (rule assoc[symmetric]) (simp_all add:A0 A1 A3)
  also have "\<dots> = z"
    using A0 A1 A3 by simp
  finally show "y = z" .
qed simp

lemma invertible_right_cancel[simp]:
  assumes A0:"invertible x" and A1:"x \<in> X" and A2:"y \<in> X" and A3:"z \<in> X"
  shows "y \<cdot> x = z \<cdot> x \<longleftrightarrow> y = z"
proof
  assume B0:"y \<cdot> x = z \<cdot> x"
  have "y = y \<cdot> (x \<cdot> inv x)"
    using A0 A1 A2 by simp
  also have "\<dots> = (y \<cdot> x) \<cdot> inv x"
    by (rule assoc[symmetric]) (simp_all add:A0 A1 A2)
  also have "\<dots> = (z \<cdot> x) \<cdot> inv x"
    by (simp add:B0)
  also have "\<dots> = z \<cdot> (x \<cdot> inv x)"
    by (rule assoc) (simp_all add:A0 A1 A3)
  also have "\<dots> = z"
    using A0 A1 A3 by simp
  finally show "y = z" .
qed simp

lemma invertible_l_cancellable:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> l_cancellable x"
  and invertible_r_cancellable:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> r_cancellable x"
  and invertible_cancellable:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> cancellable x"
  by (simp_all add:l_cancellable_def r_cancellable_def cancellable_def)

lemma inv_ident[simp]:"inv \<one> = \<one>"
  by (rule inv_eq) simp_all

lemma e_unit:"invertible \<one>"
  by (rule invertibleI[of \<one> \<one>]) simp_all

lemma unit_mem_Units:"\<one> \<in> Units"
  by (simp add:Units_def e_unit)

lemma invertible_inverse_invertible[intro, simp]:"\<lbrakk>invertible u; u \<in> X\<rbrakk> \<Longrightarrow> invertible (inv u)"
  by (rule invertibleI[of _ u]) simp_all

lemma invertible_inverse_inverse[simp]:"\<lbrakk>invertible u; u \<in> X\<rbrakk> \<Longrightarrow> inv (inv u) = u"
  by (rule inv_eq) simp_all

lemma prod_rinv:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"invertible x" and A3:"invertible y"
  shows "(x \<cdot> y) \<cdot> (inv y \<cdot> inv x) = \<one>"
proof-
  have "(x \<cdot> y) \<cdot> (inv y \<cdot> inv x) = x \<cdot> (y \<cdot> inv y) \<cdot> inv x"
    using A0 A1 A2 A3 by (intro assoc4) simp_all
  also have "\<dots> = \<one>"
    using A0 A1 A2 A3 by simp
  finally show ?thesis .
qed

lemma prod_linv:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"invertible x" and A3:"invertible y"
  shows "(inv y \<cdot> inv x) \<cdot> (x \<cdot> y) = \<one>"
proof-
  have "(inv y \<cdot> inv x) \<cdot> (x \<cdot> y) = inv y \<cdot> (inv x \<cdot> x) \<cdot> y"
    using A0 A1 A2 A3 by (intro assoc4) simp_all
  also have "\<dots> = \<one>"
    using A0 A1 A2 A3 by simp
  finally show ?thesis .
qed

lemma prod_inv:"\<lbrakk>x \<in> X; y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv y \<cdot> inv x"
  by (rule inv_eq) (simp_all add:prod_rinv prod_linv)

lemma prod_invertible:"\<lbrakk>x \<in> X; y \<in> X; invertible x; invertible y\<rbrakk> \<Longrightarrow> invertible (x \<cdot> y)"
  by (rule invertibleI[of _ "inv y \<cdot> inv x"]) (simp_all add:prod_rinv prod_linv)

lemma inv_rcancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> (inv x \<cdot> y) = y"
  and inv_lcancel:"\<lbrakk>invertible x; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x \<cdot> (x \<cdot> y) = y"
  by (simp_all add:assoc[symmetric])

lemma l_trans_inv1:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans x) (l_trans (inv x)) = Id X"
  and l_trans_inv2:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> compose X (l_trans (inv x)) (l_trans x) = Id X"
  and r_trans_inv1:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans x) (r_trans (inv x)) = Id X"
  and r_trans_inv2:"\<lbrakk>invertible x; x \<in> X\<rbrakk> \<Longrightarrow> compose X (r_trans (inv x)) (r_trans x) = Id X"
  by (simp_all add:l_trans_comp[symmetric] r_trans_comp[symmetric] unit_l_trans unit_r_trans)

lemma set_prod_unit1[simp]:
  assumes A0:"A \<subseteq> X"
  shows "set_prod {\<one>} A = A"
proof
  show "set_prod {\<one>} A \<subseteq> A"
    using A0 by (auto simp:set_prod_def)
  show "A \<subseteq> set_prod {\<one>} A"
  proof
    fix a assume B0:"a \<in> A"
    then have "a = \<one> \<cdot> a"
      using A0 by auto
    then show "a \<in> set_prod {\<one>} A"
      using set_prod_memI[of \<one> "{\<one>}" a A] B0 by simp
  qed
qed

lemma set_prod_unit2[simp]:
  assumes A0:"A \<subseteq> X"
  shows "set_prod A {\<one>} = A"
proof
  show "set_prod A {\<one>} \<subseteq> A"
    using A0 by (auto simp:set_prod_def)
  show "A \<subseteq> set_prod A {\<one>}"
  proof
    fix a assume B0:"a \<in> A"
    then have "a = a \<cdot> \<one>"
      using A0 by auto
    then show "a \<in> set_prod A {\<one>}"
      using set_prod_memI[of a A \<one> "{\<one>}"] B0 by simp
  qed
qed

lemma l_coset_unit[simp]:"H \<subseteq> X \<Longrightarrow> l_coset \<one> H = H"
  and r_coset_unit[simp]:"H \<subseteq> X \<Longrightarrow> r_coset H \<one> = H"
  by (simp_all add:l_coset_singleton_prod r_coset_singleton_prod)

lemma submonoidsI:"\<lbrakk>A \<subseteq> X; \<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A; \<one> \<in> A\<rbrakk> \<Longrightarrow> A \<in> submonoids"
  by (simp add:submonoids_def subsI)

lemma submonoidsD:
  assumes "A \<in> submonoids"
  shows "A \<subseteq> X" and "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> A" and "\<one> \<in> A"
  using assms by (auto simp:submonoids_def subs_def)

lemma submonoids_sub_subs:"submonoids \<subseteq> subs"
  by (auto simp:submonoids_def)

lemma sub_monoid:
  assumes A0:"A \<in> submonoids"
  shows "monoid A (\<cdot>) \<one>"
proof-
  have B0:"A \<in> subs"
    using A0 by (simp add:submonoids_def)
  have B1:"A \<subseteq> X"
    by (rule submonoidsD(1)[OF A0])
  show ?thesis
  proof(intro monoid.intro sub_semigroup[OF B0] unital_magma.intro sub_magma[OF B0] unital_magma_axioms.intro)
    show "\<one> \<in> A"
      by (rule submonoidsD(3)[OF A0])
    show "\<And>x. x \<in> A \<Longrightarrow> \<one> \<cdot> x = x" and "\<And>x. x \<in> A \<Longrightarrow> x \<cdot> \<one> = x"
      using B1 by auto
  qed
qed

lemma submonoid_invertible:
  assumes A0:"A \<in> submonoids" and A1:"monoid.invertible A (\<cdot>) \<one> u" and A2:"u \<in> A"
  shows "invertible u" and "inv u \<in> A" and "monoid.inv A (\<cdot>) \<one> u = inv u"
proof-
  interpret sub:monoid A "(\<cdot>)" \<one>
    by (rule sub_monoid[OF A0])
  obtain v where B0:"u \<cdot> v = \<one>" and B1:"v \<cdot> u = \<one>" and B2:"v \<in> A"
    using A1 by (rule sub.invertibleE)
  have B3:"u \<in> X" and B4:"v \<in> X"
    using A2 B2 submonoidsD(1)[OF A0] by auto
  show "invertible u"
    by (rule invertibleI[OF B0 B1 B4])
  have "inv u = v"
    by (rule inv_eq[OF B0 B1 B3 B4])
  then show "inv u \<in> A" and "monoid.inv A (\<cdot>) \<one> u = inv u"
    using B2 sub.inv_eq[OF B0 B1 A2 B2] by simp_all
qed

lemma Units_closed:"\<lbrakk>u \<in> Units; v \<in> Units\<rbrakk> \<Longrightarrow> u \<cdot> v \<in> Units"
  and Units_inv_closed:"u \<in> Units \<Longrightarrow> inv u \<in> Units"
  by (auto simp:Units_def prod_invertible)

lemma Units_submonoid:"Units \<in> submonoids"
  by (rule submonoidsI[OF Units_sub Units_closed unit_mem_Units])

lemma Units_group:"group Units (\<cdot>) \<one>"
proof(rule group.intro[OF sub_monoid[OF Units_submonoid]], rule group_axioms.intro)
  fix x assume "x \<in> Units"
  then have "inv x \<in> Units" and "inv x \<cdot> x = \<one>" and "x \<cdot> inv x = \<one>"
    by (simp_all add:Units_inv_closed Units_def)
  then show "\<exists>y\<in>Units. y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"
    by blast
qed

lemma group_iff_Units:"group X (\<cdot>) \<one> \<longleftrightarrow> Units = X"
proof
  assume "group X (\<cdot>) \<one>"
  then interpret group X "(\<cdot>)" \<one> .
  show "Units = X"
    using inverse_ex by (auto simp:Units_def invertible_def)
next
  assume A0:"Units = X"
  show "group X (\<cdot>) \<one>"
  proof(rule group.intro[OF monoid_axioms], rule group_axioms.intro)
    fix x assume "x \<in> X"
    then show "\<exists>y\<in>X. y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"
      using A0 by (auto simp:Units_def invertible_def)
  qed
qed

lemma l_trans_inj:"inj_on l_trans X"
proof(rule inj_onI)
  fix x y assume A0:"x \<in> X" and A1:"y \<in> X" and A2:"l_trans x = l_trans y"
  have "x = l_trans x \<one>"
    using A0 by (simp add:l_trans_app)
  also have "\<dots> = l_trans y \<one>"
    by (simp add:A2)
  also have "\<dots> = y"
    using A1 by (simp add:l_trans_app)
  finally show "x = y" .
qed

lemma l_trans_monoid_hom:"monoid_hom X (\<cdot>) \<one> (set_mor X X) (compose X) (Id X) l_trans"
proof-
  interpret endo:set_endomorphisms X .
  show ?thesis
  proof(intro monoid_hom.intro monoid_hom_axioms.intro l_trans_hom monoid_axioms endo.monoid_axioms)
    show "l_trans \<one> = Id X"
      by (rule unit_l_trans)
  qed
qed

theorem cayley:"magma_iso X (\<cdot>) (l_trans ` X) (compose X) l_trans"
proof-
  interpret h:magma_hom X "(\<cdot>)" "set_mor X X" "compose X" l_trans
    by (rule l_trans_hom)
  show ?thesis
  proof(intro magma_iso.intro magma_iso_axioms.intro magma_hom.intro magma_hom_axioms.intro magma_axioms h.im_magma)
    show "\<And>x. x \<in> X \<Longrightarrow> l_trans x \<in> l_trans ` X"
      by simp
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> l_trans (x \<cdot> y) = compose X (l_trans x) (l_trans y)"
      by (rule l_trans_comp)
    show "bij_betw l_trans X (l_trans ` X)"
      using l_trans_inj by (simp add:bij_betw_def)
  qed
qed

end


context group
begin

lemma invertible[simp, intro]:"x \<in> X \<Longrightarrow> invertible x"
  using inverse_ex by (auto simp:invertible_def)

lemma inv_unique:
  assumes x:"x \<in> X" and y:"y \<in> X" "y \<cdot> x = \<one>" and z:"z \<in> X" "x \<cdot> z = \<one>"
  shows "y = z"
  by (rule inverse_unique[OF z(2) y(2) x y(1) z(1)])

lemma inv_closed[simp, intro]:"x \<in> X \<Longrightarrow> inv x \<in> X"
  and inv_left[simp]:"x \<in> X \<Longrightarrow> inv x \<cdot> x = \<one>"
  and inv_right[simp]:"x \<in> X \<Longrightarrow> x \<cdot> inv x = \<one>"
  by simp_all

lemma Units_eq:"Units = X"
  by (simp add:group_iff_Units[symmetric] group_axioms)

definition subgroups :: "'a set set"
  where "subgroups = {A \<in> submonoids. \<forall>a\<in>A. inv a \<in> A}"

sublocale subgrp: moore_family X subgroups
proof unfold_locales
  show "subgroups \<subseteq> Pow X" using submon.base by (auto simp: subgroups_def)
  show "X \<in> subgroups" using submon.whole by (auto simp: subgroups_def)
  show "\<Inter>E \<in> subgroups" if E: "E \<subseteq> subgroups" "E \<noteq> {}" for E
  proof -
    have sub: "E \<subseteq> submonoids" using E(1) by (auto simp: subgroups_def)
    have "\<Inter>E \<in> submonoids" by (rule submon.Inter_closed[OF sub E(2)])
    moreover have "inv a \<in> \<Inter>E" if a: "a \<in> \<Inter>E" for a
    proof
      fix A assume "A \<in> E"
      then have "A \<in> subgroups" "a \<in> A" using E(1) a by auto
      then show "inv a \<in> A" by (auto simp: subgroups_def)
    qed
    ultimately show ?thesis by (auto simp: subgroups_def)
  qed
qed

end


context monoid_hom
begin

lemma inverse_image_id1:"\<lbrakk>x \<in> X; dom.invertible x\<rbrakk> \<Longrightarrow> f x \<star> f (dom.inv x) = e'"
  and inverse_image_id2:"\<lbrakk>x \<in> X; dom.invertible x\<rbrakk> \<Longrightarrow> f (dom.inv x) \<star> f x = e'"
  by (simp_all add:hom[symmetric] unit)

lemma invertible_image:"\<lbrakk>x \<in> X; dom.invertible x\<rbrakk> \<Longrightarrow> cod.invertible (f x)"
  by (rule cod.invertibleI[OF inverse_image_id1 inverse_image_id2]) simp_all

lemma inv_image:"\<lbrakk>x \<in> X; dom.invertible x\<rbrakk> \<Longrightarrow> f (dom.inv x) = cod.inv (f x)"
  by (rule cod.inv_eq[OF inverse_image_id1 inverse_image_id2, symmetric]) simp_all

lemma Units_image:"f ` dom.Units \<subseteq> cod.Units"
  by (auto simp:dom.Units_def cod.Units_def invertible_image)

lemma image_submonoid:
  assumes A0:"A \<in> dom.submonoids"
  shows "f ` A \<in> cod.submonoids"
proof-
  have "f ` A \<in> cod.subs"
    using A0 by (intro image_sub) (simp add:dom.submonoids_def)
  moreover have "e' \<in> f ` A"
    by (metis imageI unit dom.submonoidsD(3)[OF A0])
  ultimately show ?thesis
    by (simp add:cod.submonoids_def)
qed

lemma vimage_submonoid:
  assumes A0:"B \<in> cod.submonoids"
  shows "X \<inter> f -` B \<in> dom.submonoids"
proof-
  have "X \<inter> f -` B \<in> dom.subs"
    using A0 by (intro vimage_sub) (simp add:cod.submonoids_def)
  moreover have "e \<in> X \<inter> f -` B"
    using cod.submonoidsD(3)[OF A0] unit by simp
  ultimately show ?thesis
    by (simp add:dom.submonoids_def)
qed

lemma im_submonoid:"f ` X \<in> cod.submonoids"
  by (rule image_submonoid[OF dom.submon.whole])

lemma im_monoid:"monoid (f ` X) (\<star>) e'"
  by (rule cod.sub_monoid[OF im_submonoid])

end

lemma monoid_hom_compose:
  assumes A0:"monoid_hom X mul e Y mul' e' f" and A1:"monoid_hom Y mul' e' Z mul'' e'' g"
  shows "monoid_hom X mul e Z mul'' e'' (g \<circ> f)"
proof-
  interpret f:monoid_hom X mul e Y mul' e' f by (rule A0)
  interpret g:monoid_hom Y mul' e' Z mul'' e'' g by (rule A1)
  show ?thesis
  proof(intro monoid_hom.intro monoid_hom_axioms.intro f.dom.monoid_axioms g.cod.monoid_axioms)
    show "magma_hom X mul Z mul'' (g \<circ> f)"
      by (rule magma_hom_compose[OF f.magma_hom_axioms g.magma_hom_axioms])
    show "(g \<circ> f) e = e''"
      by (simp add:f.unit g.unit)
  qed
qed

locale monoid_iso = monoid_hom +
  assumes bij:"bij_betw f X Y"

sublocale monoid_iso \<subseteq> magma_iso X mul Y mul' f
  by unfold_locales (rule bij)

lemma (in monoid_iso) inv_monoid_iso:"monoid_iso Y (\<star>) e' X (\<cdot>) e (inv_into X f)"
proof-
  interpret i:magma_iso Y "(\<star>)" X "(\<cdot>)" "inv_into X f"
    by (rule inv_iso)
  show ?thesis
  proof(intro monoid_iso.intro monoid_iso_axioms.intro monoid_hom.intro monoid_hom_axioms.intro
              i.magma_hom_axioms cod.monoid_axioms dom.monoid_axioms)
    show "inv_into X f e' = e"
      using unit inv_f[of e] by simp
    show "bij_betw (inv_into X f) Y X"
      by (rule i.bij)
  qed
qed


locale monoid_action = monoid M mul e + action M E \<alpha>
  for M::"'a set" and mul::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::'a ("\<one>") and E::"'b set" and \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b" +
  assumes act_unit:"x \<in> E \<Longrightarrow> \<alpha> \<one> x = x"
    and act_assoc:"\<lbrakk>m \<in> M; n \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> \<alpha> (m \<cdot> n) x = \<alpha> m (\<alpha> n x)"
begin

lemma l_law_unit:"l_law \<one> = Id E"
proof-
  have "l_law \<one> = (\<lambda>x\<in>E. \<alpha> \<one> x)"
    by (simp add:l_law_def)
  also have "\<dots> = Id E"
    by (rule restrict_ext) (simp add:act_unit)
  finally show ?thesis .
qed

lemma l_law_comp:
  assumes A0:"m \<in> M" and A1:"n \<in> M"
  shows "l_law (m \<cdot> n) = compose E (l_law m) (l_law n)"
proof-
  have "l_law (m \<cdot> n) = (\<lambda>x\<in>E. \<alpha> (m \<cdot> n) x)"
    using A0 A1 by (simp add:l_law_def)
  also have "\<dots> = (\<lambda>x\<in>E. \<alpha> m (\<alpha> n x))"
    by (rule restrict_ext) (simp add:act_assoc A0 A1)
  also have "\<dots> = compose E (l_law m) (l_law n)"
    unfolding compose_def by (rule restrict_ext) (simp add:l_law_app A0 A1)
  finally show ?thesis .
qed

lemma l_law_hom:"monoid_hom M (\<cdot>) \<one> (set_mor E E) (compose E) (Id E) l_law"
proof-
  interpret endo:set_endomorphisms E .
  show ?thesis
  proof(intro monoid_hom.intro magma_hom.intro magma_hom_axioms.intro monoid_hom_axioms.intro
              magma_axioms endo.magma_axioms monoid_axioms endo.monoid_axioms)
    show "\<And>m. m \<in> M \<Longrightarrow> l_law m \<in> set_mor E E"
      by (rule l_law_maps)
    show "\<And>m n. \<lbrakk>m \<in> M; n \<in> M\<rbrakk> \<Longrightarrow> l_law (m \<cdot> n) = compose E (l_law m) (l_law n)"
      by (rule l_law_comp)
    show "l_law \<one> = Id E"
      by (rule l_law_unit)
  qed
qed

lemma orbit_refl:"x \<in> E \<Longrightarrow> x \<in> orbit x"
  using act_unit[of x] by (auto simp:orbit_def intro:bexI[where x = \<one>])

lemma orbit_trans:"\<lbrakk>x \<in> E; y \<in> orbit x\<rbrakk> \<Longrightarrow> orbit y \<subseteq> orbit x"
proof
  fix z assume A0:"x \<in> E" and A1:"y \<in> orbit x" and A2:"z \<in> orbit y"
  obtain m where B0:"m \<in> M" and B1:"y = \<alpha> m x"
    using A1 by (auto simp:orbit_def)
  obtain n where B2:"n \<in> M" and B3:"z = \<alpha> n y"
    using A2 by (auto simp:orbit_def)
  have "z = \<alpha> (n \<cdot> m) x"
    using A0 B0 B2 by (simp add:B3 B1 act_assoc)
  then show "z \<in> orbit x"
    using B0 B2 by (auto simp:orbit_def)
qed

lemma orbit_invariant:"x \<in> E \<Longrightarrow> invariant (orbit x)"
  using orbit_trans orbit_refl by (auto simp:invariant_orbit orbit_sub)

lemma orbit_cl:
  assumes A0:"x \<in> E"
  shows "moore_family.cl {A. invariant A} {x} = orbit x"
proof-
  interpret invariants:moore_family E "{A. invariant A}"
    by (rule invariants_moore)
  show ?thesis
  proof
    show "invariants.cl {x} \<subseteq> orbit x"
      using orbit_invariant[OF A0] orbit_refl[OF A0] by (intro invariants.cl_least) simp_all
    have B0:"invariant (invariants.cl {x})" and B1:"x \<in> invariants.cl {x}"
      using A0 invariants.cl_closed[of "{x}"] invariants.cl_extensive[of "{x}"] by auto
    show "orbit x \<subseteq> invariants.cl {x}"
    proof
      fix y assume "y \<in> orbit x"
      then obtain m where "m \<in> M" and "y = \<alpha> m x"
        by (auto simp:orbit_def)
      then show "y \<in> invariants.cl {x}"
        using invariantD2[OF B0 _ B1] by simp
    qed
  qed
qed

lemma stabilizer_submonoid:
  assumes A0:"x \<in> E"
  shows "stabilizer x \<in> submonoids"
proof(rule submonoidsI)
  show "stabilizer x \<subseteq> M"
    by (rule stabilizer_sub)
  show "\<one> \<in> stabilizer x"
    using A0 by (simp add:stabilizer_def act_unit)
  fix m n assume "m \<in> stabilizer x" and "n \<in> stabilizer x"
  then show "m \<cdot> n \<in> stabilizer x"
    using A0 by (simp add:stabilizer_def act_assoc)
qed

end

lemma (in monoid) monoid_actionI:
  assumes A0:"monoid_hom X (\<cdot>) \<one> (set_mor E E) (compose E) (Id E) \<phi>"
  shows "monoid_action X (\<cdot>) \<one> E (\<lambda>m x. \<phi> m x)"
proof-
  interpret phi:monoid_hom X "(\<cdot>)" \<one> "set_mor E E" "compose E" "Id E" \<phi>
    by (rule A0)
  show ?thesis
  proof(unfold_locales)
    show "\<And>m x. \<lbrakk>m \<in> X; x \<in> E\<rbrakk> \<Longrightarrow> \<phi> m x \<in> E"
      by (rule set_morphisms_memE1[OF phi.maps])
    show "\<And>x. x \<in> E \<Longrightarrow> \<phi> \<one> x = x"
      using phi.unit by simp
    show "\<And>m n x. \<lbrakk>m \<in> X; n \<in> X; x \<in> E\<rbrakk> \<Longrightarrow> \<phi> (m \<cdot> n) x = \<phi> m (\<phi> n x)"
      by (simp add:phi.hom comp_eq)
  qed
qed

sublocale monoid \<subseteq> self:monoid_action X "(\<cdot>)" \<one> X "(\<cdot>)"
  by (intro monoid_action.intro monoid_action_axioms.intro monoid_axioms l_action.action_axioms) (simp_all add:assoc)

lemma (in set_endomorphisms) endo_monoid_action:"monoid_action (set_mor E E) (compose E) (Id E) E (\<lambda>f x. f x)"
proof(unfold_locales)
  fix f x assume "f \<in> set_mor E E" and "x \<in> E"
  then show "f x \<in> E"
    by (rule set_morphisms_memE1)
next
  fix f g x assume "f \<in> set_mor E E" and "g \<in> set_mor E E" and "x \<in> E"
  then show "compose E f g x = f (g x)"
    by (simp add:comp_eq)
qed simp

locale transformation_monoid = set_endomorphisms E for E::"'a set" +
  fixes M::"('a \<Rightarrow> 'a) set"
  assumes M_submonoid:"M \<in> submonoids"
begin

sublocale tr:monoid M "compose E" "Id E"
  by (rule sub_monoid[OF M_submonoid])

lemma tr_maps:"f \<in> M \<Longrightarrow> f \<in> set_mor E E"
  using submonoidsD(1)[OF M_submonoid] by auto

lemma tr_closed[intro, simp]:"\<lbrakk>f \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> f x \<in> E"
  by (rule set_morphisms_memE1[OF tr_maps])

lemma tr_undef[intro, simp]:"\<lbrakk>f \<in> M; x \<notin> E\<rbrakk> \<Longrightarrow> f x = undefined"
  by (rule set_morphisms_memE4[OF tr_maps])

sublocale tr_action:monoid_action M "compose E" "Id E" E "\<lambda>f x. f x"
proof(intro monoid_action.intro monoid_action_axioms.intro tr.monoid_axioms action.intro)
  show "\<And>f x. \<lbrakk>f \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> f x \<in> E"
    by (rule tr_closed)
  show "\<And>x. x \<in> E \<Longrightarrow> (Id E) x = x"
    by simp
  show "\<And>f g x. \<lbrakk>f \<in> M; g \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> compose E f g x = f (g x)"
    by (simp add:comp_eq)
qed

end

context monoid
begin

lemma opp_inv:"opp.inv x = inv x"
proof-
  have "(\<lambda>v. v \<in> X \<and> x \<cdot> v = \<one> \<and> v \<cdot> x = \<one>) = (\<lambda>v. v \<in> X \<and> v \<cdot> x = \<one> \<and> x \<cdot> v = \<one>)"
    by (rule ext) auto
  then show ?thesis
    by (simp add:opp.inv_def inv_def)
qed

lemma opp_invertible:"opp.invertible x \<longleftrightarrow> invertible x"
  by (auto simp:opp.invertible_def invertible_def)

lemma opp_Units:"opp.Units = Units"
  by (simp add:opp.Units_def Units_def opp_invertible)

end

sublocale group \<subseteq> opp:group X "\<lambda>x y. y \<cdot> x" \<one>
  by (rule opp_group)

context group
begin

lemma l_cancel1:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X; a \<cdot> x = a \<cdot> y\<rbrakk> \<Longrightarrow> x = y"
  and r_cancel1:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X; x \<cdot> a = y \<cdot> a\<rbrakk> \<Longrightarrow> x = y"
  by simp_all

lemma l_cancel_iff[simp]:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> a \<cdot> x = a \<cdot> y \<longleftrightarrow> x = y"
  and r_cancel_iff[simp]:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x \<cdot> a = y \<cdot> a \<longleftrightarrow> x = y"
  by simp_all

lemma group_cancellable:"x \<in> X \<Longrightarrow> cancellable x"
  by (simp add:invertible_cancellable)

lemma inv_inv[simp]:"x \<in> X \<Longrightarrow> inv (inv x) = x"
  by simp

lemma inv_unit_iff[simp]:"x \<in> X \<Longrightarrow> inv x = \<one> \<longleftrightarrow> x = \<one>"
proof
  assume A0:"x \<in> X" and A1:"inv x = \<one>"
  have "x = inv (inv x)"
    using A0 by simp
  then show "x = \<one>"
    by (simp add:A1)
qed simp

lemma inv_commute:
  assumes A0:"x \<cdot> y = \<one>" and A1:"x \<in> X" and A2:"y \<in> X"
  shows "y \<cdot> x = \<one>"
proof-
  have "inv x = y"
    by (rule inverse_unique[OF A0 inv_left[OF A1] A1 inv_closed[OF A1] A2])
  then show ?thesis
    using inv_left[OF A1] by simp
qed

lemma inv_eq_right:"\<lbrakk>x \<cdot> y = \<one>; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x = y"
  by (rule inv_eq) (simp_all add:inv_commute)

lemma inv_eq_left:"\<lbrakk>y \<cdot> x = \<one>; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x = y"
  by (rule inv_eq) (simp_all add:inv_commute)

lemma inv_lsolve1:
  assumes A0:"a \<in> X" and A1:"b \<in> X" and A2:"c \<in> X"
  shows "a = inv b \<cdot> c \<longleftrightarrow> c = b \<cdot> a"
proof
  assume "a = inv b \<cdot> c"
  then show "c = b \<cdot> a"
    using inv_rcancel[of b c] A1 A2 by simp
next
  assume "c = b \<cdot> a"
  then show "a = inv b \<cdot> c"
    using inv_lcancel[of b a] A0 A1 by simp
qed

lemma inv_rsolve1:
  assumes A0:"a \<in> X" and A1:"b \<in> X" and A2:"c \<in> X"
  shows "a = b \<cdot> inv c \<longleftrightarrow> b = a \<cdot> c"
proof
  assume "a = b \<cdot> inv c"
  then show "b = a \<cdot> c"
    using A1 A2 by (simp add:assoc)
next
  assume "b = a \<cdot> c"
  then show "a = b \<cdot> inv c"
    using A0 A2 by (simp add:assoc)
qed

lemma inv_lsolve2:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> inv b \<cdot> c = a \<longleftrightarrow> c = b \<cdot> a"
  and inv_rsolve2:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> b \<cdot> inv c = a \<longleftrightarrow> b = a \<cdot> c"
  using inv_lsolve1 inv_rsolve1 by (metis)+

lemma insert_id1:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (c \<cdot> inv c) \<cdot> b"
  and insert_id2:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> a \<cdot> b = a \<cdot> (inv c \<cdot> c) \<cdot> b"
  by simp_all

lemma remove_id1:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<cdot> inv c) \<cdot> (c \<cdot> b) = a \<cdot> b"
  and remove_id2:"\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> (a \<cdot> c) \<cdot> (inv c \<cdot> b) = a \<cdot> b"
  using assoc4[of a "inv c" c b] assoc4[of a c "inv c" b] by simp_all

lemma inj_on_cmult:"c \<in> X \<Longrightarrow> inj_on (\<lambda>x. c \<cdot> x) X"
  by (rule inj_onI) simp

lemma inj_on_multc:"c \<in> X \<Longrightarrow> inj_on (\<lambda>x. x \<cdot> c) X"
  by (rule inj_onI) simp

lemma l_trans_bij:
  assumes A0:"a \<in> X"
  shows "bij_betw (l_trans a) X X"
proof(rule bij_betwI2[where g = "l_trans (inv a)"])
  show "l_trans a \<in> maps_to X X" and "l_trans (inv a) \<in> maps_to X X"
    using A0 by (auto simp:l_trans_app)
  show "\<And>x. x \<in> X \<Longrightarrow> l_trans (inv a) (l_trans a x) = x"
    and "\<And>y. y \<in> X \<Longrightarrow> l_trans a (l_trans (inv a) y) = y"
    using A0 by (simp_all add:l_trans_app inv_lcancel inv_rcancel)
qed

lemma r_trans_bij:
  assumes A0:"a \<in> X"
  shows "bij_betw (r_trans a) X X"
proof(rule bij_betwI2[where g = "r_trans (inv a)"])
  show "r_trans a \<in> maps_to X X" and "r_trans (inv a) \<in> maps_to X X"
    using A0 by (auto simp:r_trans_app)
  show "\<And>x. x \<in> X \<Longrightarrow> r_trans (inv a) (r_trans a x) = x"
    and "\<And>y. y \<in> X \<Longrightarrow> r_trans a (r_trans (inv a) y) = y"
    using A0 by (simp_all add:r_trans_app assoc)
qed

definition set_inv::"'a set \<Rightarrow> 'a set"
  where "set_inv H = inv ` H"

lemma set_inv_iff:"x \<in> set_inv H \<longleftrightarrow> (\<exists>h\<in>H. x = inv h)"
  by (auto simp:set_inv_def)

lemma set_inv_memI:"\<lbrakk>h \<in> H; x = inv h\<rbrakk> \<Longrightarrow> x \<in> set_inv H"
  and set_inv_memI2:"h \<in> H \<Longrightarrow> inv h \<in> set_inv H"
  by (auto simp:set_inv_def)

lemma set_inv_sub:"H \<subseteq> X \<Longrightarrow> set_inv H \<subseteq> X"
  by (auto simp:set_inv_def)

lemma set_inv_iso:"A \<subseteq> B \<Longrightarrow> set_inv A \<subseteq> set_inv B"
  by (auto simp:set_inv_def)

lemma set_inv_set_inv:
  assumes A0:"H \<subseteq> X"
  shows "set_inv (set_inv H) = H"
proof
  show "set_inv (set_inv H) \<subseteq> H"
    using A0 by (auto simp:set_inv_def)
  show "H \<subseteq> set_inv (set_inv H)"
  proof
    fix h assume B0:"h \<in> H"
    then have "h = inv (inv h)"
      using A0 by auto
    then show "h \<in> set_inv (set_inv H)"
      using set_inv_memI[OF set_inv_memI2[OF B0]] by simp
  qed
qed

lemma set_inv_set_prod:
  assumes A0:"A \<subseteq> X" and A1:"B \<subseteq> X"
  shows "set_inv (set_prod A B) = set_prod (set_inv B) (set_inv A)"
proof
  show "set_inv (set_prod A B) \<subseteq> set_prod (set_inv B) (set_inv A)"
  proof
    fix z assume "z \<in> set_inv (set_prod A B)"
    then obtain p where B0:"p \<in> set_prod A B" and B1:"z = inv p"
      by (auto simp:set_inv_iff)
    obtain a b where B2:"a \<in> A" and B3:"b \<in> B" and B4:"p = a \<cdot> b"
      using B0 by (rule set_prod_memE)
    have "z = inv b \<cdot> inv a"
      using A0 A1 B2 B3 by (simp add:B1 B4 prod_inv subset_iff)
    then show "z \<in> set_prod (set_inv B) (set_inv A)"
      using set_prod_memI[OF set_inv_memI2[OF B3] set_inv_memI2[OF B2]] by simp
  qed
  show "set_prod (set_inv B) (set_inv A) \<subseteq> set_inv (set_prod A B)"
  proof
    fix z assume "z \<in> set_prod (set_inv B) (set_inv A)"
    then obtain p q where B0:"p \<in> set_inv B" and B1:"q \<in> set_inv A" and B2:"z = p \<cdot> q"
      by (rule set_prod_memE)
    obtain b where B3:"b \<in> B" and B4:"p = inv b"
      using B0 by (auto simp:set_inv_iff)
    obtain a where B5:"a \<in> A" and B6:"q = inv a"
      using B1 by (auto simp:set_inv_iff)
    have "z = inv (a \<cdot> b)"
      using A0 A1 B3 B5 by (simp add:B2 B4 B6 prod_inv subset_iff)
    then show "z \<in> set_inv (set_prod A B)"
      by (rule set_inv_memI[OF set_prod_memI[OF B5 B3]])
  qed
qed

lemma set_inv_singleton:"set_inv {a} = {inv a}"
  by (simp add:set_inv_def)

lemma set_inv_l_coset:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> set_inv (l_coset a H) = r_coset (set_inv H) (inv a)"
  and set_inv_r_coset:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> set_inv (r_coset H a) = l_coset (inv a) (set_inv H)"
  by (simp_all add:l_coset_singleton_prod r_coset_singleton_prod set_inv_set_prod set_inv_singleton)

lemma l_coset_image:"l_coset a A = (\<lambda>x. a \<cdot> x) ` A"
  and r_coset_image:"r_coset A a = (\<lambda>x. x \<cdot> a) ` A"
  by (auto simp:l_coset_def r_coset_def)

lemma l_coset_cancel:"\<lbrakk>A \<subseteq> X; b \<in> X; x \<in> l_coset b A\<rbrakk> \<Longrightarrow> inv b \<cdot> x \<in> A"
  and r_coset_cancel:"\<lbrakk>A \<subseteq> X; b \<in> X; x \<in> r_coset A b\<rbrakk> \<Longrightarrow> x \<cdot> inv b \<in> A"
  by (auto simp:l_coset_def r_coset_def inv_lcancel assoc subset_iff)

lemma l_coset_mem_iff:
  assumes A0:"A \<subseteq> X" and A1:"b \<in> X" and A2:"x \<in> X"
  shows "x \<in> l_coset b A \<longleftrightarrow> inv b \<cdot> x \<in> A"
proof
  assume "inv b \<cdot> x \<in> A"
  then have "b \<cdot> (inv b \<cdot> x) \<in> l_coset b A"
    by (rule l_coset_memI)
  then show "x \<in> l_coset b A"
    using A1 A2 by (simp add:inv_rcancel)
qed (rule l_coset_cancel[OF A0 A1])

lemma r_coset_mem_iff:
  assumes A0:"A \<subseteq> X" and A1:"b \<in> X" and A2:"x \<in> X"
  shows "x \<in> r_coset A b \<longleftrightarrow> x \<cdot> inv b \<in> A"
proof
  assume "x \<cdot> inv b \<in> A"
  then have "(x \<cdot> inv b) \<cdot> b \<in> r_coset A b"
    by (rule r_coset_memI)
  then show "x \<in> r_coset A b"
    using A1 A2 by (simp add:assoc)
qed (rule r_coset_cancel[OF A0 A1])

lemma l_coset_stab:"\<lbrakk>a \<in> X; b \<in> X; H \<subseteq> X; l_coset b H = H\<rbrakk> \<Longrightarrow> l_coset (a \<cdot> b) H = l_coset a H"
  and r_coset_stab:"\<lbrakk>a \<in> X; b \<in> X; H \<subseteq> X; r_coset H a = H\<rbrakk> \<Longrightarrow> r_coset H (a \<cdot> b) = r_coset H b"
  by (simp_all add:l_coset_assoc[symmetric] r_coset_assoc[symmetric])

lemma inv_prod_l_coset1:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"H \<subseteq> X" and A3:"l_coset (inv x \<cdot> y) H = H"
  shows "l_coset x H = l_coset y H"
proof-
  have "l_coset y H = l_coset (x \<cdot> (inv x \<cdot> y)) H"
    using A0 A1 by (simp add:inv_rcancel)
  also have "\<dots> = l_coset x (l_coset (inv x \<cdot> y) H)"
    using A0 A1 A2 by (simp add:l_coset_assoc)
  finally show ?thesis
    by (simp add:A3)
qed

lemma inv_prod_l_coset2:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"H \<subseteq> X" and A3:"l_coset x H = l_coset y H"
  shows "l_coset (inv x \<cdot> y) H = H"
proof-
  have "l_coset (inv x \<cdot> y) H = l_coset (inv x) (l_coset y H)"
    using A0 A1 A2 by (simp add:l_coset_assoc)
  also have "\<dots> = l_coset (inv x) (l_coset x H)"
    by (simp add:A3)
  also have "\<dots> = l_coset (inv x \<cdot> x) H"
    using A0 A2 by (simp add:l_coset_assoc)
  finally show ?thesis
    using A0 A2 by simp
qed

lemma inv_prod_r_coset1:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"H \<subseteq> X" and A3:"r_coset H (x \<cdot> inv y) = H"
  shows "r_coset H x = r_coset H y"
proof-
  have "r_coset H x = r_coset H ((x \<cdot> inv y) \<cdot> y)"
    using A0 A1 by (simp add:assoc)
  also have "\<dots> = r_coset (r_coset H (x \<cdot> inv y)) y"
    using A0 A1 A2 by (simp add:r_coset_assoc)
  finally show ?thesis
    by (simp add:A3)
qed

lemma inv_prod_r_coset2:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"H \<subseteq> X" and A3:"r_coset H x = r_coset H y"
  shows "r_coset H (x \<cdot> inv y) = H"
proof-
  have "r_coset H (x \<cdot> inv y) = r_coset (r_coset H x) (inv y)"
    using A0 A1 A2 by (simp add:r_coset_assoc)
  also have "\<dots> = r_coset (r_coset H y) (inv y)"
    by (simp add:A3)
  also have "\<dots> = r_coset H (y \<cdot> inv y)"
    using A1 A2 by (simp add:r_coset_assoc)
  finally show ?thesis
    using A1 A2 by simp
qed

lemma l_coset_eq_iff:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"H \<subseteq> X"
  shows "l_coset x H = l_coset y H \<longleftrightarrow> l_coset (inv x \<cdot> y) H = H"
  using inv_prod_l_coset1[OF A0 A1 A2] inv_prod_l_coset2[OF A0 A1 A2] by blast

lemma r_coset_eq_iff:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"H \<subseteq> X"
  shows "r_coset H x = r_coset H y \<longleftrightarrow> r_coset H (x \<cdot> inv y) = H"
  using inv_prod_r_coset1[OF A0 A1 A2] inv_prod_r_coset2[OF A0 A1 A2] by blast

lemma l_coset_bij:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> bij_betw (\<lambda>x. a \<cdot> x) H (l_coset a H)"
  and r_coset_bij:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> bij_betw (\<lambda>x. x \<cdot> a) H (r_coset H a)"
  by (simp_all add:bij_betw_def l_coset_image r_coset_image inj_on_subset[OF inj_on_cmult] inj_on_subset[OF inj_on_multc])

lemma l_coset_card:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> card (l_coset a H) = card H"
  by (rule bij_betw_same_card[OF l_coset_bij, symmetric])

lemma r_coset_card:"\<lbrakk>a \<in> X; H \<subseteq> X\<rbrakk> \<Longrightarrow> card (r_coset H a) = card H"
  by (rule bij_betw_same_card[OF r_coset_bij, symmetric])

lemma l_coset_finite:"\<lbrakk>finite H; a \<in> X\<rbrakk> \<Longrightarrow> finite (l_coset a H)"
  and r_coset_finite:"\<lbrakk>finite H; a \<in> X\<rbrakk> \<Longrightarrow> finite (r_coset H a)"
  by (simp_all add:l_coset_image r_coset_image)

end


locale subgroup = group +
  fixes H::"'a set"
  assumes subset:"H \<subseteq> X"
    and sub_closed:"\<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
    and id_mem:"\<one> \<in> H"
    and inv_cl:"a \<in> H \<Longrightarrow> inv a \<in> H"
begin

lemma sub_mem[intro, simp]:"a \<in> H \<Longrightarrow> a \<in> X"
  using subset by auto

lemma submonoids_mem:"H \<in> submonoids"
  by (rule submonoidsI[OF subset sub_closed id_mem])

lemma subgroups_mem:"H \<in> subgroups"
  using submonoids_mem inv_cl by (auto simp:subgroups_def)

sublocale sub:group H "(\<cdot>)" \<one>
proof(rule group.intro[OF sub_monoid[OF submonoids_mem]], rule group_axioms.intro)
  fix x assume B0:"x \<in> H"
  then show "\<exists>y\<in>H. y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"
    using inv_cl[OF B0] by (intro bexI[where x = "inv x"]) simp_all
qed

lemma sub_inv_eq[simp]:"a \<in> H \<Longrightarrow> sub.inv a = inv a"
  by (rule submonoid_invertible(3)[OF submonoids_mem sub.invertible])

lemma sub_group:"group H (\<cdot>) \<one>"
  by (rule sub.group_axioms)

lemma sub_set_inv:"set_inv H = H"
proof
  show "set_inv H \<subseteq> H"
    using inv_cl by (auto simp:set_inv_def)
  show "H \<subseteq> set_inv H"
  proof
    fix h assume B0:"h \<in> H"
    then have "h = inv (inv h)"
      by simp
    then show "h \<in> set_inv H"
      using set_inv_memI[OF inv_cl[OF B0]] by simp
  qed
qed

lemma sub_set_prod:"set_prod H H = H"
proof
  show "set_prod H H \<subseteq> H"
    using sub_closed by (auto simp:set_prod_def)
  show "H \<subseteq> set_prod H H"
  proof
    fix h assume "h \<in> H"
    then have "h = h \<cdot> \<one>"
      by simp
    then show "h \<in> set_prod H H"
      using set_prod_memI[of h H \<one> H] \<open>h \<in> H\<close> id_mem by simp
  qed
qed

lemma l_coset_absorb_iff:
  assumes A0:"a \<in> X"
  shows "l_coset a H = H \<longleftrightarrow> a \<in> H"
proof
  assume B0:"l_coset a H = H"
  have "a \<in> l_coset a H"
    using l_coset_memI[OF id_mem, of a] A0 by simp
  then show "a \<in> H"
    by (simp add:B0)
next
  assume B0:"a \<in> H"
  show "l_coset a H = H"
  proof
    show "l_coset a H \<subseteq> H"
      using B0 sub_closed by (auto simp:l_coset_def)
    show "H \<subseteq> l_coset a H"
    proof
      fix h assume C0:"h \<in> H"
      have "inv a \<cdot> h \<in> H"
        using B0 C0 by (simp add:sub_closed inv_cl)
      then show "h \<in> l_coset a H"
        using l_coset_mem_iff[OF subset A0] C0 by simp
    qed
  qed
qed

lemma r_coset_absorb_iff:
  assumes A0:"a \<in> X"
  shows "r_coset H a = H \<longleftrightarrow> a \<in> H"
proof
  assume B0:"r_coset H a = H"
  have "a \<in> r_coset H a"
    using r_coset_memI[OF id_mem, of a] A0 by simp
  then show "a \<in> H"
    by (simp add:B0)
next
  assume B0:"a \<in> H"
  show "r_coset H a = H"
  proof
    show "r_coset H a \<subseteq> H"
      using B0 sub_closed by (auto simp:r_coset_def)
    show "H \<subseteq> r_coset H a"
    proof
      fix h assume C0:"h \<in> H"
      have "h \<cdot> inv a \<in> H"
        using B0 C0 by (simp add:sub_closed inv_cl)
      then show "h \<in> r_coset H a"
        using r_coset_mem_iff[OF subset A0] C0 by simp
    qed
  qed
qed

lemma lcoset_absorb:"a \<in> X \<Longrightarrow> a \<in> l_coset a H"
  using l_coset_memI[OF id_mem, of a] by simp

lemma rcoset_absorb:"a \<in> X \<Longrightarrow> a \<in> r_coset H a"
  using r_coset_memI[OF id_mem, of a] by simp

lemma lcoset_mem:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x \<cdot> y \<in> H \<longleftrightarrow> y \<in> l_coset x H"
  and rcoset_mem:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> y \<cdot> inv x \<in> H \<longleftrightarrow> y \<in> r_coset H x"
  by (simp_all add:l_coset_mem_iff[OF subset] r_coset_mem_iff[OF subset])

lemma coset_eq_iff1:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> l_coset a H = l_coset b H \<longleftrightarrow> inv a \<cdot> b \<in> H"
  and coset_eq_iff3:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> r_coset H a = r_coset H b \<longleftrightarrow> a \<cdot> inv b \<in> H"
  by (simp_all add:l_coset_eq_iff[OF _ _ subset] r_coset_eq_iff[OF _ _ subset] l_coset_absorb_iff r_coset_absorb_iff)

lemma coset_eq_iff2:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> l_coset a H = l_coset b H \<longleftrightarrow> b \<in> l_coset a H"
  and coset_eq_iff4:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> r_coset H a = r_coset H b \<longleftrightarrow> a \<in> r_coset H b"
  by (simp_all add:coset_eq_iff1 coset_eq_iff3 lcoset_mem rcoset_mem)

lemma l_coset_eq_or_disjoint:
  assumes A0:"a \<in> X" and A1:"b \<in> X" and A2:"l_coset a H \<inter> l_coset b H \<noteq> {}"
  shows "l_coset a H = l_coset b H"
proof-
  obtain x where B0:"x \<in> l_coset a H" and B1:"x \<in> l_coset b H"
    using A2 by blast
  have B2:"x \<in> X"
    using B0 l_coset_sub[OF subset A0] by auto
  have "l_coset a H = l_coset x H"
    using coset_eq_iff2[OF A0 B2] B0 by simp
  also have "\<dots> = l_coset b H"
    using coset_eq_iff2[OF A1 B2] B1 by simp
  finally show ?thesis .
qed

lemma r_coset_eq_or_disjoint:
  assumes A0:"a \<in> X" and A1:"b \<in> X" and A2:"r_coset H a \<inter> r_coset H b \<noteq> {}"
  shows "r_coset H a = r_coset H b"
proof-
  obtain x where B0:"x \<in> r_coset H a" and B1:"x \<in> r_coset H b"
    using A2 by blast
  have B2:"x \<in> X"
    using B0 r_coset_sub[OF subset A0] by auto
  have "r_coset H a = r_coset H x"
    using coset_eq_iff4[OF B2 A0] B0 by simp
  also have "\<dots> = r_coset H b"
    using coset_eq_iff4[OF B2 A1] B1 by simp
  finally show ?thesis .
qed

lemma coset_bij1:
  assumes A0:"a \<in> X"
  shows "bij_betw inv (l_coset a H) (r_coset H (inv a))"
proof(rule bij_betwI2[where g = inv])
  have B0:"inv ` l_coset a H = r_coset H (inv a)"
    using set_inv_l_coset[OF A0 subset] sub_set_inv by (simp add:set_inv_def)
  have B1:"inv ` r_coset H (inv a) = l_coset a H"
    using set_inv_r_coset[OF inv_closed[OF A0] subset] sub_set_inv A0 by (simp add:set_inv_def)
  show "inv \<in> maps_to (l_coset a H) (r_coset H (inv a))"
    using B0 by auto
  show "inv \<in> maps_to (r_coset H (inv a)) (l_coset a H)"
    using B1 by auto
  show "\<And>x. x \<in> l_coset a H \<Longrightarrow> inv (inv x) = x"
    using l_coset_sub[OF subset A0] by auto
  show "\<And>y. y \<in> r_coset H (inv a) \<Longrightarrow> inv (inv y) = y"
    using r_coset_sub[OF subset inv_closed[OF A0]] by auto
qed

lemma coset_bij2:
  assumes A0:"a \<in> X" and A1:"b \<in> X"
  shows "bij_betw (\<lambda>x. (b \<cdot> inv a) \<cdot> x) (l_coset a H) (l_coset b H)"
proof-
  have B0:"(\<lambda>x. (b \<cdot> inv a) \<cdot> x) ` l_coset a H = l_coset b H"
  proof-
    have "(\<lambda>x. (b \<cdot> inv a) \<cdot> x) ` l_coset a H = l_coset (b \<cdot> inv a) (l_coset a H)"
      by (rule l_coset_image[symmetric])
    also have "\<dots> = l_coset ((b \<cdot> inv a) \<cdot> a) H"
      using A0 A1 subset by (simp add:l_coset_assoc)
    also have "\<dots> = l_coset b H"
      using A0 A1 by (simp add:assoc)
    finally show ?thesis .
  qed
  have B1:"inj_on (\<lambda>x. (b \<cdot> inv a) \<cdot> x) (l_coset a H)"
    by (rule inj_on_subset[OF inj_on_cmult l_coset_sub[OF subset A0]]) (simp add:A0 A1)
  show ?thesis
    using B0 B1 by (simp add:bij_betw_def)
qed

lemma l_cosets_memD:"t \<in> l_cosets H \<Longrightarrow> \<exists>g\<in>X. t = l_coset g H"
  and r_cosets_memD:"t \<in> r_cosets H \<Longrightarrow> \<exists>g\<in>X. t = r_coset H g"
  by (auto simp:l_cosets_def r_cosets_def)

lemma l_cosets_ne:"t \<in> l_cosets H \<Longrightarrow> t \<noteq> {}"
proof-
  assume "t \<in> l_cosets H"
  then obtain g where "g \<in> X" and "t = l_coset g H"
    by (rule l_cosets_memE)
  then show "t \<noteq> {}"
    using lcoset_absorb by blast
qed

lemma r_cosets_ne:"t \<in> r_cosets H \<Longrightarrow> t \<noteq> {}"
proof-
  assume "t \<in> r_cosets H"
  then obtain g where "g \<in> X" and "t = r_coset H g"
    by (rule r_cosets_memE)
  then show "t \<noteq> {}"
    using rcoset_absorb by blast
qed

lemma l_cosets_disj:
  assumes A0:"t \<in> l_cosets H" and A1:"s \<in> l_cosets H" and A2:"t \<inter> s \<noteq> {}"
  shows "t = s"
proof-
  obtain a where B0:"a \<in> X" and B1:"t = l_coset a H"
    using A0 by (rule l_cosets_memE)
  obtain b where B2:"b \<in> X" and B3:"s = l_coset b H"
    using A1 by (rule l_cosets_memE)
  show ?thesis
    using l_coset_eq_or_disjoint[OF B0 B2] A2 by (simp add:B1 B3)
qed

lemma r_cosets_disj:
  assumes A0:"t \<in> r_cosets H" and A1:"s \<in> r_cosets H" and A2:"t \<inter> s \<noteq> {}"
  shows "t = s"
proof-
  obtain a where B0:"a \<in> X" and B1:"t = r_coset H a"
    using A0 by (rule r_cosets_memE)
  obtain b where B2:"b \<in> X" and B3:"s = r_coset H b"
    using A1 by (rule r_cosets_memE)
  show ?thesis
    using r_coset_eq_or_disjoint[OF B0 B2] A2 by (simp add:B1 B3)
qed

lemma l_cosets_card:"t \<in> l_cosets H \<Longrightarrow> card t = card H"
proof-
  assume "t \<in> l_cosets H"
  then obtain g where "g \<in> X" and "t = l_coset g H"
    by (rule l_cosets_memE)
  then show "card t = card H"
    by (simp add:l_coset_card[OF _ subset])
qed

lemma r_cosets_card:"t \<in> r_cosets H \<Longrightarrow> card t = card H"
proof-
  assume "t \<in> r_cosets H"
  then obtain g where "g \<in> X" and "t = r_coset H g"
    by (rule r_cosets_memE)
  then show "card t = card H"
    by (simp add:r_coset_card[OF _ subset])
qed

lemma l_cosets_Union:"\<Union>(l_cosets H) = X"
proof
  show "\<Union>(l_cosets H) \<subseteq> X"
    using l_cosets_sub[OF subset] by auto
  show "X \<subseteq> \<Union>(l_cosets H)"
  proof
    fix x assume "x \<in> X"
    then have "x \<in> l_coset x H" and "l_coset x H \<in> l_cosets H"
      by (simp_all add:lcoset_absorb l_cosets_memI)
    then show "x \<in> \<Union>(l_cosets H)"
      by blast
  qed
qed

lemma r_cosets_Union:"\<Union>(r_cosets H) = X"
proof
  show "\<Union>(r_cosets H) \<subseteq> X"
    using r_cosets_sub[OF subset] by auto
  show "X \<subseteq> \<Union>(r_cosets H)"
  proof
    fix x assume "x \<in> X"
    then have "x \<in> r_coset H x" and "r_coset H x \<in> r_cosets H"
      by (simp_all add:rcoset_absorb r_cosets_memI)
    then show "x \<in> \<Union>(r_cosets H)"
      by blast
  qed
qed

lemma l_cosets_finite:"finite X \<Longrightarrow> finite (l_cosets H)"
  and r_cosets_finite:"finite X \<Longrightarrow> finite (r_cosets H)"
  using l_cosets_sub[OF subset] r_cosets_sub[OF subset] by (simp_all add:finite_subset)

theorem lagrange:
  assumes A0:"finite X"
  shows "card H * card (l_cosets H) = card X"
proof-
  have B0:"finite (l_cosets H)"
    by (rule l_cosets_finite[OF A0])
  have B1:"finite (\<Union>(l_cosets H))"
    by (simp add:l_cosets_Union A0)
  have B2:"\<And>t s. \<lbrakk>t \<in> l_cosets H; s \<in> l_cosets H; t \<noteq> s\<rbrakk> \<Longrightarrow> t \<inter> s = {}"
    using l_cosets_disj by blast
  show ?thesis
    using card_partition[OF B0 B1 l_cosets_card B2] by (simp add:l_cosets_Union)
qed

theorem lagrange_r:
  assumes A0:"finite X"
  shows "card H * card (r_cosets H) = card X"
proof-
  have B0:"finite (r_cosets H)"
    by (rule r_cosets_finite[OF A0])
  have B1:"finite (\<Union>(r_cosets H))"
    by (simp add:r_cosets_Union A0)
  have B2:"\<And>t s. \<lbrakk>t \<in> r_cosets H; s \<in> r_cosets H; t \<noteq> s\<rbrakk> \<Longrightarrow> t \<inter> s = {}"
    using r_cosets_disj by blast
  show ?thesis
    using card_partition[OF B0 B1 r_cosets_card B2] by (simp add:r_cosets_Union)
qed

theorem card_subgroup_dvd:"finite X \<Longrightarrow> card H dvd card X"
  using lagrange by (metis dvd_triv_left)

lemma card_l_cosets_r_cosets:
  assumes A0:"finite X"
  shows "card (l_cosets H) = card (r_cosets H)"
proof-
  have "card H \<noteq> 0"
    using id_mem finite_subset[OF subset A0] by (auto simp:card_eq_0_iff)
  then show ?thesis
    using lagrange[OF A0] lagrange_r[OF A0] by (metis mult_left_cancel)
qed

definition l_sub_eq::"'a rel"
  where "l_sub_eq = {(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> H}"

definition r_sub_eq::"'a rel"
  where "r_sub_eq = {(x, y). x \<in> X \<and> y \<in> X \<and> y \<cdot> inv x \<in> H}"

lemma l_sub_eq_iff:"(x, y) \<in> l_sub_eq \<longleftrightarrow> x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> H"
  and r_sub_eq_iff:"(x, y) \<in> r_sub_eq \<longleftrightarrow> x \<in> X \<and> y \<in> X \<and> y \<cdot> inv x \<in> H"
  by (simp_all add:l_sub_eq_def r_sub_eq_def)

lemma l_sub_eq_sub:"l_sub_eq \<subseteq> X \<times> X" and r_sub_eq_sub:"r_sub_eq \<subseteq> X \<times> X"
  by (auto simp:l_sub_eq_def r_sub_eq_def)

lemma l_sub_eq_refl:"x \<in> X \<Longrightarrow> (x, x) \<in> l_sub_eq"
  and r_sub_eq_refl:"x \<in> X \<Longrightarrow> (x, x) \<in> r_sub_eq"
  by (simp_all add:l_sub_eq_iff r_sub_eq_iff)

lemma l_sub_eq_sym:"(x, y) \<in> l_sub_eq \<Longrightarrow> (y, x) \<in> l_sub_eq"
proof-
  assume "(x, y) \<in> l_sub_eq"
  then have B0:"x \<in> X" and B1:"y \<in> X" and B2:"inv x \<cdot> y \<in> H"
    by (simp_all add:l_sub_eq_iff)
  have "inv y \<cdot> x = inv (inv x \<cdot> y)"
    using B0 B1 by (simp add:prod_inv)
  then have "inv y \<cdot> x \<in> H"
    using inv_cl[OF B2] by simp
  then show "(y, x) \<in> l_sub_eq"
    using B0 B1 by (simp add:l_sub_eq_iff)
qed

lemma r_sub_eq_sym:"(x, y) \<in> r_sub_eq \<Longrightarrow> (y, x) \<in> r_sub_eq"
proof-
  assume "(x, y) \<in> r_sub_eq"
  then have B0:"x \<in> X" and B1:"y \<in> X" and B2:"y \<cdot> inv x \<in> H"
    by (simp_all add:r_sub_eq_iff)
  have "x \<cdot> inv y = inv (y \<cdot> inv x)"
    using B0 B1 by (simp add:prod_inv)
  then have "x \<cdot> inv y \<in> H"
    using inv_cl[OF B2] by simp
  then show "(y, x) \<in> r_sub_eq"
    using B0 B1 by (simp add:r_sub_eq_iff)
qed

lemma l_sub_eq_trans:"\<lbrakk>(x, y) \<in> l_sub_eq; (y, z) \<in> l_sub_eq\<rbrakk> \<Longrightarrow> (x, z) \<in> l_sub_eq"
proof-
  assume "(x, y) \<in> l_sub_eq" and "(y, z) \<in> l_sub_eq"
  then have B0:"x \<in> X" and B1:"y \<in> X" and B2:"z \<in> X" and B3:"inv x \<cdot> y \<in> H" and B4:"inv y \<cdot> z \<in> H"
    by (simp_all add:l_sub_eq_iff)
  have "inv x \<cdot> z = (inv x \<cdot> y) \<cdot> (inv y \<cdot> z)"
    using B0 B1 B2 by (simp add:remove_id2)
  then have "inv x \<cdot> z \<in> H"
    using sub_closed[OF B3 B4] by simp
  then show "(x, z) \<in> l_sub_eq"
    using B0 B2 by (simp add:l_sub_eq_iff)
qed

lemma r_sub_eq_trans:"\<lbrakk>(x, y) \<in> r_sub_eq; (y, z) \<in> r_sub_eq\<rbrakk> \<Longrightarrow> (x, z) \<in> r_sub_eq"
proof-
  assume "(x, y) \<in> r_sub_eq" and "(y, z) \<in> r_sub_eq"
  then have B0:"x \<in> X" and B1:"y \<in> X" and B2:"z \<in> X" and B3:"y \<cdot> inv x \<in> H" and B4:"z \<cdot> inv y \<in> H"
    by (simp_all add:r_sub_eq_iff)
  have "z \<cdot> inv x = (z \<cdot> inv y) \<cdot> (y \<cdot> inv x)"
    using B0 B1 B2 by (simp add:remove_id1)
  then have "z \<cdot> inv x \<in> H"
    using sub_closed[OF B4 B3] by simp
  then show "(x, z) \<in> r_sub_eq"
    using B0 B2 by (simp add:r_sub_eq_iff)
qed

lemma l_sub_eq_equiv:"equiv X l_sub_eq"
  unfolding equiv_def refl_on_def sym_def trans_def
  using l_sub_eq_sub l_sub_eq_refl l_sub_eq_sym l_sub_eq_trans by blast

lemma r_sub_eq_equiv:"equiv X r_sub_eq"
  unfolding equiv_def refl_on_def sym_def trans_def
  using r_sub_eq_sub r_sub_eq_refl r_sub_eq_sym r_sub_eq_trans by blast

lemma l_sub_eq_l_cong:"l_cong l_sub_eq"
proof(rule l_congI1)
  fix a x y assume A0:"a \<in> X" and A1:"(x, y) \<in> l_sub_eq"
  have B0:"x \<in> X" and B1:"y \<in> X" and B2:"inv x \<cdot> y \<in> H"
    using A1 by (simp_all add:l_sub_eq_iff)
  have "inv (a \<cdot> x) \<cdot> (a \<cdot> y) = inv x \<cdot> (inv a \<cdot> a) \<cdot> y"
    using A0 B0 B1 by (simp add:prod_inv assoc4)
  then have "inv (a \<cdot> x) \<cdot> (a \<cdot> y) \<in> H"
    using A0 B0 B2 by simp
  then show "(a \<cdot> x, a \<cdot> y) \<in> l_sub_eq"
    using A0 B0 B1 by (simp add:l_sub_eq_iff)
qed

lemma r_sub_eq_r_cong:"r_cong r_sub_eq"
proof(rule r_congI1)
  fix a x y assume A0:"a \<in> X" and A1:"(x, y) \<in> r_sub_eq"
  have B0:"x \<in> X" and B1:"y \<in> X" and B2:"y \<cdot> inv x \<in> H"
    using A1 by (simp_all add:r_sub_eq_iff)
  have "(y \<cdot> a) \<cdot> inv (x \<cdot> a) = y \<cdot> (a \<cdot> inv a) \<cdot> inv x"
    using A0 B0 B1 by (simp add:prod_inv assoc4)
  then have "(y \<cdot> a) \<cdot> inv (x \<cdot> a) \<in> H"
    using A0 B1 B2 by simp
  then show "(x \<cdot> a, y \<cdot> a) \<in> r_sub_eq"
    using A0 B0 B1 by (simp add:r_sub_eq_iff)
qed

lemma l_sub_eq_class:
  assumes A0:"x \<in> X"
  shows "l_sub_eq `` {x} = l_coset x H"
proof
  show "l_sub_eq `` {x} \<subseteq> l_coset x H"
    using A0 by (auto simp:l_sub_eq_iff lcoset_mem)
  show "l_coset x H \<subseteq> l_sub_eq `` {x}"
  proof
    fix y assume B0:"y \<in> l_coset x H"
    then have B1:"y \<in> X"
      using l_coset_sub[OF subset A0] by auto
    then show "y \<in> l_sub_eq `` {x}"
      using A0 B0 by (simp add:l_sub_eq_iff lcoset_mem)
  qed
qed

lemma r_sub_eq_class:
  assumes A0:"x \<in> X"
  shows "r_sub_eq `` {x} = r_coset H x"
proof
  show "r_sub_eq `` {x} \<subseteq> r_coset H x"
    using A0 by (auto simp:r_sub_eq_iff rcoset_mem)
  show "r_coset H x \<subseteq> r_sub_eq `` {x}"
  proof
    fix y assume B0:"y \<in> r_coset H x"
    then have B1:"y \<in> X"
      using r_coset_sub[OF subset A0] by auto
    then show "y \<in> r_sub_eq `` {x}"
      using A0 B0 by (simp add:r_sub_eq_iff rcoset_mem)
  qed
qed

lemma l_sub_eq_quot:"X // l_sub_eq = l_cosets H"
  and r_sub_eq_quot:"X // r_sub_eq = r_cosets H"
  by (auto simp:quotient_def l_cosets_def r_cosets_def l_sub_eq_class r_sub_eq_class)

end

context group
begin

lemma subgroup_iff:"subgroup X (\<cdot>) \<one> H \<longleftrightarrow> H \<in> subgroups"
proof
  assume "subgroup X (\<cdot>) \<one> H"
  then interpret s:subgroup X "(\<cdot>)" \<one> H .
  show "H \<in> subgroups"
    by (rule s.subgroups_mem)
next
  assume A0:"H \<in> subgroups"
  then have B0:"H \<in> submonoids" and B1:"\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    by (auto simp:subgroups_def)
  show "subgroup X (\<cdot>) \<one> H"
    by (intro subgroup.intro group_axioms subgroup_axioms.intro submonoidsD[OF B0] B1)
qed

lemma subgroupI1:
  assumes A0:"H \<subseteq> X" and A1:"H \<noteq> {}" and A2:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
    and A3:"\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  shows "subgroup X (\<cdot>) \<one> H"
proof(intro subgroup.intro group_axioms subgroup_axioms.intro A0 A2 A3)
  obtain a where B0:"a \<in> H"
    using A1 by blast
  then have "inv a \<cdot> a \<in> H"
    by (simp add:A2 A3)
  then show "\<one> \<in> H"
    using A0 B0 by auto
qed

lemma subgroupI2:
  assumes A0:"H \<subseteq> X" and A1:"H \<noteq> {}" and A2:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> inv b \<in> H"
  shows "subgroup X (\<cdot>) \<one> H"
proof-
  obtain a where B0:"a \<in> H"
    using A1 by blast
  have B1:"\<one> \<in> H"
    using A2[OF B0 B0] A0 B0 by auto
  have B2:"\<And>b. b \<in> H \<Longrightarrow> inv b \<in> H"
  proof-
    fix b assume C0:"b \<in> H"
    then have "b \<in> X"
      using A0 by auto
    then show "inv b \<in> H"
      using A2[OF B1 C0] by simp
  qed
  have B3:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
  proof-
    fix a b assume C0:"a \<in> H" and C1:"b \<in> H"
    then have "b \<in> X"
      using A0 by auto
    then show "a \<cdot> b \<in> H"
      using A2[OF C0 B2[OF C1]] by simp
  qed
  show ?thesis
    by (intro subgroup.intro group_axioms subgroup_axioms.intro A0 B1 B2 B3)
qed

lemma subgroupI3:
  assumes A0:"H \<subseteq> X" and A1:"H \<noteq> {}" and A2:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> inv a \<cdot> b \<in> H"
  shows "subgroup X (\<cdot>) \<one> H"
proof-
  obtain a where B0:"a \<in> H"
    using A1 by blast
  have B1:"\<one> \<in> H"
    using A2[OF B0 B0] A0 B0 by auto
  have B2:"\<And>b. b \<in> H \<Longrightarrow> inv b \<in> H"
  proof-
    fix b assume C0:"b \<in> H"
    then have "b \<in> X"
      using A0 by auto
    then show "inv b \<in> H"
      using A2[OF C0 B1] by simp
  qed
  have B3:"\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
  proof-
    fix a b assume C0:"a \<in> H" and C1:"b \<in> H"
    then have "a \<in> X"
      using A0 by auto
    then show "a \<cdot> b \<in> H"
      using A2[OF B2[OF C0] C1] by simp
  qed
  show ?thesis
    by (intro subgroup.intro group_axioms subgroup_axioms.intro A0 B1 B2 B3)
qed

lemma subgroupD:
  assumes "subgroup X (\<cdot>) \<one> H"
  shows "H \<subseteq> X" and "H \<noteq> {}" and "\<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H" and "a \<in> H \<Longrightarrow> inv a \<in> H" and "\<one> \<in> H"
  using assms by (auto simp:subgroup_def subgroup_axioms_def)

lemma trivial_subgroup:"subgroup X (\<cdot>) \<one> {\<one>}"
  by (intro subgroup.intro group_axioms subgroup_axioms.intro) simp_all

lemma top_subgroup:"subgroup X (\<cdot>) \<one> X"
  by (intro subgroup.intro group_axioms subgroup_axioms.intro) simp_all

lemma subgroup_Int:
  assumes A0:"subgroup X (\<cdot>) \<one> H" and A1:"subgroup X (\<cdot>) \<one> K"
  shows "subgroup X (\<cdot>) \<one> (H \<inter> K)"
  using subgroupD[OF A0] subgroupD[OF A1] by (intro subgroup.intro group_axioms subgroup_axioms.intro) auto

lemma subgroup_Inter:
  assumes A0:"\<And>H. H \<in> \<H> \<Longrightarrow> subgroup X (\<cdot>) \<one> H" and A1:"\<H> \<noteq> {}"
  shows "subgroup X (\<cdot>) \<one> (\<Inter>\<H>)"
  using subgrp.Inter_closed[of \<H>] A0 A1 by (simp add:subgroup_iff subset_iff)

lemma subgroup_trans:
  assumes A0:"subgroup X (\<cdot>) \<one> H" and A1:"subgroup H (\<cdot>) \<one> K"
  shows "subgroup X (\<cdot>) \<one> K"
proof-
  interpret h:subgroup X "(\<cdot>)" \<one> H by (rule A0)
  interpret k:subgroup H "(\<cdot>)" \<one> K by (rule A1)
  show ?thesis
  proof(intro subgroup.intro group_axioms subgroup_axioms.intro)
    show "K \<subseteq> X"
      using k.subset h.subset by auto
    show "\<And>a b. \<lbrakk>a \<in> K; b \<in> K\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> K"
      by (rule k.sub_closed)
    show "\<one> \<in> K"
      by (rule k.id_mem)
    show "\<And>a. a \<in> K \<Longrightarrow> inv a \<in> K"
    proof-
      fix a assume "a \<in> K"
      then have "a \<in> H" and "monoid.inv H (\<cdot>) \<one> a \<in> K"
        using k.subset k.inv_cl by auto
      then show "inv a \<in> K"
        by simp
    qed
  qed
qed

end


locale normal_subgroup = subgroup +
  assumes normal:"\<lbrakk>g \<in> X; h \<in> H\<rbrakk> \<Longrightarrow> g \<cdot> h \<cdot> inv g \<in> H"
begin

lemma conj_closed:"\<lbrakk>g \<in> X; h \<in> H\<rbrakk> \<Longrightarrow> inv g \<cdot> h \<cdot> g \<in> H"
  using normal[of "inv g" h] by simp

lemma l_coset_eq_r_coset:
  assumes A0:"g \<in> X"
  shows "l_coset g H = r_coset H g"
proof
  show "l_coset g H \<subseteq> r_coset H g"
  proof
    fix x assume "x \<in> l_coset g H"
    then obtain h where B0:"h \<in> H" and B1:"x = g \<cdot> h"
      by (rule l_coset_memE)
    have "x = (g \<cdot> h \<cdot> inv g) \<cdot> g"
      using A0 B0 by (simp add:B1 assoc)
    then show "x \<in> r_coset H g"
      using normal[OF A0 B0] by (simp add:r_coset_memI)
  qed
  show "r_coset H g \<subseteq> l_coset g H"
  proof
    fix x assume "x \<in> r_coset H g"
    then obtain h where B0:"h \<in> H" and B1:"x = h \<cdot> g"
      by (rule r_coset_memE)
    have "x = g \<cdot> (inv g \<cdot> h \<cdot> g)"
      using A0 B0 by (simp add:B1 assoc[symmetric])
    then show "x \<in> l_coset g H"
      using conj_closed[OF A0 B0] by (simp add:l_coset_memI)
  qed
qed

lemma l_sub_eq_r_sub_eq:"l_sub_eq = r_sub_eq"
proof-
  have "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inv x \<cdot> y \<in> H \<longleftrightarrow> y \<cdot> inv x \<in> H"
  proof-
    fix x y assume A0:"x \<in> X" and A1:"y \<in> X"
    have B0:"x \<cdot> (inv x \<cdot> y) \<cdot> inv x = y \<cdot> inv x"
      using A0 A1 by (simp add:inv_rcancel)
    have B1:"inv x \<cdot> (y \<cdot> inv x) \<cdot> x = inv x \<cdot> y"
      using A0 A1 by (simp add:assoc)
    show "inv x \<cdot> y \<in> H \<longleftrightarrow> y \<cdot> inv x \<in> H"
      using normal[OF A0, of "inv x \<cdot> y"] conj_closed[OF A0, of "y \<cdot> inv x"] unfolding B0 B1 by blast
  qed
  then show ?thesis
    by (auto simp:l_sub_eq_def r_sub_eq_def)
qed

lemma l_sub_eq_r_cong:"r_cong l_sub_eq"
  using r_sub_eq_r_cong by (simp add:l_sub_eq_r_sub_eq)

lemma l_sub_eq_congruence:"congruence X (\<cdot>) l_sub_eq"
  by (rule congruenceI[OF l_sub_eq_equiv l_sub_eq_l_cong l_sub_eq_r_cong])

sublocale quo:congruence X "(\<cdot>)" l_sub_eq
  by (rule l_sub_eq_congruence)

lemma quo_cls:"x \<in> X \<Longrightarrow> quo.cls x = l_coset x H"
  by (simp add:quo.cls_def l_sub_eq_class)

lemma quo_quot:"quo.quot = l_cosets H"
  by (auto simp:quo.quot_def l_cosets_def quo_cls)

lemma quo_unit:"quo.cls \<one> = H"
  by (simp add:quo_cls subset)

lemma quo_qmul:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> quo.qmul (l_coset a H) (l_coset b H) = l_coset (a \<cdot> b) H"
  using quo.qmul_cls by (simp add:quo_cls)

lemma coset_set_prod:
  assumes A0:"a \<in> X" and A1:"b \<in> X"
  shows "set_prod (l_coset a H) (l_coset b H) = l_coset (a \<cdot> b) H"
proof-
  have "set_prod (l_coset a H) (l_coset b H) = set_prod (set_prod {a} H) (set_prod {b} H)"
    by (simp add:l_coset_singleton_prod)
  also have "\<dots> = set_prod {a} (set_prod (set_prod H {b}) H)"
    using A0 A1 subset by (simp add:set_prod_assoc set_prod_closed)
  also have "\<dots> = set_prod {a} (set_prod (set_prod {b} H) H)"
    using l_coset_eq_r_coset[OF A1] by (simp add:l_coset_singleton_prod r_coset_singleton_prod)
  also have "\<dots> = set_prod {a} (set_prod {b} (set_prod H H))"
    using A1 subset by (simp add:set_prod_assoc)
  also have "\<dots> = set_prod (set_prod {a} {b}) H"
    using A0 A1 subset by (simp add:sub_set_prod set_prod_assoc)
  finally show ?thesis
    by (simp add:set_prod_singleton l_coset_singleton_prod)
qed

end

lemma (in subgroup) normal_subgroupI1:
  assumes A0:"\<And>g. g \<in> X \<Longrightarrow> l_coset g H = r_coset H g"
  shows "normal_subgroup X (\<cdot>) \<one> H"
proof(intro normal_subgroup.intro subgroup_axioms normal_subgroup_axioms.intro)
  fix g h assume B0:"g \<in> X" and B1:"h \<in> H"
  have "g \<cdot> h \<in> r_coset H g"
    using l_coset_memI[OF B1, of g] by (simp add:A0[OF B0])
  then obtain k where B2:"k \<in> H" and B3:"g \<cdot> h = k \<cdot> g"
    by (rule r_coset_memE)
  have "g \<cdot> h \<cdot> inv g = k"
    using B0 B1 B2 by (simp add:B3 assoc)
  then show "g \<cdot> h \<cdot> inv g \<in> H"
    by (simp add:B2)
qed

lemma (in subgroup) normal_subgroupI2:
  assumes A0:"\<And>g. g \<in> X \<Longrightarrow> r_coset (l_coset g H) (inv g) \<subseteq> H"
  shows "normal_subgroup X (\<cdot>) \<one> H"
proof(intro normal_subgroup.intro subgroup_axioms normal_subgroup_axioms.intro)
  fix g h assume B0:"g \<in> X" and B1:"h \<in> H"
  have "g \<cdot> h \<cdot> inv g \<in> r_coset (l_coset g H) (inv g)"
    using l_coset_memI[OF B1, of g] by (rule r_coset_memI)
  then show "g \<cdot> h \<cdot> inv g \<in> H"
    using A0[OF B0] by auto
qed

lemma (in congruence) quotient_group:
  assumes A0:"group X (\<cdot>) e"
  shows "group quot (\<bullet>) (cls e)"
proof-
  interpret g:group X "(\<cdot>)" e by (rule A0)
  interpret q:monoid quot "(\<bullet>)" "cls e" by (rule quotient_monoid[OF g.monoid_axioms])
  show ?thesis
  proof(rule group.intro[OF q.monoid_axioms], rule group_axioms.intro)
    fix t assume "t \<in> quot"
    then obtain x where B0:"x \<in> X" and B1:"t = cls x"
      by (auto simp:quot_def)
    have "cls (g.inv x) \<bullet> cls x = cls e" and "cls x \<bullet> cls (g.inv x) = cls e"
      using B0 by (simp_all add:qmul_cls)
    then show "\<exists>s\<in>quot. s \<bullet> t = cls e \<and> t \<bullet> s = cls e"
      using B0 by (auto simp:B1 quot_def)
  qed
qed

lemma (in normal_subgroup) quotient_group:"group (l_cosets H) quo.qmul H"
  using quo.quotient_group[OF group_axioms] by (simp add:quo_quot quo_unit)

lemma (in group) congruence_normal:
  assumes A0:"congruence X (\<cdot>) R"
  shows "normal_subgroup X (\<cdot>) \<one> (R `` {\<one>})"
    and "R = {(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> R `` {\<one>}}"
proof-
  interpret r:congruence X "(\<cdot>)" R by (rule A0)
  have B0:"\<And>x y. (x, y) \<in> R \<Longrightarrow> x \<in> X \<and> y \<in> X"
    using r.R_carrier by auto
  have B1:"\<And>a. a \<in> R `` {\<one>} \<Longrightarrow> a \<in> X"
    using B0 by auto
  have B2:"\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> inv x \<cdot> y \<in> R `` {\<one>}"
  proof-
    fix x y assume C0:"x \<in> X" and C1:"y \<in> X"
    show "(x, y) \<in> R \<longleftrightarrow> inv x \<cdot> y \<in> R `` {\<one>}"
    proof
      assume "(x, y) \<in> R"
      then have "(inv x \<cdot> x, inv x \<cdot> y) \<in> R"
        by (rule r.l_compat[OF inv_closed[OF C0]])
      then show "inv x \<cdot> y \<in> R `` {\<one>}"
        using C0 by simp
    next
      assume "inv x \<cdot> y \<in> R `` {\<one>}"
      then have "(\<one>, inv x \<cdot> y) \<in> R"
        by simp
      then have "(x \<cdot> \<one>, x \<cdot> (inv x \<cdot> y)) \<in> R"
        by (rule r.l_compat[OF C0])
      then show "(x, y) \<in> R"
        using C0 C1 by (simp add:inv_rcancel)
    qed
  qed
  show "normal_subgroup X (\<cdot>) \<one> (R `` {\<one>})"
  proof(intro normal_subgroup.intro subgroup.intro group_axioms subgroup_axioms.intro normal_subgroup_axioms.intro)
    show "R `` {\<one>} \<subseteq> X"
      using B1 by auto
    show "\<one> \<in> R `` {\<one>}"
      by (simp add:r.R_refl)
    show "\<And>a b. \<lbrakk>a \<in> R `` {\<one>}; b \<in> R `` {\<one>}\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> R `` {\<one>}"
    proof-
      fix a b assume "a \<in> R `` {\<one>}" and "b \<in> R `` {\<one>}"
      then have "(\<one> \<cdot> \<one>, a \<cdot> b) \<in> R"
        by (intro r.R_compat) simp_all
      then show "a \<cdot> b \<in> R `` {\<one>}"
        by simp
    qed
    show "\<And>a. a \<in> R `` {\<one>} \<Longrightarrow> inv a \<in> R `` {\<one>}"
    proof-
      fix a assume C0:"a \<in> R `` {\<one>}"
      then have C1:"a \<in> X"
        by (rule B1)
      have "(inv a \<cdot> \<one>, inv a \<cdot> a) \<in> R"
        using C0 C1 by (intro r.l_compat) simp_all
      then have "(inv a, \<one>) \<in> R"
        using C1 by simp
      then show "inv a \<in> R `` {\<one>}"
        using r.R_sym by simp
    qed
    show "\<And>g h. \<lbrakk>g \<in> X; h \<in> R `` {\<one>}\<rbrakk> \<Longrightarrow> g \<cdot> h \<cdot> inv g \<in> R `` {\<one>}"
    proof-
      fix g h assume C0:"g \<in> X" and C1:"h \<in> R `` {\<one>}"
      then have "(g \<cdot> \<one> \<cdot> inv g, g \<cdot> h \<cdot> inv g) \<in> R"
        by (intro r.R_compat r.l_compat r.R_refl) simp_all
      then show "g \<cdot> h \<cdot> inv g \<in> R `` {\<one>}"
        using C0 by simp
    qed
  qed
  show "R = {(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> R `` {\<one>}}"
  proof
    show "R \<subseteq> {(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> R `` {\<one>}}"
    proof
      fix p assume C0:"p \<in> R"
      then obtain x y where C1:"p = (x, y)" and C2:"x \<in> X" and C3:"y \<in> X"
        using B0 by (cases p) auto
      then show "p \<in> {(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> R `` {\<one>}}"
        using C0 B2[OF C2 C3] by simp
    qed
    show "{(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> R `` {\<one>}} \<subseteq> R"
    proof
      fix p assume "p \<in> {(x, y). x \<in> X \<and> y \<in> X \<and> inv x \<cdot> y \<in> R `` {\<one>}}"
      then obtain x y where C1:"p = (x, y)" and C2:"x \<in> X" and C3:"y \<in> X" and C4:"inv x \<cdot> y \<in> R `` {\<one>}"
        by (cases p) auto
      then show "p \<in> R"
        using B2[OF C2 C3] by simp
    qed
  qed
qed

theorem (in group) congs_normal_subgroups:
  "congs = {subgroup.l_sub_eq X (\<cdot>) \<one> N |N. normal_subgroup X (\<cdot>) \<one> N}"
proof
  show "congs \<subseteq> {subgroup.l_sub_eq X (\<cdot>) \<one> N |N. normal_subgroup X (\<cdot>) \<one> N}"
  proof
    fix R assume "R \<in> congs"
    then have B0:"congruence X (\<cdot>) R"
      by (rule congsD)
    have B1:"normal_subgroup X (\<cdot>) \<one> (R `` {\<one>})"
      by (rule congruence_normal(1)[OF B0])
    have "R = subgroup.l_sub_eq X (\<cdot>) \<one> (R `` {\<one>})"
      using congruence_normal(2)[OF B0] subgroup.l_sub_eq_def[OF normal_subgroup.axioms(1)[OF B1]] by simp
    then show "R \<in> {subgroup.l_sub_eq X (\<cdot>) \<one> N |N. normal_subgroup X (\<cdot>) \<one> N}"
      using B1 by blast
  qed
  show "{subgroup.l_sub_eq X (\<cdot>) \<one> N |N. normal_subgroup X (\<cdot>) \<one> N} \<subseteq> congs"
  proof
    fix R assume "R \<in> {subgroup.l_sub_eq X (\<cdot>) \<one> N |N. normal_subgroup X (\<cdot>) \<one> N}"
    then obtain N where B0:"normal_subgroup X (\<cdot>) \<one> N" and B1:"R = subgroup.l_sub_eq X (\<cdot>) \<one> N"
      by blast
    show "R \<in> congs"
      using normal_subgroup.l_sub_eq_congruence[OF B0] by (simp add:B1 congs_def)
  qed
qed


locale group_hom = magma_hom X mul Y mul' f + dom:group X mul e + cod:group Y mul' e'
  for X::"'a set" and mul::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e
    and Y::"'b set" and mul'::"'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<star>" 70) and e' and f
begin

lemma unit:"f e = e'"
proof(rule unit_image_cancellable[OF dom.unit_closed dom.unit_id_elem cod.unit_closed cod.unit_id_elem])
  show "cod.l_cancellable (f e)"
    by (rule cod.invertible_l_cancellable) simp_all
qed

end

sublocale group_hom \<subseteq> monoid_hom X mul e Y mul' e' f
  by unfold_locales (rule unit)

context group_hom
begin

lemma hom_inv:"x \<in> X \<Longrightarrow> f (dom.inv x) = cod.inv (f x)"
  by (simp add:inv_image)

definition Ker::"'a set"
  where "Ker = {x \<in> X. f x = e'}"

lemma Ker_iff:"x \<in> Ker \<longleftrightarrow> x \<in> X \<and> f x = e'"
  by (simp add:Ker_def)

lemma Ker_memI:"\<lbrakk>x \<in> X; f x = e'\<rbrakk> \<Longrightarrow> x \<in> Ker"
  and Ker_memD1:"x \<in> Ker \<Longrightarrow> x \<in> X"
  and Ker_memD2:"x \<in> Ker \<Longrightarrow> f x = e'"
  by (simp_all add:Ker_def)

lemma Ker_sub:"Ker \<subseteq> X"
  by (auto simp:Ker_def)

lemma Ker_unit:"e \<in> Ker"
  by (simp add:Ker_def unit)

lemma Ker_closed:"\<lbrakk>a \<in> Ker; b \<in> Ker\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> Ker"
  by (simp add:Ker_def hom)

lemma Ker_inv:"a \<in> Ker \<Longrightarrow> dom.inv a \<in> Ker"
  by (simp add:Ker_def hom_inv)

lemma Ker_conj:"\<lbrakk>g \<in> X; k \<in> Ker\<rbrakk> \<Longrightarrow> g \<cdot> k \<cdot> dom.inv g \<in> Ker"
  by (simp add:Ker_def hom hom_inv)

lemma Ker_normal:"normal_subgroup X (\<cdot>) e Ker"
  by (intro normal_subgroup.intro subgroup.intro dom.group_axioms subgroup_axioms.intro normal_subgroup_axioms.intro
            Ker_sub Ker_closed Ker_unit Ker_inv Ker_conj)

lemma K_Ker:"K = {(x, y). x \<in> X \<and> y \<in> X \<and> dom.inv x \<cdot> y \<in> Ker}"
proof-
  have "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f x = f y \<longleftrightarrow> f (dom.inv x \<cdot> y) = e'"
  proof-
    fix x y assume A0:"x \<in> X" and A1:"y \<in> X"
    have "f (dom.inv x \<cdot> y) = cod.inv (f x) \<star> f y"
      using A0 A1 by (simp add:hom hom_inv)
    then have "f (dom.inv x \<cdot> y) = e' \<longleftrightarrow> f y = f x"
      using A0 A1 cod.inv_lsolve2[of e' "f x" "f y"] by simp
    then show "f x = f y \<longleftrightarrow> f (dom.inv x \<cdot> y) = e'"
      by auto
  qed
  then show ?thesis
    by (auto simp:K_def Ker_def)
qed

lemma inj_iff_Ker:"inj_on f X \<longleftrightarrow> Ker = {e}"
proof
  assume A0:"inj_on f X"
  show "Ker = {e}"
    using inj_onD[OF A0] unit by (auto simp:Ker_def)
next
  assume A0:"Ker = {e}"
  show "inj_on f X"
  proof(rule inj_onI)
    fix x y assume B0:"x \<in> X" and B1:"y \<in> X" and B2:"f x = f y"
    have "(x, y) \<in> K"
      using B0 B1 B2 by (simp add:K_def)
    then have "dom.inv x \<cdot> y \<in> Ker"
      unfolding K_Ker by simp
    then have "dom.inv x \<cdot> y = e"
      by (simp add:A0)
    then show "x = y"
      using B0 B1 by (simp add:dom.inv_lsolve2)
  qed
qed

lemma image_subgroup:
  assumes A0:"subgroup X (\<cdot>) e A"
  shows "subgroup Y (\<star>) e' (f ` A)"
proof-
  interpret a:subgroup X "(\<cdot>)" e A by (rule A0)
  show ?thesis
  proof(intro subgroup.intro cod.group_axioms subgroup_axioms.intro)
    show "f ` A \<subseteq> Y"
      using a.subset by auto
    show "e' \<in> f ` A"
      using a.id_mem unit by (metis imageI)
    show "\<And>a b. \<lbrakk>a \<in> f ` A; b \<in> f ` A\<rbrakk> \<Longrightarrow> a \<star> b \<in> f ` A"
    proof-
      fix a b assume "a \<in> f ` A" and "b \<in> f ` A"
      then obtain x y where B0:"x \<in> A" and B1:"y \<in> A" and B2:"a = f x" and B3:"b = f y"
        by blast
      have "a \<star> b = f (x \<cdot> y)"
        using a.subset B0 B1 by (simp add:B2 B3 hom subset_iff)
      then show "a \<star> b \<in> f ` A"
        using a.sub_closed[OF B0 B1] by simp
    qed
    show "\<And>a. a \<in> f ` A \<Longrightarrow> cod.inv a \<in> f ` A"
    proof-
      fix a assume "a \<in> f ` A"
      then obtain x where B0:"x \<in> A" and B1:"a = f x"
        by blast
      have "cod.inv a = f (dom.inv x)"
        using a.subset B0 by (simp add:B1 hom_inv subset_iff)
      then show "cod.inv a \<in> f ` A"
        using a.inv_cl[OF B0] by simp
    qed
  qed
qed

lemma vimage_subgroup:
  assumes A0:"subgroup Y (\<star>) e' B"
  shows "subgroup X (\<cdot>) e (X \<inter> f -` B)"
proof-
  interpret b:subgroup Y "(\<star>)" e' B by (rule A0)
  show ?thesis
    by (intro subgroup.intro dom.group_axioms subgroup_axioms.intro) (auto simp:hom hom_inv unit b.sub_closed b.inv_cl)
qed

lemma vimage_normal:
  assumes A0:"normal_subgroup Y (\<star>) e' B"
  shows "normal_subgroup X (\<cdot>) e (X \<inter> f -` B)"
proof-
  interpret b:normal_subgroup Y "(\<star>)" e' B by (rule A0)
  show ?thesis
    by (intro normal_subgroup.intro vimage_subgroup[OF b.subgroup_axioms] normal_subgroup_axioms.intro)
       (auto simp:hom hom_inv b.normal)
qed

lemma im_subgroup:"subgroup Y (\<star>) e' (f ` X)"
  by (rule image_subgroup[OF dom.top_subgroup])

lemma im_group:"group (f ` X) (\<star>) e'"
  by (rule subgroup.sub_group[OF im_subgroup])

end

locale group_iso = group_hom +
  assumes bij:"bij_betw f X Y"

sublocale group_iso \<subseteq> monoid_iso X mul e Y mul' e' f
  by unfold_locales (rule bij)

lemma group_hom_compose:
  assumes A0:"group_hom X mul e Y mul' e' f" and A1:"group_hom Y mul' e' Z mul'' e'' g"
  shows "group_hom X mul e Z mul'' e'' (g \<circ> f)"
proof-
  interpret f:group_hom X mul e Y mul' e' f by (rule A0)
  interpret g:group_hom Y mul' e' Z mul'' e'' g by (rule A1)
  show ?thesis
    by (intro group_hom.intro magma_hom_compose[OF f.magma_hom_axioms g.magma_hom_axioms] f.dom.group_axioms g.cod.group_axioms)
qed

context group_hom
begin

context
begin

interpretation ker:normal_subgroup X "(\<cdot>)" e Ker
  by (rule Ker_normal)

theorem first_iso_group:
  obtains h where "group_iso ker.quo.quot ker.quo.qmul (ker.quo.cls e) (f ` X) (\<star>) e' h"
    and "\<And>x. x \<in> X \<Longrightarrow> h (ker.quo.cls x) = f x"
proof-
  have B0:"K = ker.l_sub_eq"
    by (simp add:K_Ker ker.l_sub_eq_def)
  obtain h where B1:"magma_iso (congruence.quot X K) (congruence.qmul (\<cdot>) K) (f ` X) (\<star>) h"
    and B2:"\<And>x. x \<in> X \<Longrightarrow> h (congruence.cls K x) = f x"
    using first_iso_quotient by blast
  interpret i:magma_iso ker.quo.quot ker.quo.qmul "f ` X" "(\<star>)" h
    using B1 by (simp add:B0)
  have B3:"group_iso ker.quo.quot ker.quo.qmul (ker.quo.cls e) (f ` X) (\<star>) e' h"
  proof(intro group_iso.intro group_iso_axioms.intro group_hom.intro i.magma_hom_axioms im_group i.bij)
    show "group ker.quo.quot ker.quo.qmul (ker.quo.cls e)"
      by (rule ker.quo.quotient_group[OF dom.group_axioms])
  qed
  show thesis
    using B3 B2[unfolded B0] by (rule that)
qed

end

end

context monoid
begin

primrec pow_nat::"'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "**" 80)
  where pow_0:"x ** 0 = \<one>"
      | pow_Suc:"x ** Suc n = x \<cdot> (x ** n)"

lemma pow_closed[simp, intro]:"x \<in> X \<Longrightarrow> x ** n \<in> X"
  by (induction n) simp_all

lemma pow_unit[simp]:"\<one> ** n = \<one>"
  by (induction n) simp_all

lemma pow_1[simp]:"x \<in> X \<Longrightarrow> x ** 1 = x"
  unfolding One_nat_def by simp

lemma pow_commutes:"x \<in> X \<Longrightarrow> (x ** n) \<cdot> x = x \<cdot> (x ** n)"
  by (induction n) (simp_all add:assoc)

lemma pow_Suc2:"x \<in> X \<Longrightarrow> x ** Suc n = x ** n \<cdot> x"
  by (simp add:pow_commutes)

lemma pow_add:"x \<in> X \<Longrightarrow> x ** (m + n) = x ** m \<cdot> x ** n"
  by (induction m) (simp_all add:assoc)

lemma pow_mult:"x \<in> X \<Longrightarrow> x ** (m * n) = (x ** m) ** n"
  by (induction n) (simp_all add:pow_add)

lemma commute_pow1:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"x \<cdot> y = y \<cdot> x"
  shows "x ** n \<cdot> y = y \<cdot> x ** n"
proof(induction n)
  case 0
  then show ?case
    using A1 by simp
next
  case (Suc n)
  have "x ** Suc n \<cdot> y = x \<cdot> (x ** n \<cdot> y)"
    using A0 A1 by (simp add:assoc)
  also have "\<dots> = (x \<cdot> y) \<cdot> x ** n"
    using A0 A1 Suc.IH by (simp add:assoc)
  also have "\<dots> = y \<cdot> x ** Suc n"
    using A0 A1 by (simp add:A2 assoc)
  finally show ?case .
qed

lemma commute_pow2:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"x \<cdot> y = y \<cdot> x"
  shows "x ** n \<cdot> y ** m = y ** m \<cdot> x ** n"
  using commute_pow1[OF A0 pow_closed[OF A1] commute_pow1[OF A1 A0 A2[symmetric], symmetric]] by simp

lemma commute_pow3:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"x \<cdot> y = y \<cdot> x"
  shows "(x \<cdot> y) ** n = x ** n \<cdot> y ** n"
proof(induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "(x \<cdot> y) ** Suc n = x \<cdot> (y \<cdot> (x ** n \<cdot> y ** n))"
    using A0 A1 by (simp add:Suc.IH assoc)
  also have "\<dots> = x \<cdot> ((x ** n \<cdot> y) \<cdot> y ** n)"
    using A0 A1 commute_pow1[OF A0 A1 A2, of n] by (simp add:assoc)
  also have "\<dots> = x ** Suc n \<cdot> y ** Suc n"
    using A0 A1 by (simp add:assoc)
  finally show ?case .
qed

lemma pow_invertible[simp, intro]:"\<lbrakk>x \<in> X; invertible x\<rbrakk> \<Longrightarrow> invertible (x ** n)"
  by (induction n) (simp_all add:e_unit prod_invertible)

lemma inv_pow:
  assumes A0:"x \<in> X" and A1:"invertible x"
  shows "inv (x ** n) = inv x ** n"
proof(induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "inv (x ** Suc n) = inv (x ** n) \<cdot> inv x"
    using A0 A1 by (simp add:prod_inv)
  also have "\<dots> = inv x ** n \<cdot> inv x"
    by (simp add:Suc.IH)
  also have "\<dots> = inv x ** Suc n"
    using A0 A1 by (simp add:pow_commutes)
  finally show ?case .
qed

definition elem_exponents::"'a \<Rightarrow> nat set"
  where "elem_exponents x = {n. 0 < n \<and> x ** n = \<one>}"

definition elem_ord::"'a \<Rightarrow> nat"
  where "elem_ord x = (if elem_exponents x \<noteq> {} then (LEAST n. n \<in> elem_exponents x) else 0)"

lemma elem_exponents_iff:"n \<in> elem_exponents x \<longleftrightarrow> 0 < n \<and> x ** n = \<one>"
  by (simp add:elem_exponents_def)

lemma elem_ord_mem:"elem_exponents x \<noteq> {} \<Longrightarrow> elem_ord x \<in> elem_exponents x"
  unfolding elem_ord_def by (simp add:LeastI_ex[of "\<lambda>n. n \<in> elem_exponents x"] ex_in_conv)

lemma elem_ord_exp:"x ** elem_ord x = \<one>"
proof(cases "elem_exponents x = {}")
  case True
  then show ?thesis
    by (simp add:elem_ord_def)
next
  case False
  then show ?thesis
    using elem_ord_mem[OF False] by (simp add:elem_exponents_iff)
qed

lemma elem_ord_ne_iff:"elem_ord x \<noteq> 0 \<longleftrightarrow> elem_exponents x \<noteq> {}"
proof
  assume "elem_ord x \<noteq> 0"
  then show "elem_exponents x \<noteq> {}"
    by (auto simp:elem_ord_def)
next
  assume "elem_exponents x \<noteq> {}"
  then show "elem_ord x \<noteq> 0"
    using elem_ord_mem by (simp add:elem_exponents_iff)
qed

lemma elem_ord_least:
  assumes A0:"0 < n" and A1:"x ** n = \<one>"
  shows "elem_ord x \<le> n"
proof-
  have B0:"n \<in> elem_exponents x"
    by (simp add:elem_exponents_iff A0 A1)
  then have "elem_exponents x \<noteq> {}"
    by blast
  then show ?thesis
    unfolding elem_ord_def using Least_le[of "\<lambda>n. n \<in> elem_exponents x" n, OF B0] by simp
qed

lemma elem_ord_ne:
  assumes A0:"0 < n" and A1:"x ** n = \<one>"
  shows "elem_ord x \<noteq> 0"
proof-
  have "n \<in> elem_exponents x"
    by (simp add:elem_exponents_iff A0 A1)
  then have "elem_exponents x \<noteq> {}"
    by blast
  then show ?thesis
    using elem_ord_ne_iff by blast
qed

lemma elem_ord_pos:"elem_ord x \<noteq> 0 \<Longrightarrow> 0 < elem_ord x"
  by simp

lemma pow_mod:
  assumes A0:"x \<in> X" and A1:"elem_ord x \<noteq> 0"
  shows "x ** n = x ** (n mod elem_ord x)"
proof-
  have "x ** n = x ** (elem_ord x * (n div elem_ord x) + n mod elem_ord x)"
    by (metis mult_div_mod_eq)
  also have "\<dots> = (x ** elem_ord x) ** (n div elem_ord x) \<cdot> x ** (n mod elem_ord x)"
    using A0 by (simp only:pow_add pow_mult)
  also have "\<dots> = x ** (n mod elem_ord x)"
    using A0 by (simp add:elem_ord_exp)
  finally show ?thesis .
qed

lemma elem_exp_iff:
  assumes A0:"x \<in> X" and A1:"elem_ord x \<noteq> 0"
  shows "x ** n = \<one> \<longleftrightarrow> elem_ord x dvd n"
proof
  assume B0:"x ** n = \<one>"
  have B1:"x ** (n mod elem_ord x) = \<one>"
    using B0 pow_mod[OF A0 A1] by simp
  have "n mod elem_ord x = 0"
  proof(rule ccontr)
    assume "n mod elem_ord x \<noteq> 0"
    then have "elem_ord x \<le> n mod elem_ord x"
      using elem_ord_least[OF _ B1] by simp
    moreover have "n mod elem_ord x < elem_ord x"
      using A1 by simp
    ultimately show False
      by linarith
  qed
  then show "elem_ord x dvd n"
    by (simp add:dvd_eq_mod_eq_0)
next
  assume "elem_ord x dvd n"
  then obtain k where "n = elem_ord x * k"
    by (rule dvdE)
  then show "x ** n = \<one>"
    using A0 by (simp add:pow_mult elem_ord_exp)
qed

lemma order_divides_exponent:"\<lbrakk>x \<in> X; elem_ord x \<noteq> 0; m \<in> elem_exponents x\<rbrakk> \<Longrightarrow> elem_ord x dvd m"
  by (simp add:elem_exp_iff elem_exponents_iff)

lemma elem_ord_unit:"elem_ord \<one> = 1"
proof-
  have B0:"elem_exponents \<one> = {n. 0 < n}"
    by (simp add:elem_exponents_def)
  have B1:"(LEAST n::nat. 0 < n) = 1"
    by (rule Least_equality) simp_all
  have B2:"{n::nat. 0 < n} \<noteq> {}"
    by blast
  show ?thesis
    unfolding elem_ord_def B0 using B1 B2 by simp
qed

lemma elem_ord_dvd_iff_sub:
  assumes A0:"x \<in> X" and A1:"elem_ord x \<noteq> 0"
  shows "elem_exponents x = {n. 0 < n \<and> elem_ord x dvd n}"
  by (auto simp:elem_exponents_def elem_exp_iff[OF A0 A1])

lemma elem_ord_pow:
  assumes A0:"a \<in> X" and A1:"elem_ord a \<noteq> 0" and A2:"0 < k"
  shows "elem_ord (a ** k) = elem_ord a div gcd (elem_ord a) k"
proof-
  define od where "od = elem_ord a"
  define g where "g = gcd od k"
  have B0:"0 < od"
    using A1 by (simp add:od_def)
  have B1:"0 < g"
    using B0 by (simp add:g_def)
  have B2:"coprime (od div g) (k div g)"
    using B0 unfolding g_def by (intro div_gcd_coprime) simp
  have B3:"od = (od div g) * g" and B4:"k = (k div g) * g"
    unfolding g_def by simp_all
  have B5:"0 < od div g"
    using B0 B1 B3 by (metis mult_0 neq0_conv)
  have B6:"\<And>n. (a ** k) ** n = \<one> \<longleftrightarrow> (od div g) dvd n"
  proof-
    fix n
    have "(a ** k) ** n = \<one> \<longleftrightarrow> a ** (k * n) = \<one>"
      using A0 by (simp add:pow_mult)
    also have "\<dots> \<longleftrightarrow> od dvd k * n"
      using elem_exp_iff[OF A0 A1] by (simp add:od_def)
    also have "\<dots> \<longleftrightarrow> (od div g) * g dvd (k div g) * g * n"
      using B3 B4 by metis
    also have "\<dots> \<longleftrightarrow> (od div g) dvd (k div g) * n"
      using B1 by (simp add:mult.commute mult.left_commute)
    also have "\<dots> \<longleftrightarrow> (od div g) dvd n"
      using B2 by (simp add:coprime_dvd_mult_left_iff mult.commute)
    finally show "(a ** k) ** n = \<one> \<longleftrightarrow> (od div g) dvd n" .
  qed
  have B7:"elem_exponents (a ** k) = {n. 0 < n \<and> (od div g) dvd n}"
    by (auto simp:elem_exponents_def B6)
  have B8:"elem_exponents (a ** k) \<noteq> {}"
    using B5 B7 by auto
  have B9:"(LEAST n. n \<in> elem_exponents (a ** k)) = od div g"
    unfolding B7
  proof(rule Least_equality)
    show "od div g \<in> {n. 0 < n \<and> od div g dvd n}"
      using B5 by simp
    show "\<And>y. y \<in> {n. 0 < n \<and> od div g dvd n} \<Longrightarrow> od div g \<le> y"
      by (simp add:dvd_imp_le)
  qed
  show ?thesis
    using B8 B9 by (simp add:elem_ord_def od_def g_def)
qed

end


context monoid_hom
begin

lemma hom_pow:"x \<in> X \<Longrightarrow> f (dom.pow_nat x n) = cod.pow_nat (f x) n"
  by (induction n) (simp_all add:unit hom)

lemma hom_elem_ord_dvd:"\<lbrakk>x \<in> X; dom.elem_ord x \<noteq> 0\<rbrakk> \<Longrightarrow> cod.elem_ord (f x) dvd dom.elem_ord x"
proof-
  assume A0:"x \<in> X" and A1:"dom.elem_ord x \<noteq> 0"
  have B0:"cod.pow_nat (f x) (dom.elem_ord x) = e'"
    using hom_pow[OF A0, of "dom.elem_ord x"] dom.elem_ord_exp[of x] unit by simp
  then have B1:"cod.elem_ord (f x) \<noteq> 0"
    using A1 by (intro cod.elem_ord_ne) simp_all
  show ?thesis
    using cod.elem_exp_iff[OF maps[OF A0] B1] B0 by simp
qed

end


context group
begin

definition pow_int::"'a \<Rightarrow> int \<Rightarrow> 'a" (infixl "[^]" 80)
  where "x [^] z = (if z < 0 then inv (x ** nat (- z)) else x ** nat z)"

lemma int_pow_int[simp]:"x [^] int n = x ** n"
  by (simp add:pow_int_def)

lemma int_pow_0[simp]:"x [^] 0 = \<one>"
  by (simp add:pow_int_def)

lemma int_pow_1[simp]:"x \<in> X \<Longrightarrow> x [^] 1 = x"
  by (simp add:pow_int_def)

lemma int_pow_closed[simp, intro]:"x \<in> X \<Longrightarrow> x [^] i \<in> X"
  by (simp add:pow_int_def)

lemma int_pow_unit[simp]:"\<one> [^] i = \<one>"
  by (simp add:pow_int_def)

lemma int_pow_nonneg:"0 \<le> i \<Longrightarrow> x [^] i = x ** nat i"
  by (simp add:pow_int_def)

lemma int_pow_neg_int:"x \<in> X \<Longrightarrow> x [^] (- int n) = inv (x ** n)"
  by (cases "n = 0") (simp_all add:pow_int_def)

lemma int_pow_neg:
  assumes A0:"x \<in> X"
  shows "x [^] (- i) = inv (x [^] i)"
proof(cases "i < 0")
  case True
  then show ?thesis
    using A0 by (simp add:pow_int_def)
next
  case False
  then show ?thesis
    using A0 int_pow_neg_int[OF A0, of "nat i"] by (simp add:int_pow_nonneg)
qed

lemma int_pow_Suc:
  assumes A0:"x \<in> X"
  shows "x [^] (i + 1) = x [^] i \<cdot> x"
proof(cases "0 \<le> i")
  case True
  then have "nat (i + 1) = Suc (nat i)"
    by (simp add:nat_add_distrib)
  then show ?thesis
    using True A0 by (simp add:int_pow_nonneg pow_commutes)
next
  case False
  then have B0:"i < 0"
    by simp
  show ?thesis
  proof(cases "i = - 1")
    case True
    then show ?thesis
      using A0 int_pow_neg_int[OF A0, of 1] by simp
  next
    case False
    then have B1:"i + 1 < 0"
      using B0 by simp
    define m where "m = nat (- (i + 1))"
    have B2:"nat (- i) = Suc m"
      using B1 unfolding m_def by (simp add:nat_add_distrib[symmetric])
    have "x [^] i \<cdot> x = inv (x \<cdot> x ** m) \<cdot> x"
      using B0 by (simp add:pow_int_def B2)
    also have "\<dots> = (inv (x ** m) \<cdot> inv x) \<cdot> x"
      using A0 by (simp add:prod_inv)
    also have "\<dots> = inv (x ** m)"
      using A0 by (simp add:assoc)
    also have "\<dots> = x [^] (i + 1)"
      using B1 by (simp add:pow_int_def m_def)
    finally show ?thesis
      by simp
  qed
qed

lemma int_pow_pred:
  assumes A0:"x \<in> X"
  shows "x [^] (i - 1) = x [^] i \<cdot> inv x"
proof-
  have "x [^] i = x [^] (i - 1) \<cdot> x"
    using int_pow_Suc[OF A0, of "i - 1"] by simp
  then show ?thesis
    using A0 by (simp add:assoc)
qed

lemma int_pow_add:
  assumes A0:"x \<in> X"
  shows "x [^] (i + j) = x [^] i \<cdot> x [^] j"
proof(induction j rule:int_induct[where k = 0])
  case base
  then show ?case
    using A0 by simp
next
  case (step1 j)
  have "x [^] (i + (j + 1)) = x [^] (i + j) \<cdot> x"
    using int_pow_Suc[OF A0, of "i + j"] by (simp add:add.assoc)
  also have "\<dots> = x [^] i \<cdot> x [^] (j + 1)"
    using A0 by (simp add:step1.IH int_pow_Suc assoc)
  finally show ?case .
next
  case (step2 j)
  have "x [^] (i + (j - 1)) = x [^] (i + j) \<cdot> inv x"
    using int_pow_pred[OF A0, of "i + j"] by (simp add:add_diff_eq)
  also have "\<dots> = x [^] i \<cdot> x [^] (j - 1)"
    using A0 by (simp add:step2.IH int_pow_pred assoc)
  finally show ?case .
qed

lemma int_pow_inv:
  assumes A0:"x \<in> X"
  shows "(inv x) [^] i = inv (x [^] i)"
proof(cases "i < 0")
  case True
  then show ?thesis
    using A0 by (simp add:pow_int_def inv_pow)
next
  case False
  then show ?thesis
    using A0 by (simp add:pow_int_def inv_pow)
qed

lemma int_pow_diff:"x \<in> X \<Longrightarrow> x [^] (i - j) = x [^] i \<cdot> inv (x [^] j)"
  using int_pow_add[of x i "- j"] int_pow_neg[of x j] by simp

lemma int_pow_mult:
  assumes A0:"x \<in> X"
  shows "(x [^] i) [^] j = x [^] (i * j)"
proof(induction j rule:int_induct[where k = 0])
  case base
  then show ?case
    by simp
next
  case (step1 j)
  have "(x [^] i) [^] (j + 1) = x [^] (i * j) \<cdot> x [^] i"
    using A0 by (simp add:int_pow_Suc step1.IH)
  also have "\<dots> = x [^] (i * (j + 1))"
    using A0 by (simp add:int_pow_add[symmetric] distrib_left)
  finally show ?case .
next
  case (step2 j)
  have "(x [^] i) [^] (j - 1) = x [^] (i * j) \<cdot> inv (x [^] i)"
    using A0 by (simp add:int_pow_pred step2.IH)
  also have "\<dots> = x [^] (i * (j - 1))"
    using A0 by (simp add:int_pow_diff[symmetric] right_diff_distrib)
  finally show ?case .
qed

lemma commute_inv:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"x \<cdot> y = y \<cdot> x"
  shows "inv y \<cdot> x = x \<cdot> inv y"
proof-
  have "inv y \<cdot> x = inv y \<cdot> (x \<cdot> y) \<cdot> inv y"
    using A0 A1 by (simp add:assoc)
  also have "\<dots> = inv y \<cdot> (y \<cdot> x) \<cdot> inv y"
    by (simp add:A2)
  also have "\<dots> = x \<cdot> inv y"
    using A0 A1 by (simp add:assoc[symmetric])
  finally show ?thesis .
qed

lemma commute_int_pow:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"x \<cdot> y = y \<cdot> x"
  shows "y [^] i \<cdot> x = x \<cdot> y [^] i"
proof(cases "i < 0")
  case True
  have "x \<cdot> y ** nat (- i) = y ** nat (- i) \<cdot> x"
    using commute_pow1[OF A1 A0 A2[symmetric]] by simp
  then show ?thesis
    using True A0 A1 commute_inv[OF A0 pow_closed[OF A1], of "nat (- i)"] by (simp add:pow_int_def)
next
  case False
  then show ?thesis
    using commute_pow1[OF A1 A0 A2[symmetric]] by (simp add:pow_int_def)
qed

lemma int_pow_mult_distrib:
  assumes A0:"x \<in> X" and A1:"y \<in> X" and A2:"x \<cdot> y = y \<cdot> x"
  shows "(x \<cdot> y) [^] i = x [^] i \<cdot> y [^] i"
proof(induction i rule:int_induct[where k = 0])
  case base
  then show ?case
    by simp
next
  case (step1 i)
  have "(x \<cdot> y) [^] (i + 1) = (x [^] i \<cdot> y [^] i) \<cdot> (x \<cdot> y)"
    using A0 A1 by (simp add:int_pow_Suc step1.IH)
  also have "\<dots> = x [^] i \<cdot> (y [^] i \<cdot> x) \<cdot> y"
    using A0 A1 by (simp add:assoc)
  also have "\<dots> = (x [^] i \<cdot> x) \<cdot> (y [^] i \<cdot> y)"
    using A0 A1 by (simp add:commute_int_pow[OF A0 A1 A2] assoc)
  also have "\<dots> = x [^] (i + 1) \<cdot> y [^] (i + 1)"
    using A0 A1 by (simp add:int_pow_Suc)
  finally show ?case .
next
  case (step2 i)
  have B0:"inv y \<cdot> inv x = inv x \<cdot> inv y"
    using A0 A1 by (simp add:prod_inv[symmetric] A2)
  have B1:"x [^] i \<cdot> inv y = inv y \<cdot> x [^] i"
    using commute_int_pow[OF A1 A0 A2[symmetric], of i] commute_inv[OF int_pow_closed[OF A0] A1] by simp
  have "(x \<cdot> y) [^] (i - 1) = (x [^] i \<cdot> y [^] i) \<cdot> (inv y \<cdot> inv x)"
    using A0 A1 by (simp add:int_pow_pred step2.IH prod_inv)
  also have "\<dots> = (x [^] i \<cdot> y [^] i) \<cdot> (inv x \<cdot> inv y)"
    by (simp add:B0)
  also have "\<dots> = x [^] i \<cdot> (y [^] i \<cdot> inv x) \<cdot> inv y"
    using A0 A1 by (simp add:assoc)
  also have "\<dots> = x [^] i \<cdot> (inv x \<cdot> y [^] i) \<cdot> inv y"
    using commute_int_pow[OF A0 A1 A2, of i] commute_inv[OF int_pow_closed[OF A1] A0] by simp
  also have "\<dots> = (x [^] i \<cdot> inv x) \<cdot> (y [^] i \<cdot> inv y)"
    using A0 A1 by (simp add:assoc)
  also have "\<dots> = x [^] (i - 1) \<cdot> y [^] (i - 1)"
    using A0 A1 by (simp add:int_pow_pred)
  finally show ?case .
qed

lemma pow_eq_div2:
  assumes A0:"x \<in> X" and A1:"x ** m = x ** n"
  shows "x ** (m - n) = \<one>"
proof(cases "n \<le> m")
  case True
  have "x ** m = x ** (m - n) \<cdot> x ** n"
    using True A0 pow_add[OF A0, of "m - n" n] by simp
  then have "x ** (m - n) \<cdot> x ** n = \<one> \<cdot> x ** n"
    using A0 A1 by simp
  then show ?thesis
    using A0 by (simp only:r_cancel_iff pow_closed unit_closed)
next
  case False
  then show ?thesis
    by simp
qed

lemma elem_ord_inv:
  assumes A0:"x \<in> X"
  shows "elem_ord (inv x) = elem_ord x"
proof-
  have "elem_exponents (inv x) = elem_exponents x"
    using A0 by (auto simp:elem_exponents_def inv_pow[symmetric])
  then show ?thesis
    by (simp add:elem_ord_def)
qed

lemma int_pow_elem_ord:"\<lbrakk>x \<in> X; elem_ord x \<noteq> 0\<rbrakk> \<Longrightarrow> x [^] i = x ** nat (i mod int (elem_ord x))"
proof-
  assume A0:"x \<in> X" and A1:"elem_ord x \<noteq> 0"
  have B0:"i = int (elem_ord x) * (i div int (elem_ord x)) + i mod int (elem_ord x)"
    by simp
  have B1:"x [^] (int (elem_ord x) * (i div int (elem_ord x))) = \<one>"
    using A0 by (simp add:int_pow_mult[symmetric] elem_ord_exp)
  have B2:"0 \<le> i mod int (elem_ord x)"
    using A1 by simp
  show ?thesis
    using A0 B1 B2 int_pow_add[OF A0, of "int (elem_ord x) * (i div int (elem_ord x))" "i mod int (elem_ord x)"]
    by (simp add:int_pow_nonneg B0[symmetric])
qed

end


context group_hom
begin

lemma hom_int_pow:
  assumes A0:"x \<in> X"
  shows "f (dom.pow_int x i) = cod.pow_int (f x) i"
proof(cases "i < 0")
  case True
  then show ?thesis
    using A0 by (simp add:dom.pow_int_def cod.pow_int_def hom_inv hom_pow)
next
  case False
  then show ?thesis
    using A0 by (simp add:dom.pow_int_def cod.pow_int_def hom_pow)
qed

end

context group
begin

lemma subgroup_pow_closed:
  assumes A0:"subgroup X (\<cdot>) \<one> H" and A1:"h \<in> H"
  shows "h ** n \<in> H"
  by (induction n) (simp_all add:A1 subgroup.id_mem[OF A0] subgroup.sub_closed[OF A0])

lemma subgroup_int_pow_closed:
  assumes A0:"subgroup X (\<cdot>) \<one> H" and A1:"h \<in> H"
  shows "h [^] k \<in> H"
  by (simp add:pow_int_def subgroup_pow_closed[OF A0 A1] subgroup.inv_cl[OF A0])

inductive_set gen_group::"'a set \<Rightarrow> 'a set" for A::"'a set"
  where gen_unit:"\<one> \<in> gen_group A"
      | gen_base:"a \<in> A \<Longrightarrow> a \<in> gen_group A"
      | gen_inv:"a \<in> gen_group A \<Longrightarrow> inv a \<in> gen_group A"
      | gen_step:"\<lbrakk>a \<in> gen_group A; b \<in> gen_group A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> gen_group A"

lemma gen_group_sub:
  assumes A0:"A \<subseteq> X"
  shows "gen_group A \<subseteq> X"
proof
  fix a assume "a \<in> gen_group A"
  then show "a \<in> X"
    using A0 by induction auto
qed

lemma gen_group_subgroup:"A \<subseteq> X \<Longrightarrow> subgroup X (\<cdot>) \<one> (gen_group A)"
  by (intro subgroup.intro group_axioms subgroup_axioms.intro gen_group_sub gen_group.gen_unit gen_group.gen_inv gen_group.gen_step)

lemma gen_group_eq_cl:
  assumes A0:"A \<subseteq> X"
  shows "gen_group A = subgrp.cl A"
proof
  have B0:"subgrp.cl A \<in> subgroups"
    using A0 by simp
  interpret c:subgroup X "(\<cdot>)" \<one> "subgrp.cl A"
    using B0 by (simp add:subgroup_iff)
  show "gen_group A \<subseteq> subgrp.cl A"
  proof
    fix a assume "a \<in> gen_group A"
    then show "a \<in> subgrp.cl A"
    proof induction
      case gen_unit
      then show ?case
        by (rule c.id_mem)
    next
      case (gen_base a)
      then show ?case
        using subgrp.cl_extensive[of A] by blast
    next
      case (gen_inv a)
      then show ?case
        using c.inv_cl by blast
    next
      case (gen_step a b)
      then show ?case
        using c.sub_closed by blast
    qed
  qed
  show "subgrp.cl A \<subseteq> gen_group A"
    using gen_group_subgroup[OF A0] by (intro subgrp.cl_least) (auto simp:subgroup_iff intro:gen_group.gen_base)
qed

lemma subgrp_cl_subgroup:"A \<subseteq> X \<Longrightarrow> subgroup X (\<cdot>) \<one> (subgrp.cl A)"
  by (simp add:subgroup_iff)

lemma subgrp_cl_sub:"A \<subseteq> X \<Longrightarrow> subgrp.cl A \<subseteq> X"
  using subgrp.cl_closed subgrp.base by blast

lemma cl_singleton_pow:
  assumes A0:"a \<in> X"
  shows "subgrp.cl {a} = {a [^] k |k. True}"
proof
  have B0:"subgroup X (\<cdot>) \<one> {a [^] k |k. True}"
  proof(rule subgroupI1)
    show "{a [^] k |k. True} \<subseteq> X"
      using A0 by auto
    show "{a [^] k |k. True} \<noteq> {}"
      by blast
    show "\<And>x y. \<lbrakk>x \<in> {a [^] k |k. True}; y \<in> {a [^] k |k. True}\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> {a [^] k |k. True}"
    proof-
      fix x y assume "x \<in> {a [^] k |k. True}" and "y \<in> {a [^] k |k. True}"
      then obtain i j where "x = a [^] i" and "y = a [^] j"
        by blast
      then have "x \<cdot> y = a [^] (i + j)"
        by (simp add:int_pow_add[OF A0])
      then show "x \<cdot> y \<in> {a [^] k |k. True}"
        by blast
    qed
    show "\<And>x. x \<in> {a [^] k |k. True} \<Longrightarrow> inv x \<in> {a [^] k |k. True}"
    proof-
      fix x assume "x \<in> {a [^] k |k. True}"
      then obtain i where "x = a [^] i"
        by blast
      then have "inv x = a [^] (- i)"
        by (simp add:int_pow_neg[OF A0])
      then show "inv x \<in> {a [^] k |k. True}"
        by blast
    qed
  qed
  have B1:"a \<in> {a [^] k |k. True}"
    using int_pow_1[OF A0] by (intro CollectI exI[where x = 1]) simp
  show "subgrp.cl {a} \<subseteq> {a [^] k |k. True}"
    using B0 B1 by (intro subgrp.cl_least) (simp_all add:subgroup_iff)
  show "{a [^] k |k. True} \<subseteq> subgrp.cl {a}"
  proof
    fix x assume "x \<in> {a [^] k |k. True}"
    then obtain k where B2:"x = a [^] k"
      by blast
    have "a \<in> subgrp.cl {a}"
      using subgrp.cl_extensive[of "{a}"] by blast
    then show "x \<in> subgrp.cl {a}"
      using subgroup_int_pow_closed[OF subgrp_cl_subgroup] A0 by (simp add:B2)
  qed
qed

lemma cl_singleton_inv:
  assumes A0:"x \<in> X"
  shows "subgrp.cl {x} = subgrp.cl {inv x}"
proof-
  have "{x [^] k |k. True} = {inv x [^] k |k. True}"
  proof
    show "{x [^] k |k. True} \<subseteq> {inv x [^] k |k. True}"
    proof
      fix y assume "y \<in> {x [^] k |k. True}"
      then obtain k where "y = x [^] k"
        by blast
      then have "y = inv x [^] (- k)"
        using A0 by (simp add:int_pow_inv int_pow_neg)
      then show "y \<in> {inv x [^] k |k. True}"
        by blast
    qed
    show "{inv x [^] k |k. True} \<subseteq> {x [^] k |k. True}"
    proof
      fix y assume "y \<in> {inv x [^] k |k. True}"
      then obtain k where "y = inv x [^] k"
        by blast
      then have "y = x [^] (- k)"
        using A0 by (simp add:int_pow_inv int_pow_neg)
      then show "y \<in> {x [^] k |k. True}"
        by blast
    qed
  qed
  then show ?thesis
    using A0 by (simp add:cl_singleton_pow)
qed

lemma cl_unit:"subgrp.cl {\<one>} = {\<one>}"
  using subgrp.cl_fixed[of "{\<one>}"] trivial_subgroup by (simp add:subgroup_iff)

lemma cl_empty:"subgrp.cl {} = {\<one>}"
proof
  show "subgrp.cl {} \<subseteq> {\<one>}"
    using trivial_subgroup by (intro subgrp.cl_least) (simp_all add:subgroup_iff)
  show "{\<one>} \<subseteq> subgrp.cl {}"
    using subgroup.id_mem[OF subgrp_cl_subgroup[of "{}"]] by simp
qed

definition cyclic_group::"'a set \<Rightarrow> bool"
  where "cyclic_group G \<longleftrightarrow> (\<exists>x\<in>X. subgrp.cl {x} = G)"

lemma cyclic_group_eq:"cyclic_group G \<longleftrightarrow> (\<exists>g\<in>X. G = {g [^] k |k. True})"
  by (auto simp:cyclic_group_def cl_singleton_pow)

lemma cyclic_group_subgroup:"cyclic_group G \<Longrightarrow> subgroup X (\<cdot>) \<one> G"
  by (auto simp:cyclic_group_def subgrp_cl_subgroup)

lemma cyclic_group_commutative:
  assumes A0:"cyclic_group G"
  shows "commutative_group G (\<cdot>) \<one>"
proof-
  obtain g where B0:"g \<in> X" and B1:"G = {g [^] k |k. True}"
    using A0 by (auto simp:cyclic_group_eq)
  interpret s:subgroup X "(\<cdot>)" \<one> G
    by (rule cyclic_group_subgroup[OF A0])
  have B2:"\<And>x y. \<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  proof-
    fix x y assume "x \<in> G" and "y \<in> G"
    then obtain i j where "x = g [^] i" and "y = g [^] j"
      using B1 by blast
    then show "x \<cdot> y = y \<cdot> x"
      using B0 by (simp add:int_pow_add[symmetric] add.commute)
  qed
  show ?thesis
    by (intro commutative_group.intro s.sub.group_axioms commutative_monoid.intro s.sub.monoid_axioms
              commutative_semigroup.intro s.sub.semigroup_axioms commutative_magma.intro s.sub.magma_axioms
              commutative_magma_axioms.intro B2)
qed

theorem cyclic_subgroup:
  assumes A0:"cyclic_group G" and A1:"subgroup G (\<cdot>) \<one> H"
  shows "cyclic_group H"
proof-
  obtain g where B0:"g \<in> X" and B1:"G = subgrp.cl {g}"
    using A0 by (auto simp:cyclic_group_def)
  have B2:"subgroup X (\<cdot>) \<one> G"
    by (rule cyclic_group_subgroup[OF A0])
  have B3:"subgroup X (\<cdot>) \<one> H"
    by (rule subgroup_trans[OF B2 A1])
  interpret h:subgroup X "(\<cdot>)" \<one> H by (rule B3)
  have B4:"H \<subseteq> G"
    using A1 by (simp add:subgroup_def subgroup_axioms_def)
  have B5:"\<And>x. x \<in> H \<Longrightarrow> \<exists>k. x = g [^] k"
    using B4 cl_singleton_pow[OF B0] B1 by blast
  show ?thesis
  proof(cases "H = {\<one>}")
    case True
    then show ?thesis
      using cl_unit by (auto simp:cyclic_group_def)
  next
    case False
    define M where "M = {n::nat. 0 < n \<and> g [^] int n \<in> H}"
    have B6:"M \<noteq> {}"
    proof-
      obtain x where C0:"x \<in> H" and C1:"x \<noteq> \<one>"
        using False h.id_mem by blast
      obtain k where C2:"x = g [^] k"
        using B5[OF C0] by blast
      have C3:"k \<noteq> 0"
        using C1 C2 by auto
      show ?thesis
      proof(cases "0 < k")
        case True
        then have "nat k \<in> M"
          using C0 C2 by (simp add:M_def int_pow_nonneg)
        then show ?thesis
          by blast
      next
        case False
        then have "0 < - k"
          using C3 by simp
        moreover have "g [^] (- k) \<in> H"
          using C0 C2 h.inv_cl[OF C0] int_pow_neg[OF B0] by simp
        ultimately have "nat (- k) \<in> M"
          by (simp add:M_def int_pow_nonneg)
        then show ?thesis
          by blast
      qed
    qed
    define m where "m = (LEAST n. n \<in> M)"
    have B7:"m \<in> M"
      unfolding m_def by (rule LeastI_ex) (simp add:B6 ex_in_conv)
    have B8:"0 < m" and B9:"g [^] int m \<in> H"
      using B7 by (simp_all add:M_def)
    have B10:"\<And>n. n \<in> M \<Longrightarrow> m \<le> n"
      unfolding m_def by (rule Least_le)
    have B11:"g [^] int m \<in> X"
      using B0 by simp
    have "subgrp.cl {g [^] int m} = H"
    proof
      show "subgrp.cl {g [^] int m} \<subseteq> H"
        using B3 B9 by (intro subgrp.cl_least) (simp_all add:subgroup_iff)
      show "H \<subseteq> subgrp.cl {g [^] int m}"
      proof
        fix x assume C0:"x \<in> H"
        obtain k where C1:"x = g [^] k"
          using B5[OF C0] by blast
        define q where "q = k div int m"
        define r where "r = k mod int m"
        have C2:"k = int m * q + r"
          by (simp add:q_def r_def)
        have C3:"0 \<le> r" and C4:"r < int m"
          using B8 by (simp_all add:r_def)
        have C5a:"x = (g [^] int m) [^] q \<cdot> g [^] r"
          using B0 by (simp only:C1 C2 int_pow_add int_pow_mult)
        have C5:"g [^] r = inv ((g [^] int m) [^] q) \<cdot> x"
          using B0 C5a by (simp add:inv_lcancel)
        have C6:"g [^] r \<in> H"
          using C5 h.sub_closed[OF h.inv_cl[OF subgroup_int_pow_closed[OF B3 B9]] C0] by simp
        have C7:"r = 0"
        proof(rule ccontr)
          assume "r \<noteq> 0"
          then have "nat r \<in> M"
            using C3 C6 by (simp add:M_def int_pow_nonneg)
          then have "m \<le> nat r"
            by (rule B10)
          moreover have "nat r < m"
            using C3 C4 by (simp add:nat_less_iff)
          ultimately show False
            by simp
        qed
        have "x = (g [^] int m) [^] q"
          using B0 C5a by (simp add:C7)
        then show "x \<in> subgrp.cl {g [^] int m}"
          using subgroup_int_pow_closed[OF subgrp_cl_subgroup[of "{g [^] int m}"]] subgrp.cl_extensive[of "{g [^] int m}"] B11
          by auto
      qed
    qed
    then show ?thesis
      using B11 by (auto simp:cyclic_group_def)
  qed
qed

definition rconj::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "rconj g x = x \<cdot> g \<cdot> inv x"

definition conjugacy_class::"'a \<Rightarrow> 'a set"
  where "conjugacy_class g = {x \<cdot> g \<cdot> inv x |x. x \<in> X}"

lemma rconj_closed[simp, intro]:"\<lbrakk>g \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj g x \<in> X"
  by (simp add:rconj_def)

lemma rconj_unit[simp]:"x \<in> X \<Longrightarrow> rconj \<one> x = \<one>"
  and rconj_by_unit[simp]:"g \<in> X \<Longrightarrow> rconj g \<one> = g"
  by (simp_all add:rconj_def)

lemma rconj_mul:"\<lbrakk>g \<in> X; h \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj (g \<cdot> h) x = rconj g x \<cdot> rconj h x"
  by (simp add:rconj_def assoc inv_lcancel)

lemma rconj_inv:"\<lbrakk>g \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj (inv g) x = inv (rconj g x)"
  by (simp add:rconj_def prod_inv assoc)

lemma rconj_rconj:"\<lbrakk>g \<in> X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> rconj (rconj g x) y = rconj g (y \<cdot> x)"
  by (simp add:rconj_def prod_inv assoc)

lemma rconj_pow:"\<lbrakk>g \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj g x ** n = rconj (g ** n) x"
  by (induction n) (simp_all add:rconj_mul)

lemma rconj_int_pow:"\<lbrakk>g \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj g x [^] i = rconj (g [^] i) x"
  by (simp add:pow_int_def rconj_pow rconj_inv)

lemma rconj_eq_unit_iff:"\<lbrakk>g \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj g x = \<one> \<longleftrightarrow> g = \<one>"
proof-
  assume A0:"g \<in> X" and A1:"x \<in> X"
  have "rconj g x = \<one> \<longleftrightarrow> x \<cdot> g = x"
    using A0 A1 by (simp add:rconj_def inv_rsolve2)
  also have "\<dots> \<longleftrightarrow> g = \<one>"
    using A0 A1 l_cancel_iff[of x g \<one>] by simp
  finally show ?thesis .
qed

lemma inner_aut:
  assumes A0:"x \<in> X"
  shows "group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (\<lambda>g. rconj g x)"
proof(intro group_iso.intro group_iso_axioms.intro group_hom.intro magma_hom.intro magma_hom_axioms.intro
            magma_axioms group_axioms)
  show "\<And>g. g \<in> X \<Longrightarrow> rconj g x \<in> X"
    using A0 by simp
  show "\<And>g h. \<lbrakk>g \<in> X; h \<in> X\<rbrakk> \<Longrightarrow> rconj (g \<cdot> h) x = rconj g x \<cdot> rconj h x"
    using A0 by (simp add:rconj_mul)
  show "bij_betw (\<lambda>g. rconj g x) X X"
  proof(rule bij_betwI2[where g = "\<lambda>g. rconj g (inv x)"])
    show "(\<lambda>g. rconj g x) \<in> maps_to X X" and "(\<lambda>g. rconj g (inv x)) \<in> maps_to X X"
      using A0 by auto
    show "\<And>g. g \<in> X \<Longrightarrow> rconj (rconj g x) (inv x) = g"
      and "\<And>g. g \<in> X \<Longrightarrow> rconj (rconj g (inv x)) x = g"
      using A0 by (simp_all add:rconj_rconj)
  qed
qed

lemma conjugacy_class_iff:"h \<in> conjugacy_class g \<longleftrightarrow> (\<exists>x\<in>X. h = rconj g x)"
  by (auto simp:conjugacy_class_def rconj_def)

lemma conjugacy_class_sub:"g \<in> X \<Longrightarrow> conjugacy_class g \<subseteq> X"
  by (auto simp:conjugacy_class_def)

lemma conjugacy_class_refl:"g \<in> X \<Longrightarrow> g \<in> conjugacy_class g"
  using rconj_by_unit[of g] by (auto simp:conjugacy_class_iff intro:bexI[where x = \<one>])

lemma conj_class_ord:
  assumes A0:"g \<in> X" and A1:"x \<in> X"
  shows "elem_ord (rconj g x) = elem_ord g"
proof-
  have "elem_exponents (rconj g x) = elem_exponents g"
    using A0 A1 by (auto simp:elem_exponents_def rconj_pow rconj_eq_unit_iff)
  then show ?thesis
    by (simp add:elem_ord_def)
qed

lemma conjugacy_class_ord:"\<lbrakk>g \<in> X; h \<in> conjugacy_class g\<rbrakk> \<Longrightarrow> elem_ord h = elem_ord g"
  by (auto simp:conjugacy_class_iff conj_class_ord)

lemma centralizer_rconj:
  assumes A0:"A \<subseteq> X"
  shows "centralizer A = {b \<in> X. \<forall>a\<in>A. rconj a b = a}"
proof-
  have "\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> b \<cdot> a = a \<cdot> b \<longleftrightarrow> rconj a b = a"
    by (simp add:rconj_def inv_rsolve2)
  then show ?thesis
    using A0 by (auto simp:centralizer_def subset_iff)
qed

definition commutator::"'a \<Rightarrow> 'a \<Rightarrow> 'a" ("C'[_,_']")
  where "C[a,b] = a \<cdot> b \<cdot> inv a \<cdot> inv b"

lemma commutator_closed[simp, intro]:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> C[a,b] \<in> X"
  by (simp add:commutator_def)

lemma commutes_iff_commutator:
  assumes A0:"a \<in> X" and A1:"b \<in> X"
  shows "a \<cdot> b = b \<cdot> a \<longleftrightarrow> C[a,b] = \<one>"
proof-
  have "C[a,b] = \<one> \<longleftrightarrow> (a \<cdot> b) \<cdot> inv (b \<cdot> a) = \<one>"
    using A0 A1 by (simp add:commutator_def prod_inv assoc)
  also have "\<dots> \<longleftrightarrow> a \<cdot> b = b \<cdot> a"
    using A0 A1 inv_rsolve2[of \<one> "a \<cdot> b" "b \<cdot> a"] by simp
  finally show ?thesis
    by simp
qed

lemma commutesI1:"\<lbrakk>a \<in> X; b \<in> X; C[a,b] = \<one>\<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"
  and commutesD1:"\<lbrakk>a \<in> X; b \<in> X; a \<cdot> b = b \<cdot> a\<rbrakk> \<Longrightarrow> C[a,b] = \<one>"
  by (simp_all add:commutes_iff_commutator)

lemma commutator_inv:"\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> C[b,a] = inv C[a,b]"
  by (simp add:commutator_def prod_inv assoc)

lemma commutator_rconj:"\<lbrakk>a \<in> X; b \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj C[a,b] x = C[rconj a x, rconj b x]"
  by (simp add:commutator_def rconj_mul rconj_inv)

definition commutators::"'a set \<Rightarrow> 'a set"
  where "commutators A = {C[a,b] |a b. a \<in> A \<and> b \<in> A}"

definition derived::"'a set \<Rightarrow> 'a set"
  where "derived A = subgrp.cl (commutators A)"

lemma commutators_sub:"A \<subseteq> X \<Longrightarrow> commutators A \<subseteq> X"
  by (auto simp:commutators_def)

lemma commutators_subgroup:
  assumes A0:"K \<subseteq> H" and A1:"subgroup X (\<cdot>) \<one> H"
  shows "commutators K \<subseteq> H"
proof-
  interpret h:subgroup X "(\<cdot>)" \<one> H by (rule A1)
  show ?thesis
    using A0 by (auto simp:commutators_def commutator_def intro!:h.sub_closed h.inv_cl)
qed

lemma derived_sub:"\<lbrakk>K \<subseteq> H; subgroup X (\<cdot>) \<one> H\<rbrakk> \<Longrightarrow> derived K \<subseteq> H"
  unfolding derived_def by (intro subgrp.cl_least) (simp_all add:subgroup_iff commutators_subgroup)

lemma derived_subgroup:"A \<subseteq> X \<Longrightarrow> subgroup X (\<cdot>) \<one> (derived A)"
  by (simp add:derived_def subgrp_cl_subgroup commutators_sub)

lemma derived_sub_X:"A \<subseteq> X \<Longrightarrow> derived A \<subseteq> X"
  by (simp add:derived_def subgrp_cl_sub commutators_sub)

lemma commutative_iff_derived:"commutative_group X (\<cdot>) \<one> \<longleftrightarrow> derived X = {\<one>}"
proof
  assume "commutative_group X (\<cdot>) \<one>"
  then interpret c:commutative_group X "(\<cdot>)" \<one> .
  have "commutators X = {\<one>}"
  proof
    show "commutators X \<subseteq> {\<one>}"
      using c.commute by (auto simp:commutators_def commutesD1)
    have "C[\<one>,\<one>] \<in> commutators X"
      by (auto simp:commutators_def)
    then show "{\<one>} \<subseteq> commutators X"
      by (simp add:commutator_def)
  qed
  then show "derived X = {\<one>}"
    by (simp add:derived_def cl_unit)
next
  assume A0:"derived X = {\<one>}"
  have B0:"\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> C[a,b] = \<one>"
  proof-
    fix a b assume "a \<in> X" and "b \<in> X"
    then have "C[a,b] \<in> commutators X"
      by (auto simp:commutators_def)
    then have "C[a,b] \<in> derived X"
      unfolding derived_def using subgrp.cl_extensive[of "commutators X"] by blast
    then show "C[a,b] = \<one>"
      by (simp add:A0)
  qed
  show "commutative_group X (\<cdot>) \<one>"
    by (intro commutative_group.intro group_axioms commutative_monoid.intro monoid_axioms
              commutative_semigroup.intro semigroup_axioms commutative_magma.intro magma_axioms
              commutative_magma_axioms.intro commutesI1 B0)
qed

end


context group_hom
begin

lemma image_subgrp_cl:
  assumes A0:"A \<subseteq> X"
  shows "f ` dom.subgrp.cl A = cod.subgrp.cl (f ` A)"
proof
  have B0:"f ` A \<subseteq> Y"
    using A0 by auto
  have "dom.subgrp.cl A \<subseteq> X \<inter> f -` cod.subgrp.cl (f ` A)"
  proof(rule dom.subgrp.cl_least)
    show "X \<inter> f -` cod.subgrp.cl (f ` A) \<in> dom.subgroups"
      using vimage_subgroup[OF cod.subgrp_cl_subgroup[OF B0]] by (simp add:dom.subgroup_iff)
    show "A \<subseteq> X \<inter> f -` cod.subgrp.cl (f ` A)"
      using A0 cod.subgrp.cl_extensive[of "f ` A"] by auto
  qed
  then show "f ` dom.subgrp.cl A \<subseteq> cod.subgrp.cl (f ` A)"
    by auto
  show "cod.subgrp.cl (f ` A) \<subseteq> f ` dom.subgrp.cl A"
  proof(rule cod.subgrp.cl_least)
    show "f ` dom.subgrp.cl A \<in> cod.subgroups"
      using image_subgroup[OF dom.subgrp_cl_subgroup[OF A0]] by (simp add:cod.subgroup_iff)
    show "f ` A \<subseteq> f ` dom.subgrp.cl A"
      using dom.subgrp.cl_extensive[of A] by auto
  qed
qed

end

context group
begin

lemma rconj_commutators:"x \<in> X \<Longrightarrow> (\<lambda>g. rconj g x) ` commutators X = commutators X"
proof-
  assume A0:"x \<in> X"
  show ?thesis
  proof
    show "(\<lambda>g. rconj g x) ` commutators X \<subseteq> commutators X"
    proof
      fix c assume "c \<in> (\<lambda>g. rconj g x) ` commutators X"
      then obtain a b where B0:"a \<in> X" and B1:"b \<in> X" and B2:"c = rconj C[a,b] x"
        by (auto simp:commutators_def)
      have "c = C[rconj a x, rconj b x]"
        using A0 B0 B1 by (simp add:B2 commutator_rconj)
      then show "c \<in> commutators X"
        unfolding commutators_def using A0 B0 B1 by blast
    qed
    show "commutators X \<subseteq> (\<lambda>g. rconj g x) ` commutators X"
    proof
      fix c assume "c \<in> commutators X"
      then obtain a b where B0:"a \<in> X" and B1:"b \<in> X" and B2:"c = C[a,b]"
        by (auto simp:commutators_def)
      have "c = rconj C[rconj a (inv x), rconj b (inv x)] x"
        using A0 B0 B1 by (simp add:B2 commutator_rconj[symmetric] rconj_rconj)
      moreover have "C[rconj a (inv x), rconj b (inv x)] \<in> commutators X"
        using A0 B0 B1 by (auto simp:commutators_def)
      ultimately show "c \<in> (\<lambda>g. rconj g x) ` commutators X"
        by blast
    qed
  qed
qed

theorem derived_normal:"normal_subgroup X (\<cdot>) \<one> (derived X)"
proof-
  interpret d:subgroup X "(\<cdot>)" \<one> "derived X"
    by (rule derived_subgroup[OF subset_refl])
  show ?thesis
  proof(rule d.normal_subgroupI1)
    fix x assume A0:"x \<in> X"
    interpret i:group_iso X "(\<cdot>)" \<one> X "(\<cdot>)" \<one> "\<lambda>g. rconj g x"
      by (rule inner_aut[OF A0])
    have "(\<lambda>g. rconj g x) ` derived X = derived X"
      using i.image_subgrp_cl[OF commutators_sub[OF subset_refl]] rconj_commutators[OF A0] by (simp add:derived_def)
    then have "(\<lambda>g. rconj g x) ` derived X = r_coset (l_coset x (derived X)) (inv x)"
      by (simp add:rconj_def l_coset_image r_coset_image image_image)
    then have "r_coset (l_coset x (derived X)) (inv x) = derived X"
      using \<open>(\<lambda>g. rconj g x) ` derived X = derived X\<close> by simp
    then have "l_coset x (derived X) = r_coset (derived X) x"
      using A0 d.subset r_coset_assoc[of "l_coset x (derived X)" "inv x" x] l_coset_sub[OF d.subset A0] by simp
    then show "l_coset x (derived X) = r_coset (derived X) x" .
  qed
qed

end

section \<open>Group Actions\<close>

subsection \<open>The symmetric group\<close>

context set_endomorphisms
begin

lemma bij_restrict_inv:
  assumes A0:"u \<in> set_mor E E" and A1:"bij_betw u E E"
  shows bij_restrict_inv_maps:"(\<lambda>y\<in>E. inv_into E u y) \<in> set_mor E E"
    and bij_restrict_inv_right:"compose E u (\<lambda>y\<in>E. inv_into E u y) = Id E"
    and bij_restrict_inv_left:"compose E (\<lambda>y\<in>E. inv_into E u y) u = Id E"
proof-
  have B0:"\<And>y. y \<in> E \<Longrightarrow> inv_into E u y \<in> E"
  proof-
    fix y assume "y \<in> E"
    then have "y \<in> u ` E"
      using bij_betw_imp_surj_on[OF A1] by simp
    then show "inv_into E u y \<in> E"
      by (rule inv_into_into)
  qed
  show "(\<lambda>y\<in>E. inv_into E u y) \<in> set_mor E E"
    using B0 by auto
  show "compose E u (\<lambda>y\<in>E. inv_into E u y) = Id E"
    unfolding compose_def by (rule restrict_ext) (simp add:bij_betw_inv_into_right[OF A1])
  show "compose E (\<lambda>y\<in>E. inv_into E u y) u = Id E"
    unfolding compose_def by (rule restrict_ext) (simp add:set_morphisms_memE1[OF A0] bij_betw_inv_into_left[OF A1])
qed

lemma Units_iff:"u \<in> Units \<longleftrightarrow> u \<in> set_mor E E \<and> bij_betw u E E"
proof
  assume A0:"u \<in> Units"
  then have B0:"u \<in> set_mor E E" and B1:"invertible u"
    by (simp_all add:Units_def)
  obtain v where B2:"compose E u v = Id E" and B3:"compose E v u = Id E" and B4:"v \<in> set_mor E E"
    using B1 by (rule invertibleE)
  have "bij_betw u E E"
  proof(rule bij_betwI2[where g = v])
    show "u \<in> maps_to E E" and "v \<in> maps_to E E"
      using B0 B4 by (simp_all add:set_morphisms_memE2)
    show "\<And>x. x \<in> E \<Longrightarrow> v (u x) = x"
    proof-
      fix x assume C0:"x \<in> E"
      have "v (u x) = compose E v u x"
        using C0 by (simp add:comp_eq)
      then show "v (u x) = x"
        using C0 by (simp add:B3)
    qed
    show "\<And>y. y \<in> E \<Longrightarrow> u (v y) = y"
    proof-
      fix y assume C0:"y \<in> E"
      have "u (v y) = compose E u v y"
        using C0 by (simp add:comp_eq)
      then show "u (v y) = y"
        using C0 by (simp add:B2)
    qed
  qed
  then show "u \<in> set_mor E E \<and> bij_betw u E E"
    using B0 by simp
next
  assume A0:"u \<in> set_mor E E \<and> bij_betw u E E"
  then have B0:"u \<in> set_mor E E" and B1:"bij_betw u E E"
    by simp_all
  have "invertible u"
    by (rule invertibleI[OF bij_restrict_inv_right[OF B0 B1] bij_restrict_inv_left[OF B0 B1] bij_restrict_inv_maps[OF B0 B1]])
  then show "u \<in> Units"
    using B0 by (simp add:Units_def)
qed

lemma Units_memI:"\<lbrakk>u \<in> set_mor E E; bij_betw u E E\<rbrakk> \<Longrightarrow> u \<in> Units"
  and Units_memD1:"u \<in> Units \<Longrightarrow> u \<in> set_mor E E"
  and Units_memD2:"u \<in> Units \<Longrightarrow> bij_betw u E E"
  by (simp_all add:Units_iff)

lemma symmetric_group:"group Units (compose E) (Id E)"
  by (rule Units_group)

lemma Units_inv:"u \<in> Units \<Longrightarrow> inv u = (\<lambda>y\<in>E. inv_into E u y)"
proof-
  assume A0:"u \<in> Units"
  then have B0:"u \<in> set_mor E E" and B1:"bij_betw u E E"
    by (simp_all add:Units_iff)
  show "inv u = (\<lambda>y\<in>E. inv_into E u y)"
    by (rule inv_eq[OF bij_restrict_inv_right[OF B0 B1] bij_restrict_inv_left[OF B0 B1] B0 bij_restrict_inv_maps[OF B0 B1]])
qed

end

lemma (in monoid) Units_inv_eq:
  assumes A0:"u \<in> Units"
  shows "monoid.inv Units (\<cdot>) \<one> u = inv u"
proof-
  have B0:"invertible u" and B1:"u \<in> X"
    using A0 by (simp_all add:Units_def)
  have B2:"monoid Units (\<cdot>) \<one>"
    by (rule group.axioms(1)[OF Units_group])
  show ?thesis
    by (rule monoid.inv_eq[OF B2 unit_rinv[OF B0 B1] unit_linv[OF B0 B1] A0 Units_inv_closed[OF A0]])
qed

subsection \<open>Group actions\<close>

locale group_action = group G mul e + monoid_action G mul e E \<alpha>
  for G::"'a set" and mul::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::'a ("\<one>") and E::"'b set" and \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b"
begin

lemma act_inv1:"\<lbrakk>g \<in> G; x \<in> E\<rbrakk> \<Longrightarrow> \<alpha> (inv g) (\<alpha> g x) = x"
  and act_inv2:"\<lbrakk>g \<in> G; x \<in> E\<rbrakk> \<Longrightarrow> \<alpha> g (\<alpha> (inv g) x) = x"
  by (simp_all add:act_assoc[symmetric] act_unit)

lemma act_inj:
  assumes A0:"g \<in> G" and A1:"x \<in> E" and A2:"y \<in> E" and A3:"\<alpha> g x = \<alpha> g y"
  shows "x = y"
proof-
  have "x = \<alpha> (inv g) (\<alpha> g x)"
    using A0 A1 by (simp add:act_inv1)
  also have "\<dots> = \<alpha> (inv g) (\<alpha> g y)"
    by (simp add:A3)
  also have "\<dots> = y"
    using A0 A2 by (simp add:act_inv1)
  finally show ?thesis .
qed

lemma act_eq_iff:"\<lbrakk>g \<in> G; x \<in> E; y \<in> E\<rbrakk> \<Longrightarrow> \<alpha> g x = \<alpha> g y \<longleftrightarrow> x = y"
  using act_inj by blast

lemma act_inv_iff:
  assumes A0:"g \<in> G" and A1:"x \<in> E" and A2:"y \<in> E"
  shows "\<alpha> g x = y \<longleftrightarrow> x = \<alpha> (inv g) y"
proof
  assume "\<alpha> g x = y"
  then show "x = \<alpha> (inv g) y"
    using act_inv1[OF A0 A1] by simp
next
  assume "x = \<alpha> (inv g) y"
  then show "\<alpha> g x = y"
    using act_inv2[OF A0 A2] by simp
qed

lemma act_bij:
  assumes A0:"g \<in> G"
  shows "bij_betw (\<alpha> g) E E"
proof(rule bij_betwI2[where g = "\<alpha> (inv g)"])
  show "\<alpha> g \<in> maps_to E E" and "\<alpha> (inv g) \<in> maps_to E E"
    using A0 by auto
  show "\<And>x. x \<in> E \<Longrightarrow> \<alpha> (inv g) (\<alpha> g x) = x"
    and "\<And>y. y \<in> E \<Longrightarrow> \<alpha> g (\<alpha> (inv g) y) = y"
    using A0 by (simp_all add:act_inv1 act_inv2)
qed

lemma act_image:"g \<in> G \<Longrightarrow> \<alpha> g ` E = E"
  by (rule bij_betw_imp_surj_on[OF act_bij])

context
begin

interpretation sym:set_endomorphisms E .

lemma l_law_Units:"g \<in> G \<Longrightarrow> l_law g \<in> sym.Units"
proof-
  assume A0:"g \<in> G"
  have "bij_betw (l_law g) E E"
    using act_bij[OF A0] A0 by (simp add:l_law_def bij_betw_cong[of E "\<lambda>x\<in>E. \<alpha> g x" "\<alpha> g"])
  then show "l_law g \<in> sym.Units"
    using l_law_maps[OF A0] by (simp add:sym.Units_iff)
qed

lemma l_law_group_hom:"group_hom G (\<cdot>) \<one> sym.Units (compose E) (Id E) l_law"
proof-
  have B0:"group sym.Units (compose E) (Id E)"
    by (rule sym.Units_group)
  have B1:"magma sym.Units (compose E)"
    by (rule semigroup.axioms(1)[OF monoid.axioms(1)[OF group.axioms(1)[OF B0]]])
  show ?thesis
  proof(intro group_hom.intro magma_hom.intro magma_hom_axioms.intro magma_axioms group_axioms B0 B1)
    show "\<And>g. g \<in> G \<Longrightarrow> l_law g \<in> sym.Units"
      by (rule l_law_Units)
    show "\<And>g h. \<lbrakk>g \<in> G; h \<in> G\<rbrakk> \<Longrightarrow> l_law (g \<cdot> h) = compose E (l_law g) (l_law h)"
      by (rule l_law_comp)
  qed
qed

end

subsubsection \<open>Orbits\<close>

lemma orbit_sym:
  assumes A0:"x \<in> E" and A1:"y \<in> orbit x"
  shows "x \<in> orbit y"
proof-
  obtain g where B0:"g \<in> G" and B1:"y = \<alpha> g x"
    using A1 by (auto simp:orbit_iff)
  have "x = \<alpha> (inv g) y"
    using A0 B0 by (simp add:B1 act_inv1)
  then show ?thesis
    using B0 by (auto simp:orbit_iff)
qed

lemma orbit_eq:
  assumes A0:"x \<in> E" and A1:"y \<in> orbit x"
  shows "orbit y = orbit x"
proof-
  have B0:"y \<in> E"
    using A0 A1 orbit_sub by blast
  show ?thesis
    using orbit_trans[OF A0 A1] orbit_trans[OF B0 orbit_sym[OF A0 A1]] by blast
qed

lemma orbit_eq_iff:
  assumes A0:"x \<in> E" and A1:"y \<in> E"
  shows "orbit x = orbit y \<longleftrightarrow> y \<in> orbit x"
proof
  assume "orbit x = orbit y"
  then show "y \<in> orbit x"
    using orbit_refl[OF A1] by simp
next
  assume "y \<in> orbit x"
  then show "orbit x = orbit y"
    using orbit_eq[OF A0] by simp
qed

lemma orbit_disjoint:
  assumes A0:"x \<in> E" and A1:"y \<in> E" and A2:"orbit x \<noteq> orbit y"
  shows "orbit x \<inter> orbit y = {}"
proof(rule ccontr)
  assume "orbit x \<inter> orbit y \<noteq> {}"
  then obtain z where B0:"z \<in> orbit x" and B1:"z \<in> orbit y"
    by blast
  have "orbit x = orbit z" and "orbit y = orbit z"
    using orbit_eq[OF A0 B0] orbit_eq[OF A1 B1] by simp_all
  then show False
    using A2 by simp
qed

lemma orbit_finite1:"finite G \<Longrightarrow> finite (orbit x)"
  by (simp add:orbit_def)

lemma orbit_finite2:
  assumes A0:"finite E" and A1:"x \<in> E"
  shows "finite (orbit x)"
  by (rule rev_finite_subset[OF A0 orbit_sub[OF A1]])

definition orbit_rel::"'b rel"
  where "orbit_rel = {(x, y). x \<in> E \<and> y \<in> orbit x}"

lemma orbit_rel_iff:"(x, y) \<in> orbit_rel \<longleftrightarrow> x \<in> E \<and> (\<exists>g\<in>G. y = \<alpha> g x)"
  by (auto simp:orbit_rel_def orbit_iff)

lemma orbit_rel_sub:"orbit_rel \<subseteq> E \<times> E"
  using orbit_sub by (auto simp:orbit_rel_def)

lemma orbit_rel_refl:"x \<in> E \<Longrightarrow> (x, x) \<in> orbit_rel"
  by (simp add:orbit_rel_def orbit_refl)

lemma orbit_rel_sym:"(x, y) \<in> orbit_rel \<Longrightarrow> (y, x) \<in> orbit_rel"
  using orbit_sym orbit_sub by (auto simp:orbit_rel_def)

lemma orbit_rel_trans:"\<lbrakk>(x, y) \<in> orbit_rel; (y, z) \<in> orbit_rel\<rbrakk> \<Longrightarrow> (x, z) \<in> orbit_rel"
  using orbit_trans by (auto simp:orbit_rel_def)

lemma orbit_rel_equiv:"equiv E orbit_rel"
  unfolding equiv_def refl_on_def sym_def trans_def
  using orbit_rel_sub orbit_rel_refl orbit_rel_sym orbit_rel_trans by blast

lemma orbit_rel_cls:"x \<in> E \<Longrightarrow> orbit_rel `` {x} = orbit x"
  by (auto simp:orbit_rel_def)

definition orbits::"'b set set"
  where "orbits = (\<Union>x\<in>E. {orbit x})"

lemma orbits_iff:"C \<in> orbits \<longleftrightarrow> (\<exists>x\<in>E. C = orbit x)"
  by (auto simp:orbits_def)

lemma orbits_memI:"x \<in> E \<Longrightarrow> orbit x \<in> orbits"
  by (auto simp:orbits_def)

lemma orbits_quotient:"orbits = E // orbit_rel"
  using orbit_rel_cls by (auto simp:orbits_def quotient_def)

lemma orbits_Union:"\<Union>orbits = E"
proof
  show "\<Union>orbits \<subseteq> E"
    using orbit_sub by (auto simp:orbits_def)
  show "E \<subseteq> \<Union>orbits"
    using orbit_refl by (auto simp:orbits_def)
qed

lemma orbits_ne:"C \<in> orbits \<Longrightarrow> C \<noteq> {}"
  using orbit_refl by (auto simp:orbits_def)

lemma orbits_disjoint:
  assumes A0:"C \<in> orbits" and A1:"D \<in> orbits" and A2:"C \<noteq> D"
  shows "C \<inter> D = {}"
proof-
  obtain x y where B0:"x \<in> E" and B1:"C = orbit x" and B2:"y \<in> E" and B3:"D = orbit y"
    using A0 A1 by (auto simp:orbits_def)
  show ?thesis
    using orbit_disjoint[OF B0 B2] A2 by (simp add:B1 B3)
qed

lemma orbits_pairwise:"pairwise disjnt orbits"
  using orbits_disjoint by (auto simp:pairwise_def disjnt_def)

lemma orbits_finite:"finite E \<Longrightarrow> finite orbits"
  by (simp add:orbits_def)

theorem card_orbits:
  assumes A0:"finite E"
  shows "card E = (\<Sum>C\<in>orbits. card C)"
proof-
  have "card E = card (\<Union>orbits)"
    by (simp add:orbits_Union)
  also have "\<dots> = (\<Sum>C\<in>orbits. card C)"
    by (rule card_Union_disjoint[OF orbits_pairwise]) (auto simp:orbits_def orbit_finite2[OF A0])
  finally show ?thesis .
qed

subsubsection \<open>Stabilizers and the orbit-stabilizer theorem\<close>

lemma stabilizer_iff:"g \<in> stabilizer x \<longleftrightarrow> g \<in> G \<and> \<alpha> g x = x"
  by (simp add:stabilizer_def)

lemma stabilizer_subgroup:
  assumes A0:"x \<in> E"
  shows "subgroup G (\<cdot>) \<one> (stabilizer x)"
proof(intro subgroup.intro group_axioms subgroup_axioms.intro)
  show "stabilizer x \<subseteq> G"
    by (rule stabilizer_sub)
  show "\<one> \<in> stabilizer x"
    using A0 by (simp add:stabilizer_def act_unit)
  show "\<And>a b. \<lbrakk>a \<in> stabilizer x; b \<in> stabilizer x\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> stabilizer x"
    using A0 by (simp add:stabilizer_def act_assoc)
  show "\<And>a. a \<in> stabilizer x \<Longrightarrow> inv a \<in> stabilizer x"
  proof-
    fix a assume "a \<in> stabilizer x"
    then have B0:"a \<in> G" and B1:"\<alpha> a x = x"
      by (simp_all add:stabilizer_def)
    have "\<alpha> (inv a) x = \<alpha> (inv a) (\<alpha> a x)"
      by (simp add:B1)
    also have "\<dots> = x"
      using A0 B0 by (simp add:act_inv1)
    finally show "inv a \<in> stabilizer x"
      using B0 by (simp add:stabilizer_def)
  qed
qed

lemma stabilizer_rconj:
  assumes A0:"g \<in> G" and A1:"x \<in> E"
  shows "stabilizer (\<alpha> g x) = (\<lambda>h. rconj h g) ` stabilizer x"
proof
  show "stabilizer (\<alpha> g x) \<subseteq> (\<lambda>h. rconj h g) ` stabilizer x"
  proof
    fix k assume "k \<in> stabilizer (\<alpha> g x)"
    then have B0:"k \<in> G" and B1:"\<alpha> k (\<alpha> g x) = \<alpha> g x"
      by (simp_all add:stabilizer_iff)
    have B2:"inv g \<cdot> k \<cdot> g \<in> G"
      using A0 B0 by simp
    have "\<alpha> (inv g \<cdot> k \<cdot> g) x = \<alpha> (inv g) (\<alpha> k (\<alpha> g x))"
      using A0 A1 B0 by (simp add:act_assoc)
    also have "\<dots> = x"
      using A0 A1 by (simp add:B1 act_inv1)
    finally have B3:"inv g \<cdot> k \<cdot> g \<in> stabilizer x"
      using B2 by (simp add:stabilizer_iff)
    have "k = rconj (inv g \<cdot> k \<cdot> g) g"
      using A0 B0 by (simp add:rconj_def assoc inv_rcancel)
    then show "k \<in> (\<lambda>h. rconj h g) ` stabilizer x"
      using B3 by blast
  qed
  show "(\<lambda>h. rconj h g) ` stabilizer x \<subseteq> stabilizer (\<alpha> g x)"
  proof
    fix k assume "k \<in> (\<lambda>h. rconj h g) ` stabilizer x"
    then obtain h where B0:"h \<in> stabilizer x" and B1:"k = rconj h g"
      by blast
    have B2:"h \<in> G" and B3:"\<alpha> h x = x"
      using B0 by (simp_all add:stabilizer_iff)
    have "\<alpha> k (\<alpha> g x) = \<alpha> g (\<alpha> h (\<alpha> (inv g) (\<alpha> g x)))"
      using A0 A1 B2 by (simp add:B1 rconj_def act_assoc)
    also have "\<dots> = \<alpha> g x"
      using A0 A1 by (simp add:act_inv1 B3)
    finally show "k \<in> stabilizer (\<alpha> g x)"
      using A0 B2 by (simp add:stabilizer_iff B1)
  qed
qed

definition transporter::"'b \<Rightarrow> 'b \<Rightarrow> 'a set"
  where "transporter x y = {g \<in> G. \<alpha> g x = y}"

lemma transporter_iff:"g \<in> transporter x y \<longleftrightarrow> g \<in> G \<and> \<alpha> g x = y"
  by (simp add:transporter_def)

lemma transporter_sub:"transporter x y \<subseteq> G"
  by (auto simp:transporter_def)

lemma transporter_self:"transporter x x = stabilizer x"
  by (auto simp:transporter_def stabilizer_def)

lemma transporter_ne_iff:"transporter x y \<noteq> {} \<longleftrightarrow> y \<in> orbit x"
  by (auto simp:transporter_def orbit_iff)

lemma transporter_coset:
  assumes A0:"x \<in> E" and A1:"g \<in> G"
  shows "transporter x (\<alpha> g x) = l_coset g (stabilizer x)"
proof
    show "transporter x (\<alpha> g x) \<subseteq> l_coset g (stabilizer x)"
    proof
      fix h assume "h \<in> transporter x (\<alpha> g x)"
      then have B0:"h \<in> G" and B1:"\<alpha> h x = \<alpha> g x"
        by (simp_all add:transporter_iff)
      have "\<alpha> (inv g \<cdot> h) x = x"
        using A0 A1 B0 by (simp add:act_assoc B1 act_inv1)
      then have "inv g \<cdot> h \<in> stabilizer x"
        using A1 B0 by (simp add:stabilizer_iff)
      then show "h \<in> l_coset g (stabilizer x)"
        using subgroup.lcoset_mem[OF stabilizer_subgroup[OF A0] A1 B0] by simp
    qed
    show "l_coset g (stabilizer x) \<subseteq> transporter x (\<alpha> g x)"
    proof
      fix h assume "h \<in> l_coset g (stabilizer x)"
      then obtain k where B0:"k \<in> stabilizer x" and B1:"h = g \<cdot> k"
        by (rule l_coset_memE)
      have B2:"k \<in> G" and B3:"\<alpha> k x = x"
        using B0 by (simp_all add:stabilizer_iff)
      have "\<alpha> h x = \<alpha> g x"
        using A0 A1 B2 by (simp add:B1 act_assoc B3)
      then show "h \<in> transporter x (\<alpha> g x)"
        using A1 B2 by (simp add:transporter_iff B1)
    qed
qed

theorem orbit_stabilizer:
  assumes A0:"x \<in> E"
  shows "bij_betw (transporter x) (orbit x) (l_cosets (stabilizer x))"
proof(rule bij_betw_imageI)
  show "inj_on (transporter x) (orbit x)"
  proof(rule inj_onI)
    fix y z assume B0:"y \<in> orbit x" and B1:"z \<in> orbit x" and B2:"transporter x y = transporter x z"
    obtain g where B3:"g \<in> G" and B4:"y = \<alpha> g x"
      using B0 by (auto simp:orbit_iff)
    have "g \<in> transporter x y"
      using B3 by (simp add:transporter_iff B4)
    then have "g \<in> transporter x z"
      by (simp add:B2)
    then show "y = z"
      by (simp add:transporter_iff B4)
  qed
  show "transporter x ` orbit x = l_cosets (stabilizer x)"
  proof
    show "transporter x ` orbit x \<subseteq> l_cosets (stabilizer x)"
    proof
      fix C assume "C \<in> transporter x ` orbit x"
      then obtain y where B0:"y \<in> orbit x" and B1:"C = transporter x y"
        by blast
      obtain g where B2:"g \<in> G" and B3:"y = \<alpha> g x"
        using B0 by (auto simp:orbit_iff)
      have "C = l_coset g (stabilizer x)"
        by (simp add:B1 B3 transporter_coset[OF A0 B2])
      then show "C \<in> l_cosets (stabilizer x)"
        using l_cosets_memI[OF B2] by simp
    qed
    show "l_cosets (stabilizer x) \<subseteq> transporter x ` orbit x"
    proof
      fix C assume "C \<in> l_cosets (stabilizer x)"
      then obtain g where B0:"g \<in> G" and B1:"C = l_coset g (stabilizer x)"
        by (rule l_cosets_memE)
      have "C = transporter x (\<alpha> g x)"
        by (simp add:B1 transporter_coset[OF A0 B0])
      moreover have "\<alpha> g x \<in> orbit x"
        using B0 by (auto simp:orbit_iff)
      ultimately show "C \<in> transporter x ` orbit x"
        by blast
    qed
  qed
qed

corollary orbit_stabilizer_card:
  assumes A0:"finite G" and A1:"x \<in> E"
  shows "card (orbit x) * card (stabilizer x) = card G"
proof-
  have "card (orbit x) = card (l_cosets (stabilizer x))"
    by (rule bij_betw_same_card[OF orbit_stabilizer[OF A1]])
  then show ?thesis
    using subgroup.lagrange[OF stabilizer_subgroup[OF A1] A0] by (simp add:mult.commute)
qed

corollary orbit_card_dvd:
  assumes A0:"finite G" and A1:"x \<in> E"
  shows "card (orbit x) dvd card G"
  unfolding orbit_stabilizer_card[OF A0 A1, symmetric] by (rule dvd_triv_left)

subsubsection \<open>Set stabilizers and the kernel of an action\<close>

definition set_stabilizer::"'b set \<Rightarrow> 'a set"
  where "set_stabilizer A = {g \<in> G. \<alpha> g ` A = A}"

lemma set_stabilizer_iff:"g \<in> set_stabilizer A \<longleftrightarrow> g \<in> G \<and> \<alpha> g ` A = A"
  by (simp add:set_stabilizer_def)

lemma set_stabilizer_sub:"set_stabilizer A \<subseteq> G"
  by (auto simp:set_stabilizer_def)

lemma set_stabilizer_singleton:"set_stabilizer {x} = stabilizer x"
  by (auto simp:set_stabilizer_def stabilizer_def)

lemma set_stabilizer_whole:"set_stabilizer E = G"
  using act_image by (auto simp:set_stabilizer_def)

lemma set_stabilizer_subgroup:
  assumes A0:"A \<subseteq> E"
  shows "subgroup G (\<cdot>) \<one> (set_stabilizer A)"
proof(intro subgroup.intro group_axioms subgroup_axioms.intro)
  show "set_stabilizer A \<subseteq> G"
    by (rule set_stabilizer_sub)
  show "\<one> \<in> set_stabilizer A"
  proof-
    have "\<alpha> \<one> ` A = id ` A"
      using A0 by (intro image_cong) (auto simp:act_unit)
    then show "\<one> \<in> set_stabilizer A"
      by (simp add:set_stabilizer_iff)
  qed
  show "\<And>a b. \<lbrakk>a \<in> set_stabilizer A; b \<in> set_stabilizer A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> set_stabilizer A"
  proof-
    fix a b assume "a \<in> set_stabilizer A" and "b \<in> set_stabilizer A"
    then have B0:"a \<in> G" and B1:"\<alpha> a ` A = A" and B2:"b \<in> G" and B3:"\<alpha> b ` A = A"
      by (simp_all add:set_stabilizer_iff)
    have "\<alpha> (a \<cdot> b) ` A = \<alpha> a ` (\<alpha> b ` A)"
      unfolding image_image using A0 B0 B2 by (intro image_cong) (auto simp:act_assoc)
    also have "\<dots> = A"
      by (simp add:B1 B3)
    finally show "a \<cdot> b \<in> set_stabilizer A"
      using B0 B2 by (simp add:set_stabilizer_iff)
  qed
  show "\<And>a. a \<in> set_stabilizer A \<Longrightarrow> inv a \<in> set_stabilizer A"
  proof-
    fix a assume "a \<in> set_stabilizer A"
    then have B0:"a \<in> G" and B1:"\<alpha> a ` A = A"
      by (simp_all add:set_stabilizer_iff)
    have "\<alpha> (inv a) ` A = \<alpha> (inv a) ` (\<alpha> a ` A)"
      by (simp add:B1)
    also have "\<dots> = id ` A"
      unfolding image_image using A0 B0 by (intro image_cong) (auto simp:act_inv1)
    finally show "inv a \<in> set_stabilizer A"
      using B0 by (simp add:set_stabilizer_iff)
  qed
qed

definition fixer::"'b set \<Rightarrow> 'a set"
  where "fixer A = {g \<in> G. \<forall>x\<in>A. \<alpha> g x = x}"

lemma fixer_iff:"g \<in> fixer A \<longleftrightarrow> g \<in> G \<and> (\<forall>x\<in>A. \<alpha> g x = x)"
  by (simp add:fixer_def)

lemma fixer_sub:"fixer A \<subseteq> G"
  by (auto simp:fixer_def)

lemma fixer_stabilizers:"A \<noteq> {} \<Longrightarrow> fixer A = (\<Inter>x\<in>A. stabilizer x)"
  by (auto simp:fixer_def stabilizer_def)

lemma fixer_singleton:"fixer {x} = stabilizer x"
  by (auto simp:fixer_def stabilizer_def)

lemma fixer_sub_set_stabilizer:"fixer A \<subseteq> set_stabilizer A"
proof
  fix g assume B0:"g \<in> fixer A"
  have "\<alpha> g ` A = id ` A"
    using B0 by (intro image_cong) (auto simp:fixer_def)
  then show "g \<in> set_stabilizer A"
    using B0 by (simp add:set_stabilizer_iff fixer_iff)
qed

lemma fixer_subgroup:
  assumes A0:"A \<subseteq> E"
  shows "subgroup G (\<cdot>) \<one> (fixer A)"
proof(intro subgroup.intro group_axioms subgroup_axioms.intro)
  show "fixer A \<subseteq> G"
    by (rule fixer_sub)
  show "\<one> \<in> fixer A"
    using A0 act_unit by (auto simp:fixer_def)
  show "\<And>a b. \<lbrakk>a \<in> fixer A; b \<in> fixer A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> fixer A"
    using A0 by (auto simp:fixer_def act_assoc subset_iff)
  show "\<And>a. a \<in> fixer A \<Longrightarrow> inv a \<in> fixer A"
  proof-
    fix a assume B0:"a \<in> fixer A"
    then have B1:"a \<in> G"
      by (simp add:fixer_iff)
    have "\<And>x. x \<in> A \<Longrightarrow> \<alpha> (inv a) x = x"
    proof-
      fix x assume C0:"x \<in> A"
      have C1:"x \<in> E"
        using A0 C0 by auto
      have "\<alpha> (inv a) x = \<alpha> (inv a) (\<alpha> a x)"
        using B0 C0 by (simp add:fixer_iff)
      also have "\<dots> = x"
        using B1 C1 by (simp add:act_inv1)
      finally show "\<alpha> (inv a) x = x" .
    qed
    then show "inv a \<in> fixer A"
      using B1 by (simp add:fixer_iff)
  qed
qed

theorem fixer_normal:
  assumes A0:"A \<subseteq> E"
  shows "normal_subgroup (set_stabilizer A) (\<cdot>) \<one> (fixer A)"
proof-
  interpret s:subgroup G "(\<cdot>)" \<one> "set_stabilizer A"
    by (rule set_stabilizer_subgroup[OF A0])
  show ?thesis
  proof(intro normal_subgroup.intro subgroup.intro s.sub_group subgroup_axioms.intro normal_subgroup_axioms.intro)
    show "fixer A \<subseteq> set_stabilizer A"
      by (rule fixer_sub_set_stabilizer)
    show "\<one> \<in> fixer A"
      by (rule subgroup.id_mem[OF fixer_subgroup[OF A0]])
    show "\<And>a b. \<lbrakk>a \<in> fixer A; b \<in> fixer A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> fixer A"
      by (rule subgroup.sub_closed[OF fixer_subgroup[OF A0]])
    show "\<And>a. a \<in> fixer A \<Longrightarrow> s.sub.inv a \<in> fixer A"
    proof-
      fix a assume B0:"a \<in> fixer A"
      have "s.sub.inv a = inv a"
        using B0 fixer_sub_set_stabilizer by (intro s.sub_inv_eq) auto
      then show "s.sub.inv a \<in> fixer A"
        using subgroup.inv_cl[OF fixer_subgroup[OF A0] B0] by simp
    qed
    show "\<And>g h. \<lbrakk>g \<in> set_stabilizer A; h \<in> fixer A\<rbrakk> \<Longrightarrow> g \<cdot> h \<cdot> s.sub.inv g \<in> fixer A"
    proof-
      fix g h assume B0:"g \<in> set_stabilizer A" and B1:"h \<in> fixer A"
      have B2:"g \<in> G" and B3:"\<alpha> g ` A = A" and B4:"h \<in> G"
        using B0 B1 by (simp_all add:set_stabilizer_iff fixer_iff)
      have B5:"s.sub.inv g = inv g"
        by (rule s.sub_inv_eq[OF B0])
      have "\<And>x. x \<in> A \<Longrightarrow> \<alpha> (g \<cdot> h \<cdot> inv g) x = x"
      proof-
        fix x assume C0:"x \<in> A"
        have C1:"x \<in> E"
          using A0 C0 by auto
        have "x \<in> \<alpha> g ` A"
          using C0 by (simp only:B3)
        then obtain y where C2:"y \<in> A" and C3:"x = \<alpha> g y"
          by blast
        have C4:"y \<in> E"
          using A0 C2 by auto
        have C5:"\<alpha> (inv g) x \<in> A"
          using B2 C4 C2 by (simp add:C3 act_inv1)
        have "\<alpha> (g \<cdot> h \<cdot> inv g) x = \<alpha> g (\<alpha> h (\<alpha> (inv g) x))"
          using B2 B4 C1 by (simp add:act_assoc)
        also have "\<dots> = \<alpha> g (\<alpha> (inv g) x)"
          using B1 C5 by (simp add:fixer_iff)
        also have "\<dots> = x"
          using B2 C1 by (simp add:act_inv2)
        finally show "\<alpha> (g \<cdot> h \<cdot> inv g) x = x" .
      qed
      then show "g \<cdot> h \<cdot> s.sub.inv g \<in> fixer A"
        using B2 B4 by (simp add:fixer_iff B5)
    qed
  qed
qed

definition act_kernel::"'a set"
  where "act_kernel = {g \<in> G. \<forall>x\<in>E. \<alpha> g x = x}"

definition faithful::"bool"
  where "faithful \<longleftrightarrow> act_kernel = {\<one>}"

definition transitive::"bool"
  where "transitive \<longleftrightarrow> E \<noteq> {} \<and> (\<forall>x\<in>E. orbit x = E)"

definition free_action::"bool"
  where "free_action \<longleftrightarrow> (\<forall>x\<in>E. stabilizer x = {\<one>})"

lemma act_kernel_iff:"g \<in> act_kernel \<longleftrightarrow> g \<in> G \<and> (\<forall>x\<in>E. \<alpha> g x = x)"
  by (simp add:act_kernel_def)

lemma act_kernel_sub:"act_kernel \<subseteq> G"
  by (auto simp:act_kernel_def)

lemma fixer_whole:"fixer E = act_kernel"
  by (simp add:fixer_def act_kernel_def)

lemma act_kernel_stabilizers:"act_kernel = {g \<in> G. \<forall>x\<in>E. g \<in> stabilizer x}"
  by (auto simp:act_kernel_def stabilizer_def)

lemma l_law_eq_id_iff:
  assumes A0:"g \<in> G"
  shows "l_law g = (Id E) \<longleftrightarrow> (\<forall>x\<in>E. \<alpha> g x = x)"
proof
  assume B0:"l_law g = Id E"
  show "\<forall>x\<in>E. \<alpha> g x = x"
  proof
    fix x assume B1:"x \<in> E"
    have "\<alpha> g x = l_law g x"
      by (simp add:l_law_app[OF A0 B1])
    then show "\<alpha> g x = x"
      using B1 by (simp add:B0)
  qed
next
  assume B0:"\<forall>x\<in>E. \<alpha> g x = x"
  have "l_law g = (\<lambda>x\<in>E. \<alpha> g x)"
    using A0 by (simp add:l_law_def)
  also have "\<dots> = Id E"
    using B0 by (intro restrict_ext) simp
  finally show "l_law g = Id E" .
qed

context
begin

interpretation h:group_hom G "(\<cdot>)" \<one> "monoid.Units (set_mor E E) (compose E) (Id E)" "compose E" "Id E" l_law
  by (rule l_law_group_hom)

lemma act_kernel_Ker:"group_hom.Ker G (Id E) l_law = act_kernel"
  using l_law_eq_id_iff by (auto simp:h.Ker_def act_kernel_def)

theorem act_kernel_normal:"normal_subgroup G (\<cdot>) \<one> act_kernel"
  using h.Ker_normal by (simp add:act_kernel_Ker)

lemma faithful_iff:"faithful \<longleftrightarrow> inj_on l_law G"
  using h.inj_iff_Ker by (simp add:faithful_def act_kernel_Ker)

end

lemma free_imp_faithful:"\<lbrakk>E \<noteq> {}; free_action\<rbrakk> \<Longrightarrow> faithful"
proof-
  assume A0:"E \<noteq> {}" and A1:"free_action"
  obtain x where B0:"x \<in> E"
    using A0 by blast
  have "act_kernel \<subseteq> stabilizer x"
    using B0 by (auto simp:act_kernel_stabilizers)
  moreover have "\<one> \<in> act_kernel"
    using act_unit by (simp add:act_kernel_def)
  ultimately show "faithful"
    using A1 B0 by (auto simp:faithful_def free_action_def)
qed

lemma transitive_iff:"transitive \<longleftrightarrow> E \<noteq> {} \<and> (\<forall>x\<in>E. \<forall>y\<in>E. \<exists>g\<in>G. y = \<alpha> g x)"
  using orbit_sub by (auto simp:transitive_def orbit_iff)

lemma transitive_orbits:"transitive \<Longrightarrow> orbits = {E}"
  by (auto simp:transitive_def orbits_def)

end

subsubsection \<open>Equivariant maps\<close>

locale equivariant = dom:monoid_action M mul e E \<alpha> + cod:monoid_action M mul e F \<beta>
  for M::"'a set" and mul::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) and e::'a ("\<one>")
    and E::"'b set" and \<alpha>::"'a \<Rightarrow> 'b \<Rightarrow> 'b" and F::"'c set" and \<beta>::"'a \<Rightarrow> 'c \<Rightarrow> 'c" +
  fixes f::"'b \<Rightarrow> 'c"
  assumes maps[simp, intro]:"x \<in> E \<Longrightarrow> f x \<in> F"
    and equivariant:"\<lbrakk>m \<in> M; x \<in> E\<rbrakk> \<Longrightarrow> f (\<alpha> m x) = \<beta> m (f x)"
begin

lemma orbit_image:
  assumes A0:"x \<in> E"
  shows "f ` dom.orbit x = cod.orbit (f x)"
proof
  show "f ` dom.orbit x \<subseteq> cod.orbit (f x)"
  proof
    fix y assume "y \<in> f ` dom.orbit x"
    then obtain m where B0:"m \<in> M" and B1:"y = f (\<alpha> m x)"
      by (auto simp:dom.orbit_iff)
    have B2:"y = \<beta> m (f x)"
      using A0 B0 by (simp add:B1 equivariant)
    show "y \<in> cod.orbit (f x)"
      unfolding B2 cod.orbit_def using B0 by (rule UN_I) simp
  qed
  show "cod.orbit (f x) \<subseteq> f ` dom.orbit x"
  proof
    fix y assume "y \<in> cod.orbit (f x)"
    then obtain m where B0:"m \<in> M" and B1:"y = \<beta> m (f x)"
      by (auto simp:cod.orbit_iff)
    have B2:"y = f (\<alpha> m x)"
      using A0 B0 by (simp add:B1 equivariant)
    have "\<alpha> m x \<in> dom.orbit x"
      unfolding dom.orbit_def using B0 by (rule UN_I) simp
    then show "y \<in> f ` dom.orbit x"
      unfolding B2 by (rule imageI)
  qed
qed

lemma stabilizer_image:"x \<in> E \<Longrightarrow> dom.stabilizer x \<subseteq> cod.stabilizer (f x)"
  by (auto simp:dom.stabilizer_def cod.stabilizer_def equivariant[symmetric])

lemma fixed_points_image:"f ` dom.fixed_points \<subseteq> cod.fixed_points"
  by (auto simp:dom.fixed_points_def cod.fixed_points_def equivariant[symmetric])

lemma invariant_image:"dom.invariant A \<Longrightarrow> cod.invariant (f ` A)"
  by (auto simp:dom.invariant_def cod.invariant_def equivariant[symmetric])

end
subsection \<open>Composition, restriction and inversion of group isomorphisms\<close>

lemma group_iso_compose:
  assumes A0:"group_iso X mul e Y mul' e' f" and A1:"group_iso Y mul' e' Z mul'' e'' g"
  shows "group_iso X mul e Z mul'' e'' (g \<circ> f)"
proof-
  interpret f:group_iso X mul e Y mul' e' f by (rule A0)
  interpret g:group_iso Y mul' e' Z mul'' e'' g by (rule A1)
  interpret gf:magma_iso X mul Z mul'' "g \<circ> f"
    by (rule magma_iso_compose[OF f.magma_iso_axioms g.magma_iso_axioms])
  show ?thesis
    by (intro group_iso.intro group_iso_axioms.intro group_hom.intro gf.magma_hom_axioms f.dom.group_axioms g.cod.group_axioms gf.bij)
qed

lemma group_iso_restrict:
  assumes A0:"group_iso X mul e Y mul' e' f"
  shows "group_iso X mul e Y mul' e' (\<lambda>x\<in>X. f x)"
proof-
  interpret f:group_iso X mul e Y mul' e' f by (rule A0)
  show ?thesis
  proof(intro group_iso.intro group_iso_axioms.intro group_hom.intro magma_hom.intro magma_hom_axioms.intro
              f.dom.magma_axioms f.cod.magma_axioms f.dom.group_axioms f.cod.group_axioms)
    show "\<And>x. x \<in> X \<Longrightarrow> (\<lambda>x\<in>X. f x) x \<in> Y"
      by simp
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (\<lambda>x\<in>X. f x) (mul x y) = mul' ((\<lambda>x\<in>X. f x) x) ((\<lambda>x\<in>X. f x) y)"
      by (simp add:f.hom)
    have "bij_betw (\<lambda>x\<in>X. f x) X Y = bij_betw f X Y"
      by (rule bij_betw_cong) simp
    then show "bij_betw (\<lambda>x\<in>X. f x) X Y"
      by (simp add:f.bij)
  qed
qed

lemma (in group_iso) inv_group_iso:"group_iso Y (\<star>) e' X (\<cdot>) e (inv_into X f)"
proof-
  interpret i:magma_iso Y "(\<star>)" X "(\<cdot>)" "inv_into X f"
    by (rule inv_iso)
  show ?thesis
    by (intro group_iso.intro group_iso_axioms.intro group_hom.intro i.magma_hom_axioms cod.group_axioms dom.group_axioms i.bij)
qed


subsection \<open>The conjugation action and the class equation\<close>

context group
begin

lemma centralizer_subgroup:
  assumes A0:"A \<subseteq> X"
  shows "subgroup X (\<cdot>) \<one> (centralizer A)"
proof(intro subgroup.intro group_axioms subgroup_axioms.intro)
  show "centralizer A \<subseteq> X"
    by (rule centralizer_sub)
  show "\<one> \<in> centralizer A"
    using A0 by (intro centralizer_memI2) (auto simp:subset_iff)
  show "\<And>a b. \<lbrakk>a \<in> centralizer A; b \<in> centralizer A\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> centralizer A"
    by (rule subsD(2)[OF centralizer_sub_closed[OF A0]])
  show "\<And>b. b \<in> centralizer A \<Longrightarrow> inv b \<in> centralizer A"
  proof-
    fix b assume B0:"b \<in> centralizer A"
    have B1:"b \<in> X"
      using B0 centralizer_sub by auto
    show "inv b \<in> centralizer A"
    proof(rule centralizer_memI2)
      show "inv b \<in> X"
        using B1 by simp
      fix a assume C0:"a \<in> A"
      then have C1:"a \<in> X"
        using A0 by auto
      show "inv b \<cdot> a = a \<cdot> inv b"
        by (rule commute_inv[OF C1 B1 centralizer_memD[OF B0 C0]])
    qed
  qed
qed

lemma center_subgroup:"subgroup X (\<cdot>) \<one> center"
  unfolding center_def by (rule centralizer_subgroup) simp

theorem center_normal:"normal_subgroup X (\<cdot>) \<one> center"
proof(intro normal_subgroup.intro center_subgroup normal_subgroup_axioms.intro)
  fix g h assume B0:"g \<in> X" and B1:"h \<in> center"
  have B2:"h \<in> X"
    using B1 center_sub by auto
  have "g \<cdot> h \<cdot> inv g = h \<cdot> g \<cdot> inv g"
    by (simp add:center_memD[OF B1 B0])
  also have "\<dots> = h"
    using B0 B2 by (simp add:assoc)
  finally show "g \<cdot> h \<cdot> inv g \<in> center"
    by (simp add:B1)
qed

end

sublocale group \<subseteq> conj:group_action X "(\<cdot>)" \<one> X "\<lambda>x g. rconj g x"
proof(intro group_action.intro group_axioms monoid_action.intro monoid_action_axioms.intro monoid_axioms action.intro)
  show "\<And>x g. \<lbrakk>x \<in> X; g \<in> X\<rbrakk> \<Longrightarrow> rconj g x \<in> X"
    by simp
  show "\<And>g. g \<in> X \<Longrightarrow> rconj g \<one> = g"
    by (simp add:rconj_def)
  show "\<And>x y g. \<lbrakk>x \<in> X; y \<in> X; g \<in> X\<rbrakk> \<Longrightarrow> rconj g (x \<cdot> y) = rconj (rconj g y) x"
    by (simp add:rconj_rconj)
qed

context group
begin

lemma conj_orbit:"conj.orbit g = conjugacy_class g"
  by (auto simp:conj.orbit_iff conjugacy_class_iff)

lemma conj_stabilizer:
  assumes A0:"g \<in> X"
  shows "conj.stabilizer g = centralizer {g}"
proof-
  have "centralizer {g} = {b \<in> X. rconj g b = g}"
    using A0 by (simp add:centralizer_rconj)
  then show ?thesis
    by (simp add:conj.stabilizer_def)
qed

lemma conj_fixed_points:"conj.fixed_points = center"
proof-
  have B0:"\<And>g x. \<lbrakk>g \<in> X; x \<in> X\<rbrakk> \<Longrightarrow> rconj g x = g \<longleftrightarrow> g \<cdot> x = x \<cdot> g"
  proof-
    fix g x assume C0:"g \<in> X" and C1:"x \<in> X"
    have "rconj g x = g \<longleftrightarrow> x \<cdot> g = g \<cdot> x"
      using C0 C1 by (simp add:rconj_def inv_rsolve2)
    then show "rconj g x = g \<longleftrightarrow> g \<cdot> x = x \<cdot> g"
      by auto
  qed
  show ?thesis
    by (auto simp:conj.fixed_points_def center_mem_iff B0)
qed

lemma conj_act_kernel:"conj.act_kernel = center"
  by (simp add:conj.act_kernel_def center_def centralizer_rconj)

lemma conj_faithful_iff:"conj.faithful \<longleftrightarrow> center = {\<one>}"
  by (simp add:conj.faithful_def conj_act_kernel)

definition conjugacy_classes::"'a set set"
  where "conjugacy_classes = (\<Union>g\<in>X. {conjugacy_class g})"

lemma conjugacy_classes_iff:"C \<in> conjugacy_classes \<longleftrightarrow> (\<exists>g\<in>X. C = conjugacy_class g)"
  by (auto simp:conjugacy_classes_def)

lemma conj_orbits:"conj.orbits = conjugacy_classes"
  by (simp add:conj.orbits_def conjugacy_classes_def conj_orbit)

lemma conjugacy_classes_Union:"\<Union>conjugacy_classes = X"
  using conj.orbits_Union by (simp add:conj_orbits)

lemma conjugacy_classes_disjoint:"\<lbrakk>C \<in> conjugacy_classes; D \<in> conjugacy_classes; C \<noteq> D\<rbrakk> \<Longrightarrow> C \<inter> D = {}"
  using conj.orbits_disjoint by (simp add:conj_orbits)

lemma conjugacy_class_eq_iff:"\<lbrakk>g \<in> X; h \<in> X\<rbrakk> \<Longrightarrow> conjugacy_class g = conjugacy_class h \<longleftrightarrow> h \<in> conjugacy_class g"
  using conj.orbit_eq_iff by (simp add:conj_orbit)

lemma conjugacy_class_card:
  assumes A0:"finite X" and A1:"g \<in> X"
  shows "card (conjugacy_class g) * card (centralizer {g}) = card X"
  using conj.orbit_stabilizer_card[OF A0 A1] by (simp add:conj_orbit conj_stabilizer[OF A1])

lemma conjugacy_class_card_dvd:
  assumes A0:"finite X" and A1:"g \<in> X"
  shows "card (conjugacy_class g) dvd card X"
  using conj.orbit_card_dvd[OF A0 A1] by (simp add:conj_orbit)

lemma conjugacy_class_singleton_iff:
  assumes A0:"g \<in> X"
  shows "conjugacy_class g = {g} \<longleftrightarrow> g \<in> center"
proof
  assume B0:"conjugacy_class g = {g}"
  have "\<And>x. x \<in> X \<Longrightarrow> rconj g x = g"
  proof-
    fix x assume "x \<in> X"
    then have "rconj g x \<in> conjugacy_class g"
      by (auto simp:conjugacy_class_iff intro:bexI[where x = x])
    then show "rconj g x = g"
      by (simp add:B0)
  qed
  then show "g \<in> center"
    using A0 by (simp add:conj_fixed_points[symmetric] conj.fixed_points_def)
next
  assume B0:"g \<in> center"
  then have B1:"\<And>x. x \<in> X \<Longrightarrow> rconj g x = g"
    by (simp add:conj_fixed_points[symmetric] conj.fixed_points_def)
  show "conjugacy_class g = {g}"
    using conjugacy_class_refl[OF A0] B1 by (auto simp:conjugacy_class_iff)
qed

theorem class_equation:
  assumes A0:"finite X"
  shows "card X = card center + (\<Sum>C\<in>{C \<in> conjugacy_classes. 1 < card C}. card C)"
proof-
  define S where "S = {C \<in> conjugacy_classes. card C = 1}"
  define T where "T = {C \<in> conjugacy_classes. 1 < card C}"
  have B0:"finite conjugacy_classes"
    using A0 by (simp add:conjugacy_classes_def)
  have B1:"\<And>C. C \<in> conjugacy_classes \<Longrightarrow> 1 \<le> card C"
  proof-
    fix C assume "C \<in> conjugacy_classes"
    then obtain g where C0:"g \<in> X" and C1:"C = conjugacy_class g"
      by (auto simp:conjugacy_classes_def)
    have "finite C"
      using A0 conjugacy_class_sub[OF C0] by (simp add:C1 finite_subset)
    moreover have "C \<noteq> {}"
      using conjugacy_class_refl[OF C0] by (auto simp:C1)
    ultimately show "1 \<le> card C"
      by (simp add:Suc_le_eq card_gt_0_iff)
  qed
  have B2:"conjugacy_classes = S \<union> T"
  proof
    show "conjugacy_classes \<subseteq> S \<union> T"
    proof
      fix C assume C0:"C \<in> conjugacy_classes"
      have "card C = 1 \<or> 1 < card C"
        using B1[OF C0] by linarith
      then show "C \<in> S \<union> T"
        using C0 by (auto simp:S_def T_def)
    qed
    show "S \<union> T \<subseteq> conjugacy_classes"
      by (auto simp:S_def T_def)
  qed
  have B3:"S \<inter> T = {}"
    by (auto simp:S_def T_def)
  have B4:"finite S"
    by (rule finite_subset[OF _ B0]) (auto simp:S_def)
  have B5:"finite T"
    by (rule finite_subset[OF _ B0]) (auto simp:T_def)
  have B6:"S = (\<lambda>z. {z}) ` center"
  proof
    show "S \<subseteq> (\<lambda>z. {z}) ` center"
    proof
      fix C assume "C \<in> S"
      then obtain g where C0:"g \<in> X" and C1:"C = conjugacy_class g" and C2:"card C = 1"
        by (auto simp:S_def conjugacy_classes_def)
      obtain x where C3:"C = {x}"
        using C2 by (rule card_1_singletonE)
      have "g \<in> C"
        using conjugacy_class_refl[OF C0] by (simp add:C1)
      then have "C = {g}"
        using C3 by simp
      then show "C \<in> (\<lambda>z. {z}) ` center"
        using conjugacy_class_singleton_iff[OF C0] C1 by blast
    qed
    show "(\<lambda>z. {z}) ` center \<subseteq> S"
    proof
      fix C assume "C \<in> (\<lambda>z. {z}) ` center"
      then obtain z where C0:"z \<in> center" and C1:"C = {z}"
        by blast
      have C2:"z \<in> X"
        using C0 center_sub by blast
      have "conjugacy_class z = {z}"
        using C0 by (simp add:conjugacy_class_singleton_iff[OF C2])
      then show "C \<in> S"
        using C2 by (auto simp:S_def conjugacy_classes_def C1)
    qed
  qed
  have B7:"(\<Sum>C\<in>S. card C) = card center"
  proof-
    have "(\<Sum>C\<in>S. card C) = (\<Sum>C\<in>S. 1)"
      by (rule sum.cong) (simp_all add:S_def)
    also have "\<dots> = card S"
      by simp
    also have "\<dots> = card center"
      unfolding B6 by (rule card_image) (simp add:inj_on_def)
    finally show ?thesis .
  qed
  have "card X = (\<Sum>C\<in>conjugacy_classes. card C)"
    using conj.card_orbits[OF A0] by (simp add:conj_orbits)
  also have "\<dots> = (\<Sum>C\<in>S. card C) + (\<Sum>C\<in>T. card C)"
    unfolding B2 by (rule sum.union_disjoint[OF B4 B5 B3])
  finally show ?thesis
    by (simp add:B7 T_def)
qed

subsection \<open>Cayley's theorem for groups\<close>

context
begin

interpretation sym:set_endomorphisms X .

lemma l_trans_Units:"x \<in> X \<Longrightarrow> l_trans x \<in> sym.Units"
proof-
  assume A0:"x \<in> X"
  show "l_trans x \<in> sym.Units"
    using l_trans_maps[OF A0] l_trans_bij[OF A0] by (simp add:sym.Units_iff)
qed

lemma l_trans_group_hom:"group_hom X (\<cdot>) \<one> sym.Units (compose X) (Id X) l_trans"
proof-
  have B0:"group sym.Units (compose X) (Id X)"
    by (rule sym.Units_group)
  have B1:"magma sym.Units (compose X)"
    by (rule semigroup.axioms(1)[OF monoid.axioms(1)[OF group.axioms(1)[OF B0]]])
  show ?thesis
  proof(intro group_hom.intro magma_hom.intro magma_hom_axioms.intro magma_axioms group_axioms B0 B1)
    show "\<And>x. x \<in> X \<Longrightarrow> l_trans x \<in> sym.Units"
      by (rule l_trans_Units)
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> l_trans (x \<cdot> y) = compose X (l_trans x) (l_trans y)"
      by (rule l_trans_comp)
  qed
qed

context
begin

interpretation h:group_hom X "(\<cdot>)" \<one> sym.Units "compose X" "Id X" l_trans
  by (rule l_trans_group_hom)

theorem cayley_group:"group_iso X (\<cdot>) \<one> (l_trans ` X) (compose X) (Id X) l_trans"
proof-
  interpret c:magma_iso X "(\<cdot>)" "l_trans ` X" "compose X" l_trans
    by (rule cayley)
  show ?thesis
    by (intro group_iso.intro group_iso_axioms.intro group_hom.intro c.magma_hom_axioms group_axioms h.im_group c.bij)
qed

lemma l_trans_sym_subgroup:"subgroup sym.Units (compose X) (Id X) (l_trans ` X)"
  by (rule h.im_subgroup)

lemma l_trans_Ker:"h.Ker = {\<one>}"
  using h.inj_iff_Ker l_trans_inj by simp

end

subsection \<open>Automorphisms\<close>

definition Aut::"('a \<Rightarrow> 'a) set"
  where "Aut = {f \<in> set_mor X X. group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> f}"

lemma Aut_iff:"f \<in> Aut \<longleftrightarrow> f \<in> set_mor X X \<and> group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> f"
  by (simp add:Aut_def)

lemma Aut_memI:"\<lbrakk>f \<in> set_mor X X; group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> f\<rbrakk> \<Longrightarrow> f \<in> Aut"
  and Aut_memD1:"f \<in> Aut \<Longrightarrow> f \<in> set_mor X X"
  and Aut_memD2:"f \<in> Aut \<Longrightarrow> group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> f"
  by (simp_all add:Aut_def)

lemma Aut_sub_sym:"Aut \<subseteq> sym.Units"
  using group_iso.bij by (auto simp:Aut_def sym.Units_iff)

lemma Aut_id:"Id X \<in> Aut"
proof(rule Aut_memI)
  show "Id X \<in> set_mor X X"
    by auto
  show "group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (Id X)"
  proof(intro group_iso.intro group_iso_axioms.intro group_hom.intro magma_hom.intro magma_hom_axioms.intro magma_axioms group_axioms)
    show "\<And>x. x \<in> X \<Longrightarrow> (Id X) x \<in> X"
      by simp
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (Id X) (x \<cdot> y) = (Id X) x \<cdot> (Id X) y"
      by simp
    show "bij_betw (Id X) X X"
      by (rule bij_betwI2[where g = "Id X"]) auto
  qed
qed

lemma Aut_compose:
  assumes A0:"f \<in> Aut" and A1:"g \<in> Aut"
  shows "compose X f g \<in> Aut"
proof(rule Aut_memI)
  have B0:"f \<in> sym.Units" and B1:"g \<in> sym.Units"
    using A0 A1 Aut_sub_sym by auto
  show "compose X f g \<in> set_mor X X"
    by (rule sym.Units_memD1[OF sym.Units_closed[OF B0 B1]])
  have "group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (f \<circ> g)"
    by (rule group_iso_compose[OF Aut_memD2[OF A1] Aut_memD2[OF A0]])
  then have "group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (\<lambda>x\<in>X. (f \<circ> g) x)"
    by (rule group_iso_restrict)
  then show "group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (compose X f g)"
    by (simp add:compose_def)
qed

lemma Aut_inv:
  assumes A0:"f \<in> Aut"
  shows "(\<lambda>y\<in>X. inv_into X f y) \<in> Aut"
proof(rule Aut_memI)
  interpret f:group_iso X "(\<cdot>)" \<one> X "(\<cdot>)" \<one> f
    by (rule Aut_memD2[OF A0])
  show "(\<lambda>y\<in>X. inv_into X f y) \<in> set_mor X X"
    using f.inv_maps by auto
  show "group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (\<lambda>y\<in>X. inv_into X f y)"
    by (rule group_iso_restrict[OF f.inv_group_iso])
qed

lemma Aut_subgroup:"subgroup sym.Units (compose X) (Id X) Aut"
proof(intro subgroup.intro sym.Units_group subgroup_axioms.intro)
  show "Aut \<subseteq> sym.Units"
    by (rule Aut_sub_sym)
  show "Id X \<in> Aut"
    by (rule Aut_id)
  show "\<And>a b. \<lbrakk>a \<in> Aut; b \<in> Aut\<rbrakk> \<Longrightarrow> compose X a b \<in> Aut"
    by (rule Aut_compose)
  show "\<And>a. a \<in> Aut \<Longrightarrow> monoid.inv sym.Units (compose X) (Id X) a \<in> Aut"
  proof-
    fix a assume B0:"a \<in> Aut"
    have B1:"a \<in> sym.Units"
      using B0 Aut_sub_sym by auto
    have "monoid.inv sym.Units (compose X) (Id X) a = (\<lambda>y\<in>X. inv_into X a y)"
      by (simp add:sym.Units_inv_eq[OF B1] sym.Units_inv[OF B1])
    then show "monoid.inv sym.Units (compose X) (Id X) a \<in> Aut"
      by (simp add:Aut_inv[OF B0])
  qed
qed

lemma Aut_group:"group Aut (compose X) (Id X)"
  by (rule subgroup.sub_group[OF Aut_subgroup])

definition inner::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "inner x = (\<lambda>g\<in>X. rconj g x)"

definition Inn::"('a \<Rightarrow> 'a) set"
  where "Inn = inner ` X"

lemma inner_app:"\<lbrakk>x \<in> X; g \<in> X\<rbrakk> \<Longrightarrow> inner x g = rconj g x"
  by (simp add:inner_def)

lemma inner_maps:"x \<in> X \<Longrightarrow> inner x \<in> set_mor X X"
  by (auto simp:inner_def)

lemma inner_iso:"x \<in> X \<Longrightarrow> group_iso X (\<cdot>) \<one> X (\<cdot>) \<one> (inner x)"
  unfolding inner_def by (rule group_iso_restrict[OF inner_aut])

lemma inner_Aut:"x \<in> X \<Longrightarrow> inner x \<in> Aut"
  by (rule Aut_memI[OF inner_maps inner_iso])

lemma Inn_sub_Aut:"Inn \<subseteq> Aut"
  using inner_Aut by (auto simp:Inn_def)

lemma inner_unit:"inner \<one> = Id X"
  unfolding inner_def by (rule restrict_ext) (simp add:rconj_def)

lemma inner_comp:
  assumes A0:"x \<in> X" and A1:"y \<in> X"
  shows "inner (x \<cdot> y) = compose X (inner x) (inner y)"
proof(rule maps_on_eqI1[of _ X])
  show "inner (x \<cdot> y) \<in> maps_on X" and "compose X (inner x) (inner y) \<in> maps_on X"
    by (simp_all add:inner_def)
  fix g assume B0:"g \<in> X"
  have "compose X (inner x) (inner y) g = rconj (rconj g y) x"
    using A0 A1 B0 by (simp add:comp_eq inner_app)
  also have "\<dots> = rconj g (x \<cdot> y)"
    using A0 A1 B0 by (simp add:rconj_rconj)
  finally show "inner (x \<cdot> y) g = compose X (inner x) (inner y) g"
    using A0 A1 B0 by (simp add:inner_app)
qed

lemma inner_hom:"group_hom X (\<cdot>) \<one> Aut (compose X) (Id X) inner"
proof-
  have B0:"group Aut (compose X) (Id X)"
    by (rule Aut_group)
  have B1:"magma Aut (compose X)"
    by (rule semigroup.axioms(1)[OF monoid.axioms(1)[OF group.axioms(1)[OF B0]]])
  show ?thesis
  proof(intro group_hom.intro magma_hom.intro magma_hom_axioms.intro magma_axioms group_axioms B0 B1)
    show "\<And>x. x \<in> X \<Longrightarrow> inner x \<in> Aut"
      by (rule inner_Aut)
    show "\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> inner (x \<cdot> y) = compose X (inner x) (inner y)"
      by (rule inner_comp)
  qed
qed

lemma inner_eq_id_iff:
  assumes A0:"x \<in> X"
  shows "inner x = (Id X) \<longleftrightarrow> x \<in> center"
proof
  assume B0:"inner x = Id X"
  have "\<And>g. g \<in> X \<Longrightarrow> rconj g x = g"
  proof-
    fix g assume C0:"g \<in> X"
    have "rconj g x = inner x g"
      by (simp add:inner_app[OF A0 C0])
    then show "rconj g x = g"
      using C0 by (simp add:B0)
  qed
  then show "x \<in> center"
    using A0 by (simp add:conj_act_kernel[symmetric] conj.act_kernel_def)
next
  assume B0:"x \<in> center"
  then have B1:"\<And>g. g \<in> X \<Longrightarrow> rconj g x = g"
    by (simp add:conj_act_kernel[symmetric] conj.act_kernel_def)
  show "inner x = Id X"
    unfolding inner_def by (rule restrict_ext) (simp add:B1)
qed

context
begin

interpretation h:group_hom X "(\<cdot>)" \<one> Aut "compose X" "Id X" inner
  by (rule inner_hom)

interpretation z:normal_subgroup X "(\<cdot>)" \<one> center
  by (rule center_normal)

lemma inner_Ker:"h.Ker = center"
proof
  show "h.Ker \<subseteq> center"
    using inner_eq_id_iff by (auto simp:h.Ker_def)
  show "center \<subseteq> h.Ker"
    using inner_eq_id_iff center_sub by (auto simp:h.Ker_def)
qed

lemma Inn_subgroup:"subgroup Aut (compose X) (Id X) Inn"
  unfolding Inn_def by (rule h.im_subgroup)

lemma Inn_group:"group Inn (compose X) (Id X)"
  unfolding Inn_def by (rule h.im_group)

theorem Inn_iso:
  obtains k where "group_iso (l_cosets center) z.quo.qmul center Inn (compose X) (Id X) k"
    and "\<And>x. x \<in> X \<Longrightarrow> k (l_coset x center) = inner x"
proof-
  obtain k where B0:"group_iso z.quo.quot z.quo.qmul (z.quo.cls \<one>) (inner ` X) (compose X) (Id X) k"
    and B1:"\<And>x. x \<in> X \<Longrightarrow> k (z.quo.cls x) = inner x"
    using h.first_iso_group[unfolded inner_Ker] by blast
  have B2:"group_iso (l_cosets center) z.quo.qmul center Inn (compose X) (Id X) k"
    using B0 by (simp add:z.quo_quot z.quo_unit Inn_def)
  have B3:"\<And>x. x \<in> X \<Longrightarrow> k (l_coset x center) = inner x"
    using B1 by (simp add:z.quo_cls)
  show thesis
    by (rule that[OF B2 B3])
qed

end

theorem Inn_normal:"normal_subgroup Aut (compose X) (Id X) Inn"
proof(intro normal_subgroup.intro Inn_subgroup normal_subgroup_axioms.intro)
  fix f g assume B0:"f \<in> Aut" and B1:"g \<in> Inn"
  obtain x where B2:"x \<in> X" and B3:"g = inner x"
    using B1 by (auto simp:Inn_def)
  interpret f:group_iso X "(\<cdot>)" \<one> X "(\<cdot>)" \<one> f
    by (rule Aut_memD2[OF B0])
  interpret a:group Aut "compose X" "Id X"
    by (rule Aut_group)
  have B4:"a.inv f = (\<lambda>y\<in>X. inv_into X f y)"
  proof(rule a.inv_eq)
    show "compose X f (\<lambda>y\<in>X. inv_into X f y) = Id X"
      by (rule sym.bij_restrict_inv_right[OF Aut_memD1[OF B0] f.bij])
    show "compose X (\<lambda>y\<in>X. inv_into X f y) f = Id X"
      by (rule sym.bij_restrict_inv_left[OF Aut_memD1[OF B0] f.bij])
    show "f \<in> Aut"
      by (rule B0)
    show "(\<lambda>y\<in>X. inv_into X f y) \<in> Aut"
      by (rule Aut_inv[OF B0])
  qed
  have B5:"\<And>y. y \<in> X \<Longrightarrow> compose X (compose X f g) (a.inv f) y = inner (f x) y"
  proof-
    fix y assume C0:"y \<in> X"
    have C1:"inv_into X f y \<in> X"
      by (rule f.inv_maps[OF C0])
    have "compose X (compose X f g) (a.inv f) y = f (rconj (inv_into X f y) x)"
      using C0 C1 by (simp add:comp_eq B3 B4 inner_app[OF B2])
    also have "\<dots> = f x \<cdot> f (inv_into X f y) \<cdot> f (inv x)"
      using B2 C1 by (simp add:rconj_def f.hom)
    also have "\<dots> = f x \<cdot> y \<cdot> inv (f x)"
      using B2 by (simp add:f.f_inv[OF C0] f.hom_inv)
    also have "\<dots> = inner (f x) y"
      using B2 C0 by (simp add:inner_app rconj_def)
    finally show "compose X (compose X f g) (a.inv f) y = inner (f x) y" .
  qed
  have B6:"compose X (compose X f g) (a.inv f) = inner (f x)"
  proof(rule maps_on_eqI1[of _ X])
    show "compose X (compose X f g) (a.inv f) \<in> maps_on X"
      by simp
    show "inner (f x) \<in> maps_on X"
      by (simp add:inner_def)
    show "\<And>y. y \<in> X \<Longrightarrow> compose X (compose X f g) (a.inv f) y = inner (f x) y"
      by (rule B5)
  qed
  show "compose X (compose X f g) (a.inv f) \<in> Inn"
    unfolding B6 Inn_def using f.maps[OF B2] by (rule imageI)
qed

end

end

section \<open>Free Magmas\<close>

datatype 'a frm = Em 'a ("\<eta>") | Op "'a frm" "'a frm" (infixl "\<star>" 65)

inductive_set free_magma::"'a set \<Rightarrow> 'a frm set" for X::"'a set"
  where embeds[intro, simp]:"x \<in> X \<Longrightarrow> \<eta> x \<in> free_magma X"
      | closed[intro, simp]:"\<lbrakk>s \<in> free_magma X; t \<in> free_magma X\<rbrakk> \<Longrightarrow> s \<star> t \<in> free_magma X"

inductive_cases free_magma_emE:"\<eta> x \<in> free_magma X"
  and free_magma_opE:"s \<star> t \<in> free_magma X"

lemma set_frm_ne:"set_frm t \<noteq> {}"
  by (induction t) simp_all

lemma free_magma_iff:"t \<in> free_magma X \<longleftrightarrow> set_frm t \<subseteq> X"
proof
  assume "t \<in> free_magma X"
  then show "set_frm t \<subseteq> X"
    by induction auto
next
  assume "set_frm t \<subseteq> X"
  then show "t \<in> free_magma X"
    by (induction t) auto
qed

lemma free_magma_mono:"X \<subseteq> Y \<Longrightarrow> free_magma X \<subseteq> free_magma Y"
  by (auto simp:free_magma_iff)

lemma free_magma_Int:"free_magma (X \<inter> Y) = free_magma X \<inter> free_magma Y"
  by (auto simp:free_magma_iff)

lemma free_magma_Inter:"free_magma (\<Inter>\<X>) = (\<Inter>X\<in>\<X>. free_magma X)"
  by (auto simp:free_magma_iff subset_iff)

lemma free_magma_empty:"free_magma {} = {}"
  by (auto simp:free_magma_iff set_frm_ne)

lemma free_magma_UNIV:"free_magma UNIV = UNIV"
  by (auto simp:free_magma_iff)

lemma free_magma_cases:
  assumes A0:"t \<in> free_magma X"
  obtains x where "x \<in> X" and "t = \<eta> x"
        | s u where "s \<in> free_magma X" and "u \<in> free_magma X" and "t = s \<star> u"
  using A0 by cases auto

lemma free_magma_magma:"magma (free_magma X) (\<star>)"
  by unfold_locales simp

lemma free_magma_cancel:"s \<star> t = s' \<star> t' \<longleftrightarrow> s = s' \<and> t = t'"
  by simp

subsection \<open>Generators and length\<close>

definition generators::"'a set \<Rightarrow> 'a frm set" ("'\<langle>_'\<rangle>")
  where "\<langle>X\<rangle> = \<eta> ` X"

lemma generators_iff:"t \<in> \<langle>X\<rangle> \<longleftrightarrow> (\<exists>x\<in>X. t = \<eta> x)"
  by (auto simp:generators_def)

lemma generators_memI:"x \<in> X \<Longrightarrow> \<eta> x \<in> \<langle>X\<rangle>"
  by (simp add:generators_def)

lemma generators_sub:"\<langle>X\<rangle> \<subseteq> free_magma X"
  by (auto simp:generators_def)

lemma eta_inj:"inj_on \<eta> X"
  by (simp add:inj_on_def)

lemma eta_bij:"bij_betw \<eta> X \<langle>X\<rangle>"
  by (simp add:bij_betw_def eta_inj generators_def)

lemma generators_irreducible:"\<lbrakk>t \<in> \<langle>X\<rangle>; s \<in> free_magma X; u \<in> free_magma X\<rbrakk> \<Longrightarrow> t \<noteq> s \<star> u"
  by (auto simp:generators_def)

lemma generators_iff_irreducible:
  assumes A0:"t \<in> free_magma X"
  shows "t \<in> \<langle>X\<rangle> \<longleftrightarrow> \<not>(\<exists>s u. s \<in> free_magma X \<and> u \<in> free_magma X \<and> t = s \<star> u)"
proof(cases t)
  case (Em x)
  then show ?thesis
    using A0 by (simp add:generators_def free_magma_iff)
next
  case (Op s u)
  have "s \<in> free_magma X" and "u \<in> free_magma X"
    using A0 by (simp_all add:Op free_magma_iff)
  then show ?thesis
    by (auto simp:Op generators_def)
qed

fun len::"'a frm \<Rightarrow> nat"
  where "len (\<eta> x) = 1"
      | "len (s \<star> t) = len s + len t"

lemma len_gt_0:"0 < len t"
  by (induction t) simp_all

lemma len_op1:"len s < len (s \<star> t)"
  and len_op2:"len t < len (s \<star> t)"
  using len_gt_0 by simp_all

lemma len_1_iff:"len t = 1 \<longleftrightarrow> (\<exists>x. t = \<eta> x)"
proof(cases t)
  case (Em x)
  then show ?thesis
    by simp
next
  case (Op s u)
  then show ?thesis
    using len_gt_0[of s] len_gt_0[of u] by simp
qed

lemma (in magma) genE:
  assumes A0:"a \<in> gen A" and A1:"a \<notin> A"
  obtains b c where "b \<in> gen A" and "c \<in> gen A" and "a = b \<cdot> c"
  using A0 A1 by (cases rule:gen.cases) auto

subsection \<open>The free magma as a magma\<close>

locale free_magma_locale =
  fixes X::"'a set"
begin

sublocale frm:magma "free_magma X" "(\<star>)"
  by (rule free_magma_magma)

lemma generators_cl:"frm.sub.cl \<langle>X\<rangle> = free_magma X"
proof
  show "frm.sub.cl \<langle>X\<rangle> \<subseteq> free_magma X"
    by (rule frm.sub.cl_least[OF frm.sub.whole generators_sub])
  show "free_magma X \<subseteq> frm.sub.cl \<langle>X\<rangle>"
  proof
    fix t assume "t \<in> free_magma X"
    then show "t \<in> frm.sub.cl \<langle>X\<rangle>"
    proof induction
      case (embeds x)
      then show ?case
        using frm.sub.cl_extensive[of "\<langle>X\<rangle>"] by (auto simp:generators_def)
    next
      case (closed s t)
      then show ?case
        using frm.subsD(2)[OF frm.sub.cl_closed[OF generators_sub]] by blast
    qed
  qed
qed

lemma sub_cl_generators:
  assumes A0:"A \<subseteq> X"
  shows "frm.sub.cl \<langle>A\<rangle> = free_magma A"
proof
  have B0:"free_magma A \<in> frm.subs"
    using free_magma_mono[OF A0] by (intro frm.subsI) auto
  show "frm.sub.cl \<langle>A\<rangle> \<subseteq> free_magma A"
    by (rule frm.sub.cl_least[OF B0 generators_sub])
  show "free_magma A \<subseteq> frm.sub.cl \<langle>A\<rangle>"
  proof
    fix t assume "t \<in> free_magma A"
    then show "t \<in> frm.sub.cl \<langle>A\<rangle>"
    proof induction
      case (embeds x)
      then show ?case
        using frm.sub.cl_extensive[of "\<langle>A\<rangle>"] by (auto simp:generators_def)
    next
      case (closed s t)
      have "frm.sub.cl \<langle>A\<rangle> \<in> frm.subs"
        using generators_sub free_magma_mono[OF A0] by (intro frm.sub.cl_closed) blast
      then show ?case
        using closed.IH by (rule frm.subsD(2))
    qed
  qed
qed

lemma all_cancellable:"t \<in> free_magma X \<Longrightarrow> frm.cancellable t"
  by (rule frm.cancellableI1) simp_all

lemma aut_generators:
  assumes A0:"magma_iso (free_magma X) (\<star>) (free_magma X) (\<star>) \<phi>"
  shows "\<phi> ` \<langle>X\<rangle> = \<langle>X\<rangle>"
proof-
  interpret p:magma_iso "free_magma X" "(\<star>)" "free_magma X" "(\<star>)" \<phi>
    by (rule A0)
  have B0:"\<And>t. t \<in> free_magma X \<Longrightarrow> t \<in> \<langle>X\<rangle> \<longleftrightarrow> \<phi> t \<in> \<langle>X\<rangle>"
  proof-
    fix t assume C0:"t \<in> free_magma X"
    show "t \<in> \<langle>X\<rangle> \<longleftrightarrow> \<phi> t \<in> \<langle>X\<rangle>"
    proof
      assume C1:"t \<in> \<langle>X\<rangle>"
      show "\<phi> t \<in> \<langle>X\<rangle>"
      proof(rule ccontr)
        assume "\<phi> t \<notin> \<langle>X\<rangle>"
        then obtain s u where C2:"s \<in> free_magma X" and C3:"u \<in> free_magma X" and C4:"\<phi> t = s \<star> u"
          using generators_iff_irreducible[OF p.maps[OF C0]] by blast
        have "s \<in> \<phi> ` free_magma X" and "u \<in> \<phi> ` free_magma X"
          using C2 C3 by (simp_all add:p.surj)
        then obtain s' u' where C5:"s' \<in> free_magma X" and C6:"s = \<phi> s'" and C7:"u' \<in> free_magma X" and C8:"u = \<phi> u'"
          by blast
        have C9:"\<phi> t = \<phi> (s' \<star> u')"
          using C5 C7 by (simp add:C4 C6 C8 p.hom)
        have "t = s' \<star> u'"
          by (rule inj_onD[OF p.inj C9 C0]) (simp add:C5 C7)
        then show False
          using C1 by (auto simp:generators_def)
      qed
    next
      assume C1:"\<phi> t \<in> \<langle>X\<rangle>"
      show "t \<in> \<langle>X\<rangle>"
      proof(rule ccontr)
        assume "t \<notin> \<langle>X\<rangle>"
        then obtain s u where C2:"s \<in> free_magma X" and C3:"u \<in> free_magma X" and C4:"t = s \<star> u"
          using generators_iff_irreducible[OF C0] by blast
        have "\<phi> t = \<phi> s \<star> \<phi> u"
          using C2 C3 by (simp add:C4 p.hom)
        then show False
          using C1 by (auto simp:generators_def)
      qed
    qed
  qed
  show ?thesis
  proof
    show "\<phi> ` \<langle>X\<rangle> \<subseteq> \<langle>X\<rangle>"
      using B0 generators_sub by auto
    show "\<langle>X\<rangle> \<subseteq> \<phi> ` \<langle>X\<rangle>"
    proof
      fix g assume C0:"g \<in> \<langle>X\<rangle>"
      have "g \<in> \<phi> ` free_magma X"
        using C0 generators_sub by (auto simp:p.surj)
      then obtain t where C1:"t \<in> free_magma X" and C2:"g = \<phi> t"
        by blast
      have "t \<in> \<langle>X\<rangle>"
        using B0[OF C1] C0 by (simp add:C2)
      then show "g \<in> \<phi> ` \<langle>X\<rangle>"
        unfolding C2 by (rule imageI)
    qed
  qed
qed

theorem monogenous_cl:
  assumes A0:"x \<in> free_magma X" and A1:"y \<in> free_magma X"
  shows "frm.sub.cl {x} \<inter> frm.sub.cl {y} = {} \<or> frm.sub.cl {x} \<subseteq> frm.sub.cl {y} \<or> frm.sub.cl {y} \<subseteq> frm.sub.cl {x}"
proof(cases "frm.sub.cl {x} \<inter> frm.sub.cl {y} = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  have B0:"frm.sub.cl {x} = frm.gen {x}" and B1:"frm.sub.cl {y} = frm.gen {y}"
    using A0 A1 by (simp_all add:frm.gen_eq_cl)
  obtain w0 where "w0 \<in> frm.gen {x} \<inter> frm.gen {y}"
    using False by (auto simp:B0 B1)
  then obtain w where B2:"w \<in> frm.gen {x} \<inter> frm.gen {y}" and B3:"\<And>w'. w' \<in> frm.gen {x} \<inter> frm.gen {y} \<Longrightarrow> len w \<le> len w'"
    using ex_has_least_nat[of "\<lambda>w. w \<in> frm.gen {x} \<inter> frm.gen {y}" w0 len] by blast
  have B4:"w \<in> frm.gen {x}" and B5:"w \<in> frm.gen {y}"
    using B2 by simp_all
  have B6:"w = x \<or> w = y"
  proof(rule ccontr)
    assume C0:"\<not>(w = x \<or> w = y)"
    then have C1:"w \<notin> {x}" and C2:"w \<notin> {y}"
      by simp_all
    obtain a b where C3:"a \<in> frm.gen {x}" and C4:"b \<in> frm.gen {x}" and C5:"w = a \<star> b"
      using B4 C1 by (rule frm.genE)
    obtain a' b' where C6:"a' \<in> frm.gen {y}" and C7:"b' \<in> frm.gen {y}" and C8:"w = a' \<star> b'"
      using B5 C2 by (rule frm.genE)
    have C9:"a = a'"
      using C5 C8 by simp
    have "a \<in> frm.gen {x} \<inter> frm.gen {y}"
      using C3 C6 by (simp add:C9)
    then have "len w \<le> len a"
      by (rule B3)
    moreover have "len a < len w"
      using len_gt_0 by (simp add:C5)
    ultimately show False
      by simp
  qed
  show ?thesis
  proof(cases "w = x")
    case True
    then have "x \<in> frm.sub.cl {y}"
      using B5 by (simp add:B1)
    then have "frm.sub.cl {x} \<subseteq> frm.sub.cl {y}"
      using A1 by (intro frm.sub.cl_least[OF frm.sub.cl_closed]) simp_all
    then show ?thesis
      by simp
  next
    case False
    then have "y \<in> frm.sub.cl {x}"
      using B4 B6 by (simp add:B0)
    then have "frm.sub.cl {y} \<subseteq> frm.sub.cl {x}"
      using A0 by (intro frm.sub.cl_least[OF frm.sub.cl_closed]) simp_all
    then show ?thesis
      by simp
  qed
qed

end

subsection \<open>The universal property\<close>

fun ext0::"('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a frm \<Rightarrow> 'b"
  where "ext0 mul f (\<eta> x) = f x"
      | "ext0 mul f (s \<star> t) = mul (ext0 mul f s) (ext0 mul f t)"

locale free_magma_ext = dom:free_magma_locale X + cod:magma Y mul
  for X::"'a set" and Y::"'b set" and mul::"'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<cdot>" 70) and f::"'a \<Rightarrow> 'b" +
  assumes maps:"x \<in> X \<Longrightarrow> f x \<in> Y"
begin

abbreviation extend::"'a frm \<Rightarrow> 'b" ("M'(f')")
  where "M(f) \<equiv> (\<lambda>t\<in>free_magma X. ext0 (\<cdot>) f t)"

lemma extend_eta:"x \<in> X \<Longrightarrow> M(f) (\<eta> x) = f x"
  by simp

lemma extend_op:"\<lbrakk>s \<in> free_magma X; t \<in> free_magma X\<rbrakk> \<Longrightarrow> M(f) (s \<star> t) = M(f) s \<cdot> M(f) t"
  by simp

lemma ext0_maps:"t \<in> free_magma X \<Longrightarrow> ext0 (\<cdot>) f t \<in> Y"
proof-
  assume "t \<in> free_magma X"
  then show "ext0 (\<cdot>) f t \<in> Y"
  proof induction
    case (embeds x)
    then show ?case
      by (simp add:maps)
  next
    case (closed s t)
    then show ?case
      by simp
  qed
qed

lemma extend_maps:"t \<in> free_magma X \<Longrightarrow> M(f) t \<in> Y"
  by (simp add:ext0_maps)

lemma extend_hom:"magma_hom (free_magma X) (\<star>) Y (\<cdot>) M(f)"
  by (intro magma_hom.intro magma_hom_axioms.intro dom.frm.magma_axioms cod.magma_axioms) (simp_all add:ext0_maps)

lemma extend_unique:
  assumes A0:"magma_hom (free_magma X) (\<star>) Y (\<cdot>) g" and A1:"\<And>x. x \<in> X \<Longrightarrow> g (\<eta> x) = f x" and A2:"t \<in> free_magma X"
  shows "g t = M(f) t"
  using A2
proof induction
  case (embeds x)
  then show ?case
    by (simp add:A1)
next
  case (closed s t)
  then show ?case
    by (simp add:magma_hom.hom[OF A0])
qed

lemma extend_image:"M(f) ` free_magma X = cod.sub.cl (f ` X)"
proof-
  interpret h:magma_hom "free_magma X" "(\<star>)" Y "(\<cdot>)" "M(f)"
    by (rule extend_hom)
  have B0:"M(f) ` \<langle>X\<rangle> = f ` X"
  proof
    show "M(f) ` \<langle>X\<rangle> \<subseteq> f ` X"
    proof
      fix y assume "y \<in> M(f) ` \<langle>X\<rangle>"
      then obtain x where C0:"x \<in> X" and C1:"y = M(f) (\<eta> x)"
        by (auto simp:generators_def)
      have "y = f x"
        using C0 by (simp add:C1)
      then show "y \<in> f ` X"
        using C0 by (simp add:imageI)
    qed
    show "f ` X \<subseteq> M(f) ` \<langle>X\<rangle>"
    proof
      fix y assume "y \<in> f ` X"
      then obtain x where C0:"x \<in> X" and C1:"y = f x"
        by blast
      have "y = M(f) (\<eta> x)"
        using C0 by (simp add:C1)
      then show "y \<in> M(f) ` \<langle>X\<rangle>"
        using generators_memI[OF C0] by (rule image_eqI)
    qed
  qed
  have "M(f) ` free_magma X = M(f) ` dom.frm.sub.cl \<langle>X\<rangle>"
    by (simp add:dom.generators_cl)
  also have "\<dots> = cod.sub.cl (M(f) ` \<langle>X\<rangle>)"
    by (rule h.image_cl[OF generators_sub])
  finally have "M(f) ` free_magma X = cod.sub.cl (M(f) ` \<langle>X\<rangle>)" .
  then show ?thesis
    unfolding B0 .
qed

end

theorem (in free_magma_locale) universal_property:
  assumes A0:"magma Y mul" and A1:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y"
  shows "\<exists>!g. g \<in> maps_on (free_magma X) \<and> magma_hom (free_magma X) (\<star>) Y mul g \<and> (\<forall>x\<in>X. g (\<eta> x) = f x)"
proof-
  interpret e:free_magma_ext X Y mul f
    by (simp add:free_magma_ext_def free_magma_ext_axioms_def A0 A1)
  show ?thesis
  proof(rule ex1I[where a = "e.extend"])
    show "e.extend \<in> maps_on (free_magma X) \<and> magma_hom (free_magma X) (\<star>) Y mul e.extend \<and> (\<forall>x\<in>X. e.extend (\<eta> x) = f x)"
      using e.extend_hom by simp
    fix g assume B0:"g \<in> maps_on (free_magma X) \<and> magma_hom (free_magma X) (\<star>) Y mul g \<and> (\<forall>x\<in>X. g (\<eta> x) = f x)"
    show "g = e.extend"
    proof(rule maps_on_eqI1[of _ "free_magma X"])
      show "g \<in> maps_on (free_magma X)" and "e.extend \<in> maps_on (free_magma X)"
        using B0 by simp_all
      show "\<And>t. t \<in> free_magma X \<Longrightarrow> g t = e.extend t"
        using B0 by (intro e.extend_unique) simp_all
    qed
  qed
qed

subsection \<open>Functoriality\<close>

locale free_magma_funct = dom:free_magma_locale X + cod:free_magma_locale Y
  for X::"'a set" and Y::"'b set" and f::"'a \<Rightarrow> 'b" +
  assumes maps:"x \<in> X \<Longrightarrow> f x \<in> Y"
begin

sublocale ext:free_magma_ext X "free_magma Y" "(\<star>)" "\<eta> \<circ> f"
  by (simp add:free_magma_ext_def free_magma_ext_axioms_def cod.frm.magma_axioms maps)

abbreviation lift::"'a frm \<Rightarrow> 'b frm" ("M'[f']")
  where "M[f] \<equiv> (\<lambda>t\<in>free_magma X. map_frm f t)"

lemma map_frm_ext0:"map_frm f t = ext0 (\<star>) (\<eta> \<circ> f) t"
  by (induction t) simp_all

lemma lift_eq_extend:"M[f] = ext.extend"
  by (simp add:map_frm_ext0)

lemma lift_eta:"x \<in> X \<Longrightarrow> M[f] (\<eta> x) = \<eta> (f x)"
  by simp

lemma lift_maps:"t \<in> free_magma X \<Longrightarrow> M[f] t \<in> free_magma Y"
  using maps by (auto simp:free_magma_iff frm.set_map)

lemma lift_hom:"magma_hom (free_magma X) (\<star>) (free_magma Y) (\<star>) M[f]"
  using ext.extend_hom by (simp add:lift_eq_extend)

lemma lift_inj:
  assumes A0:"inj_on f X"
  shows "inj_on M[f] (free_magma X)"
proof(rule inj_onI)
  fix s u assume B0:"s \<in> free_magma X" and B1:"u \<in> free_magma X" and B2:"M[f] s = M[f] u"
  have "map_frm f s = map_frm f u"
    using B0 B1 B2 by simp
  then show "s = u"
    using B0 B1
  proof(induction s arbitrary:u)
    case (Em x)
    then show ?case
      by (cases u) (auto simp:free_magma_iff inj_onD[OF A0])
  next
    case (Op s1 s2)
    then show ?case
      by (cases u) (auto simp:free_magma_iff)
  qed
qed

lemma lift_surj:
  assumes A0:"f ` X = Y"
  shows "M[f] ` free_magma X = free_magma Y"
proof
  show "M[f] ` free_magma X \<subseteq> free_magma Y"
    using lift_maps by auto
  show "free_magma Y \<subseteq> M[f] ` free_magma X"
  proof
    fix t assume "t \<in> free_magma Y"
    then show "t \<in> M[f] ` free_magma X"
    proof induction
      case (embeds y)
      then obtain x where B0:"x \<in> X" and B1:"y = f x"
        using A0 by blast
      have "\<eta> y = M[f] (\<eta> x)"
        using B0 by (simp add:B1)
      then show ?case
        using free_magma.embeds[OF B0] by (rule image_eqI)
    next
      case (closed s u)
      then obtain s' u' where B0:"s' \<in> free_magma X" and B1:"s = M[f] s'" and B2:"u' \<in> free_magma X" and B3:"u = M[f] u'"
        by blast
      have "s \<star> u = M[f] (s' \<star> u')"
        using B0 B2 by (simp add:B1 B3)
      then show ?case
        using free_magma.closed[OF B0 B2] by (rule image_eqI)
    qed
  qed
qed

lemma lift_bij:
  assumes A0:"bij_betw f X Y"
  shows "bij_betw M[f] (free_magma X) (free_magma Y)"
  using lift_inj[OF bij_betw_imp_inj_on[OF A0]] lift_surj[OF bij_betw_imp_surj_on[OF A0]] by (rule bij_betw_imageI)

lemma lift_iso:
  assumes A0:"bij_betw f X Y"
  shows "magma_iso (free_magma X) (\<star>) (free_magma Y) (\<star>) M[f]"
  by (intro magma_iso.intro magma_iso_axioms.intro lift_hom lift_bij[OF A0])

end

lemma lift_id:"(\<lambda>t\<in>free_magma X. map_frm id t) = (\<lambda>t\<in>free_magma X. t)"
  by (rule restrict_ext) (simp add:frm.map_id frm.map_id0)

lemma lift_comp:
  assumes A0:"f ` X \<subseteq> Y"
  shows "compose (free_magma X) (\<lambda>t\<in>free_magma Y. map_frm g t) (\<lambda>t\<in>free_magma X. map_frm f t) = (\<lambda>t\<in>free_magma X. map_frm (g \<circ> f) t)"
  unfolding compose_def
proof(rule restrict_ext)
  fix t assume B0:"t \<in> free_magma X"
  have "map_frm f t \<in> free_magma Y"
    using A0 B0 by (auto simp:free_magma_iff frm.set_map)
  then show "(\<lambda>t\<in>free_magma Y. map_frm g t) ((\<lambda>t\<in>free_magma X. map_frm f t) t) = map_frm (g \<circ> f) t"
    using B0 by (simp add:frm.map_comp)
qed

subsection \<open>Submagmas of free magmas are free\<close>

context free_magma_locale
begin

theorem free_submagma:
  assumes A0:"N \<in> frm.subs"
  shows "magma_iso (free_magma (N - frm.set_prod N N)) (\<star>) N (\<star>) (\<lambda>t\<in>free_magma (N - frm.set_prod N N). ext0 (\<star>) (\<lambda>a. a) t)"
proof-
  define B where "B = N - frm.set_prod N N"
  have N0:"N \<subseteq> free_magma X" and N1:"\<And>a b. \<lbrakk>a \<in> N; b \<in> N\<rbrakk> \<Longrightarrow> a \<star> b \<in> N"
    using frm.subsD[OF A0] by auto
  have B0:"B \<subseteq> N" and B1:"\<And>a b. \<lbrakk>a \<in> N; b \<in> N\<rbrakk> \<Longrightarrow> a \<star> b \<notin> B"
    by (auto simp:B_def frm.set_prod_def)
  have B2:"\<And>n. \<lbrakk>n \<in> N; n \<notin> B\<rbrakk> \<Longrightarrow> \<exists>a\<in>N. \<exists>b\<in>N. n = a \<star> b"
    by (auto simp:B_def frm.set_prod_def)
  interpret e:free_magma_ext B N "(\<star>)" "\<lambda>a. a"
    using B0 by (auto simp:free_magma_ext_def free_magma_ext_axioms_def frm.sub_magma[OF A0])
  have E0:"\<And>t. t \<in> free_magma B \<Longrightarrow> e.extend t \<in> N"
    by (rule e.extend_maps)
  have surj:"\<And>k n. \<lbrakk>len n = k; n \<in> N\<rbrakk> \<Longrightarrow> n \<in> e.extend ` free_magma B"
  proof-
    fix k
    show "\<And>n. \<lbrakk>len n = k; n \<in> N\<rbrakk> \<Longrightarrow> n \<in> e.extend ` free_magma B"
    proof(induction k rule:less_induct)
      case (less k)
      fix n assume C0:"len n = k" and C1:"n \<in> N"
      show "n \<in> e.extend ` free_magma B"
      proof(cases "n \<in> B")
        case True
        show ?thesis
          by (rule rev_image_eqI[of "\<eta> n"]) (simp_all add:True)
      next
        case False
        obtain a b where C2:"a \<in> N" and C3:"b \<in> N" and C4:"n = a \<star> b"
          using B2[OF C1 False] by blast
        have C5:"len a < k" and C6:"len b < k"
          using C0 len_gt_0[of a] len_gt_0[of b] by (simp_all add:C4)
        obtain s where C7:"s \<in> free_magma B" and C8:"a = e.extend s"
          using less.IH[OF C5 refl C2] by blast
        obtain u where C9:"u \<in> free_magma B" and C10:"b = e.extend u"
          using less.IH[OF C6 refl C3] by blast
        have "n = e.extend (s \<star> u)"
          using C7 C9 by (simp add:C4 C8 C10)
        then show ?thesis
          using free_magma.closed[OF C7 C9] by (rule image_eqI)
      qed
    qed
  qed
  have inj:"inj_on e.extend (free_magma B)"
  proof(rule inj_onI)
    fix s u assume "s \<in> free_magma B" and "u \<in> free_magma B" and "e.extend s = e.extend u"
    then show "s = u"
    proof(induction s arbitrary:u)
      case (embeds b)
      show ?case
      proof(cases u)
        case (Em b')
        have "b' \<in> B"
          using embeds.prems(1) by (simp add:Em free_magma_iff)
        then show ?thesis
          using embeds.hyps embeds.prems(2) by (simp add:Em)
      next
        case (Op u1 u2)
        have C0:"u1 \<in> free_magma B" and C1:"u2 \<in> free_magma B"
          using embeds.prems(1) by (simp_all add:Op free_magma_iff)
        have "b = e.extend u1 \<star> e.extend u2"
          using embeds.hyps embeds.prems(2) C0 C1 by (simp add:Op)
        then have "b \<notin> B"
          using B1[OF E0[OF C0] E0[OF C1]] by simp
        then show ?thesis
          using embeds.hyps by simp
      qed
    next
      case (closed s1 s2)
      show ?case
      proof(cases u)
        case (Em b')
        have C0:"b' \<in> B"
          using closed.prems(1) by (simp add:Em free_magma_iff)
        have "b' = e.extend s1 \<star> e.extend s2"
          using closed.hyps closed.prems(2) C0 by (simp add:Em)
        then show ?thesis
          using B1[OF E0[OF closed.hyps(1)] E0[OF closed.hyps(2)]] C0 by simp
      next
        case (Op u1 u2)
        have C0:"u1 \<in> free_magma B" and C1:"u2 \<in> free_magma B"
          using closed.prems(1) by (simp_all add:Op free_magma_iff)
        have "e.extend s1 = e.extend u1" and "e.extend s2 = e.extend u2"
          using closed.hyps closed.prems(2) C0 C1 by (simp_all add:Op)
        then show ?thesis
          using closed.IH C0 C1 by (simp add:Op)
      qed
    qed
  qed
  have "bij_betw e.extend (free_magma B) N"
  proof(rule bij_betw_imageI[OF inj])
    show "e.extend ` free_magma B = N"
      using E0 surj[OF refl] by blast
  qed
  then show ?thesis
    unfolding B_def[symmetric] by (intro magma_iso.intro magma_iso_axioms.intro e.extend_hom)
qed

end

end
