theory Algebrah1738
  imports Posets9
begin

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


context group
begin

definition inv :: "'a \<Rightarrow> 'a"
  where "inv x = (THE y. y \<in> X \<and> y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>)"

lemma inv_unique:
  assumes x: "x \<in> X" and y: "y \<in> X" "y \<cdot> x = \<one>" and z: "z \<in> X" "x \<cdot> z = \<one>"
  shows "y = z"
proof -
  have "y = y \<cdot> (x \<cdot> z)" using y(1) z(2) by simp
  also have "\<dots> = (y \<cdot> x) \<cdot> z" using x y(1) z(1) by (simp add: assoc)
  also have "\<dots> = z" using y(2) z(1) by simp
  finally show ?thesis .
qed

lemma inv_props:
  assumes x: "x \<in> X"
  shows inv_closed [simp, intro]: "inv x \<in> X" and inv_left [simp]: "inv x \<cdot> x = \<one>"
    and inv_right [simp]: "x \<cdot> inv x = \<one>"
proof -
  obtain y where y: "y \<in> X" "y \<cdot> x = \<one>" "x \<cdot> y = \<one>" using inverse_ex[OF x] by blast
  have "inv x = y"
    unfolding inv_def
  proof (rule the_equality)
    show "y \<in> X \<and> y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>" using y by simp
    fix z assume z: "z \<in> X \<and> z \<cdot> x = \<one> \<and> x \<cdot> z = \<one>"
    show "z = y" by (rule inv_unique[OF x]) (simp_all add: z y)
  qed
  then show "inv x \<in> X" "inv x \<cdot> x = \<one>" "x \<cdot> inv x = \<one>" using y by simp_all
qed

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

end
