theory deez11
  imports Main 
begin
declare [[show_consts, show_results, show_types=true]]
declare [[show_abbrevs=true, trace_locales=true]]

section \<open>Magmas\<close>

definition magma_stable :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "magma_stable X f A \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A. f x y \<in> A) \<and> (A \<subseteq> X)"

lemma magma_stableI :"\<lbrakk>A \<subseteq> X; (\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> f x y \<in> A)\<rbrakk> \<Longrightarrow> magma_stable X f A" 
  by (simp add: magma_stable_def)

lemma magma_stableE1:"magma_stable X f A \<Longrightarrow> A \<subseteq> X" 
  by (simp add: magma_stable_def)

lemma magma_stableE2:"magma_stable X f A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x y \<in> A"
  by (simp add:magma_stable_def)

lemma magma_stable_int_closed:"\<lbrakk>(\<And>A. A \<in> \<A> \<Longrightarrow> magma_stable X f A) ;\<A> \<noteq> {}\<rbrakk> \<Longrightarrow> magma_stable X f (\<Inter>\<A>)"
  unfolding magma_stable_def by(blast)

inductive_set generated_magma::"('a\<Rightarrow> 'a \<Rightarrow> 'a ) \<Rightarrow> 'a set \<Rightarrow> 'a set" for f A where
    iso[intro, simp]:"a \<in> A \<Longrightarrow> a \<in> generated_magma f A" |
    opc[intro, simp]:"\<lbrakk>a \<in> generated_magma f A; b \<in> generated_magma f A\<rbrakk> \<Longrightarrow> f a b \<in> generated_magma f A"


section \<open>Magma Locale\<close>

locale magma=
  fixes X::"'a set" and law::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70) 
  assumes closed[intro, simp]:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> X" 
begin

abbreviation gen where "gen \<equiv> generated_magma law"

lemma generate_into: "a \<in> gen (X \<inter> A) \<Longrightarrow> a \<in> X"  
  by (induction rule: generated_magma.induct, simp+) 

lemma iso2:"A \<subseteq>gen A"
  by (simp add: subset_eq)


lemma generated_iso1:
  assumes A0:"(\<And>x. x \<in> A \<Longrightarrow> x \<in> B)" and A1:"x \<in> gen A "
  shows "x \<in> gen B"
  using A1 A0 by(induct x, simp_all)

lemma generated_iso2:"A \<subseteq> B \<Longrightarrow> gen A \<subseteq> gen B"
  by (meson generated_iso1 subset_eq)
  
lemma generated_least1:
  assumes A0:"\<And>x. x \<in> A \<Longrightarrow> x \<in> B" and A1:"\<And>a b. \<lbrakk>a \<in> B; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot>b \<in> B"
  shows "\<And>x. x \<in> gen A \<Longrightarrow> x \<in> B"
  by(erule generated_magma.induct,auto simp add:A0 A1)

lemma generated_least2:
  assumes A0:"\<And>x. x \<in> A \<Longrightarrow> x \<in> B" and A1:"\<And>a b. \<lbrakk>a \<in> B; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot>b \<in> B" and
            A2:"x  \<in> gen A"
  shows "x \<in> B"
  using A0 A1 A2 generated_least1 by blast

lemma generated_least3:
  assumes A0:"A \<subseteq> B" and A1:"\<And>a b. \<lbrakk>a \<in> B; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot>b \<in> B"
  shows " gen A \<subseteq> B"
  apply(rule subsetI)
  using A0 A1 generated_least2[of A B] by blast

definition cl :: "'a set \<Rightarrow> 'a set"  where 
  "cl S = gen (X \<inter> S)"

lemma cl_magma_sub:"cl H \<subseteq> X" 
  using cl_def generate_into by auto

lemma cl_stable:" magma_stable X law (cl H)"
  using cl_def cl_magma_sub magma_stable_def by fastforce


lemma cl_magma_iso:"A \<subseteq> B \<Longrightarrow> cl A \<subseteq> cl B" unfolding cl_def
  by (simp add: generated_iso2 inf.coboundedI2)


lemma cl_magma_extensive:"A \<subseteq> X \<Longrightarrow> A \<subseteq> cl A"
  by (simp add: Int_absorb1 cl_def iso2)  


lemma cl_magma_stable_ub:"\<lbrakk>A \<subseteq> B; magma_stable X law B\<rbrakk> \<Longrightarrow> cl A \<subseteq> B"
  by (simp add: cl_def generated_least3 le_infI2 magma_stableE2) 

lemma cl_magma_stable_ub2:"\<lbrakk>A \<subseteq> B; (\<And>a b. \<lbrakk>a \<in> B; b \<in> B\<rbrakk> \<Longrightarrow> a \<cdot>b \<in> B)\<rbrakk>  \<Longrightarrow> cl A \<subseteq> B"
  by (simp add: generated_least3 inf.coboundedI2 magma.cl_def magma_axioms)

lemma cl_idemp:"A \<subseteq> X \<Longrightarrow> cl A = cl (cl A)"
  by (simp add: cl_magma_extensive cl_magma_stable_ub cl_magma_sub cl_stable subset_antisym)
 
lemma cl_magma_moore0:
  assumes A0:"A \<subseteq> X" 
  shows "cl A = \<Inter>{C. magma_stable X law C \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    by (simp add: le_Inf_iff magma.cl_magma_stable_ub magma_axioms)
next
  show "?RHS \<subseteq> ?LHS"
    by (simp add: Inter_lower assms cl_magma_extensive cl_stable)
qed

lemma magma_cl_induct:
  assumes A0:"A \<subseteq> X" and
          A1:"a \<in> cl A" and
          A2:"\<And>x. x \<in> A \<Longrightarrow> P x" and
          A3:"\<And>x y. \<lbrakk>x \<in> cl A; P x; y \<in> cl A; P y\<rbrakk> \<Longrightarrow> P (x \<cdot> y)"
        shows "P a"
  using A1 A2 A3  unfolding cl_def
proof(induct rule: generated_magma.induct)
  case (iso a)
  then show ?case
    by blast 
next
  case (opc a b)
  then show ?case
    by blast 
qed

lemma cl_sub_eq:"A \<subseteq> X \<Longrightarrow> cl A = gen A"
  by (simp add: cl_def inf.absorb_iff2)

lemma cl_cases:
  assumes A0:"A \<subseteq> X" and 
          A1:"a \<in> gen A" and
         A2:"(\<And>x. a = x \<Longrightarrow> x \<in> A \<Longrightarrow> P)" and 
         A3:"(\<And>x y. a = x \<cdot> y \<Longrightarrow> x \<in> cl A \<Longrightarrow> y \<in> cl A \<Longrightarrow> P)"
       shows P
proof-
  have B0:"(\<And>x y. a = x \<cdot> y \<Longrightarrow> x \<in> gen A \<Longrightarrow> y \<in> gen A \<Longrightarrow> P)"
    using A0 A3 cl_sub_eq by blast
  show ?thesis using A0 A1 A2 B0  generated_magma.cases[of a law A] by blast
qed
    
    

lemma magma_cl_cases:
  assumes A0:"A \<subseteq> X" and A1:"x \<in> cl A"
  obtains "x \<in> A" | "\<exists>a\<in> cl A. \<exists>b \<in> cl A. x = a \<cdot> b" 
proof-
  have B0:"x \<in> gen A"
    using A0 A1 cl_sub_eq by auto
  show ?thesis
    using A0 B0 cl_cases[of A x] that(1,2) by metis
qed

lemma magma_cl_non_gen: 
  assumes A0:"A \<subseteq> X" and A1:"x \<in> cl A" and A2:"x \<notin> A"
  obtains a b where "a \<in> cl A" and "b \<in> cl A" and "x = a \<cdot> b"
  using A0 A1 A2 magma_cl_cases[of A x] using that by auto

end


lemma magma_int:"\<lbrakk>(\<And>A. A \<in> \<A> \<Longrightarrow> magma A f);\<A> \<noteq> {} \<rbrakk> \<Longrightarrow> magma (\<Inter>\<A>) f"
  by (simp add: magma_def)

lemma magma_bint:"magma A f \<Longrightarrow> magma B f \<Longrightarrow> magma (A \<inter> B) f"
  by (simp add: magma_def)



section \<open>Submagma Locale\<close>
locale submagma=magma X "(\<cdot>)" for A and X and magma_law (infixl "\<cdot>" 70)+
  assumes submem[intro, simp]:"A \<subseteq> X" and 
          subfun[intro]:"\<lbrakk>x \<in>A; y \<in> A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> A" 
begin
lemma sub[intro,simp]:"x \<in> A \<Longrightarrow> x \<in> X"  using submem by blast 

sublocale sub:magma A "(\<cdot>)" by (simp add: subfun magma.intro)
lemma stable:"magma_stable X (\<cdot>) A" using magma_stable_def by blast

lemma cl_submgama: "submagma (cl H) X (\<cdot>)" 
  apply(rule submagma.intro)
  apply (simp_all add: magma_axioms submagma_axioms.intro)
  apply(rule submagma_axioms.intro)
  apply(rule cl_magma_sub)
  by (simp add: cl_def)

lemma cl_magma_ub:
  assumes A0:"A \<subseteq> B" and A1:"submagma B X (\<cdot>)"  shows "cl A \<subseteq> B"
  using A0 A1 cl_magma_stable_ub[of A B] submagma.stable[of B X ] by blast

lemma cl_magma_ub2:  "A \<subseteq> B \<Longrightarrow> (B \<subseteq> X) \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> B; y \<in> B\<rbrakk> \<Longrightarrow>  x \<cdot> y \<in> B) \<Longrightarrow>cl A \<subseteq> B" by (simp add: cl_magma_stable_ub2)

lemma cl_magma_moore1:
  assumes A0:"A \<subseteq> X"   shows "cl A = \<Inter>{C. submagma C X (\<cdot>) \<and> A \<subseteq> C}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
    using cl_magma_ub by auto
next
  show "?RHS \<subseteq> ?LHS"
    by (simp add: Inter_lower cl_magma_extensive cl_submgama)
qed


end



lemma submagma_trans[trans]: 
  assumes "submagma A B f" and 
          "submagma B C f" 
  shows   "submagma A C f" 
proof-
  interpret A: submagma A B f
    by fact 
  interpret C: submagma B C f 
    by fact 
  show ?thesis 
    by (simp add:  C.magma_axioms submagma.intro submagma_axioms_def subset_iff) 
qed

lemma submagmaI:"magma X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (f x y) \<in> A) \<Longrightarrow> submagma A X f" 
  by (simp add: submagma.intro submagma_axioms.intro subsetD)


section \<open>Magma Homomorphism Locale\<close>


definition comm::"('a  \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b set  \<Rightarrow> ('b \<Rightarrow>'b \<Rightarrow>'b)  \<Rightarrow> bool" where
  "comm f X law1 Y law2 \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. f(law1 x y) = law2 (f x) (f y))"

lemma magma_homE:"comm f X law1 Y law2 \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> f(law1 x y) = law2 (f x) (f y)"
  by (simp add: comm_def)

lemma commI:"(\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f(law1 x y) = law2 (f x) (f y)) \<Longrightarrow> comm f X law1 Y law2"
  by (simp add: comm_def)



locale magma_homomorphism=dom:magma X "(\<cdot>)" + cod:magma Y "(\<star>)" 
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70) +
  assumes cmp:"comm f X (\<cdot>) Y (\<star>)" and
          cod[intro,simp]:"x \<in> X \<Longrightarrow> f x \<in> Y"
begin

lemma comE:"\<lbrakk>x \<in>X;x'\<in>X\<rbrakk> \<Longrightarrow> f (x\<cdot>x') = (f x)\<star>(f x')" 
  using cmp magma_homE[of f X domain_law Y codomain_law x x'] by blast

lemma into:"f`X \<subseteq> Y" by blast

lemma imag_comp:"submagma A X (\<cdot>) \<Longrightarrow> x \<in> f ` A \<Longrightarrow> y \<in> f ` A \<Longrightarrow> x \<star> y \<in> f ` A"
proof-
  fix x y assume A0:"submagma A X (\<cdot>)" "x \<in> f ` A" "y \<in> f `A" then obtain a b where A1:"a \<in> A" "b \<in> A" "x = f a" "y = f b"  by blast
  then obtain "a\<cdot>b \<in> A" by (meson A0 submagma.subfun) 
  then obtain "f (a \<cdot>b) \<in> f `A" and  "f (a \<cdot> b) = (f a)\<star>(f b)"
    by (meson A0(1) A1(1,2) comE imageI submagma.sub)
  then show "x \<star> y \<in> f ` A"  by (simp add: A1(3) A1(4)) 
qed

lemma imag_compb:"submagma A X (\<cdot>) \<Longrightarrow> (f a) \<in> f ` A \<Longrightarrow> (f a') \<in> f ` A \<Longrightarrow> (f a) \<star> (f a') \<in> f ` A"
  using imag_comp by blast

lemma imag_comp2:"magma_stable X (\<cdot>) A \<Longrightarrow> x \<in> f ` A \<Longrightarrow> y \<in> f ` A \<Longrightarrow> x \<star> y \<in> f ` A"
proof-
  fix x y assume A0:"magma_stable X (\<cdot>) A" and A1:"x \<in> f ` A" and A2:"y \<in> f `A" 
  then obtain a b where A3:"a \<in> A" and  A4:"b \<in> A" and A5:"x = f a" and A6:"y = f b"
    by blast
  obtain A7:"A \<subseteq> X" 
    using A0 unfolding magma_stable_def by auto
  then obtain A8:"y \<in> Y" and A9:"x \<in> Y" and A10:"a \<in> X" and A11:"b \<in> X"
    using A3 A4 A5 A6 by blast
  obtain A12:"a\<cdot>b \<in> A" and A13:"a \<cdot> b \<in> X"
    using A0 A3 A4 unfolding magma_stable_def by auto
  then obtain A14:"f (a \<cdot>b) \<in> f `A" and A15: "f (a \<cdot> b) = (f a)\<star>(f b)"
    using A10 A11 cmp magma_homE by fastforce
  then show "x \<star> y \<in> f ` A"
    using A5 A6 by auto 
qed

lemma stable_image:
  assumes A0:"magma_stable X (\<cdot>) A"
  shows "magma_stable Y (\<star>) (f`A)"
proof-
  have B0:"f`A \<subseteq> Y"  
    using assms magma_stable_def by fastforce
  have B1:"\<And>x y. x \<in> f ` A \<Longrightarrow> y \<in> f ` A \<Longrightarrow> x \<star> y \<in> f ` A"
    using assms imag_comp2 by blast
  show ?thesis 
    using magma_stableI B0 B1 by auto
qed


lemma magma_stable_vimage:"magma_stable Y (\<star>) B \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow>magma_stable X (\<cdot>) (vimage f B)" 
proof-
  assume A0:"magma_stable Y (\<star>) B " and A1:" (vimage f B) \<subseteq> X"
  show "magma_stable X (\<cdot>) (vimage f B)"
  proof(rule magma_stableI)
    show "(vimage f B) \<subseteq> X"
      by (simp add: A1)
    show "\<And>x y. \<lbrakk>x \<in> (vimage f B);y \<in> (vimage f B)\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> (vimage f B)"
    proof-
      fix x y assume A2:"x \<in> vimage f B" and A3:"y \<in> vimage f B"
      then obtain B0:"f x \<in> B" and B1:"f y \<in> B" and  B2:"x \<in> X" and B3:"y \<in> X"
        using A1 by blast
      then obtain "(f x) \<star> (f y) \<in> B" and "f(x \<cdot>  y) = (f x) \<star> (f y)"
        by (meson A0 cmp magma_homE magma_stableE2)
      then show " x \<cdot> y \<in> (vimage f B)" by simp
    qed
  qed
qed


lemma submagma1:"submagma A X (\<cdot>) \<Longrightarrow> submagma (f`A) Y (\<star>)" 
  by(unfold_locales;simp add: image_subsetI submagma.sub;simp add:imag_comp)

lemma submagma12:"submagma B Y (\<star>) \<Longrightarrow> (vimage f B) \<subseteq> X \<Longrightarrow>submagma (vimage f B) X (\<cdot>)" 
proof-
  assume A0:"submagma B Y (\<star>)" and A1:"(vimage f B) \<subseteq> X"
  show "submagma (vimage f B) X (\<cdot>)"
  proof(unfold_locales, auto)
    show P0:"\<And>x. f x \<in> B \<Longrightarrow> x \<in> X"
      using A1 by auto
    show "\<And>x y. f x \<in> B \<Longrightarrow> f y \<in> B \<Longrightarrow> f (x \<cdot> y) \<in> B"
    proof-
      fix x y assume A2:"f x \<in> B" and A3:"f y \<in> B"
      then obtain "(f x) \<star> (f y) \<in> B" and " f (x \<cdot> y) = (f x) \<star> (f y)"
        by (meson A0 P0 cmp magma_homE submagma.subfun)
      then show " f (x \<cdot> y) \<in> B" by simp
    qed
  qed
qed

end
lemma magma_homI:"\<lbrakk>comm f X l1 Y l2; (\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y); magma X l1; magma Y l2\<rbrakk> \<Longrightarrow> magma_homomorphism f X l1 Y l2"
  by (simp add: magma_homomorphism_axioms_def magma_homomorphism_def)


section \<open>Magma Isomorphism\<close> 


locale magma_isomorphism=hom:magma_homomorphism f X"(\<cdot>)" Y "(\<star>)"
  for f and X and domain_law (infixl "\<cdot>" 70) and Y and codomain_law (infixl "\<star>" 70)+
  assumes bij:"bij_betw f X Y"
begin

definition f_inv where "f_inv = inv_into X f"

lemma inv_bij:"bij_betw f_inv Y X"
  by (simp add: bij bij_betw_inv_into f_inv_def)

lemma inv_hom:"comm f_inv Y(\<star>) X (\<cdot>)"
proof(rule commI)
  fix y y' assume A0:"y \<in> Y" and A1:"y' \<in> Y" 
  have "f_inv (y \<star> y') = f_inv ( ( f ( f_inv y ) ) \<star> ( f ( f_inv y' ) ) )"
    using A0 A1 bij bij_betw_inv_into_right f_inv_def by fastforce
  also have "... = f_inv ( f ((f_inv y)\<cdot> f_inv y'))"
    using A0 A1 bij_betw_apply hom.cmp inv_bij magma_homE by fastforce
  also have "... = (f_inv y) \<cdot> (f_inv y')"
    by (metis A0 A1 bij bij_betw_imp_surj_on bij_betw_inv_into_left f_inv_def hom.dom.closed inv_into_into)
  finally show "f_inv (y\<star>y') = (f_inv y)\<cdot>(f_inv y')"
    by auto
qed

sublocale f_inv_iso:magma_homomorphism f_inv Y "(\<star>)" X "(\<cdot>)"
  apply(unfold_locales)
  apply (simp add: inv_hom)
  using bij_betwE inv_bij by auto


end

lemma magma_iso_intro:"bij_betw f X Y \<Longrightarrow> magma X xlaw \<Longrightarrow> magma Y ylaw \<Longrightarrow> comm f X xlaw Y ylaw \<Longrightarrow> magma_isomorphism f X xlaw Y ylaw"
  by (simp add: bij_betw_apply magma_homomorphism_axioms.intro magma_homomorphism_def magma_isomorphism_axioms.intro
      magma_isomorphism_def)

section \<open>Free Bobby Shmurda\<close>

datatype 'a frm = 
      Em 'a ("\<eta>")
    | Op "'a frm" "'a frm" (infixl "\<star>" 65)

inductive_set free_magma::"'a set \<Rightarrow> 'a frm set" for X::"'a set"  where
  embeds[intro!, simp]:"x \<in> X \<Longrightarrow> \<eta> x \<in>  free_magma X" |
  stable[intro!, simp]:"\<lbrakk>x \<in> free_magma X; y \<in> free_magma X\<rbrakk> \<Longrightarrow>  x \<star> y \<in> free_magma  X "

definition ext_free_magma :: "'a set \<Rightarrow> 'a frm set" where
  "ext_free_magma X = {t. set_frm t \<subseteq> X}"

lemma ext_free_magma_eta[simp, intro]:
  "x \<in> X \<Longrightarrow> \<eta> x \<in> ext_free_magma X"
  by (simp add: ext_free_magma_def)

lemma ext_free_magma_op[simp, intro]:
  "\<lbrakk>s \<in> ext_free_magma X; t \<in> ext_free_magma X\<rbrakk> \<Longrightarrow> s \<star> t \<in> ext_free_magma X"
  by (simp add: ext_free_magma_def)

lemma ext_free_magma_iff[simp]:
  "t \<in> ext_free_magma X \<longleftrightarrow> set_frm t \<subseteq> X"
  by (simp add: ext_free_magma_def)


inductive_cases free_magmaE[]:"x \<star> y \<in> free_magma  X"
inductive_cases free_magma_embeds:"\<eta> x \<in>  free_magma X"
inductive_cases free_magma_embeds_stable1[]:"(\<eta> x)\<star> y \<in>  free_magma X"
inductive_cases free_magma_embeds_stable2[]:"x \<star> (\<eta> y) \<in>  free_magma X"
inductive_cases free_magma_embeds_stable3[]:"(\<eta> x) \<star> (\<eta> y) \<in>  free_magma X"


lemma frm_set_emb_case:
  "y \<in> set_frm (\<eta> x) \<Longrightarrow> y = x"
  by auto

lemma frm_set1:
  "set_frm x \<union> set_frm y = set_frm (x \<star> y)" 
  by simp

lemma frm_set2:
  "set_frm (frm.map_frm f x) = f`(set_frm x)" 
  by(induct x, auto) 

lemma frm_set3: assumes
  "x \<in> (free_magma X)" shows 
  "set_frm x \<subseteq> X" using assms
proof(induct x)
  case (embeds x)
  then show ?case
    by simp 
next
  case (stable x y)
  then show ?case
    by simp 
qed

lemma free_magma_frm_set:"x \<in> free_magma X \<longleftrightarrow> (\<forall>y \<in> set_frm x. y \<in> X)"
proof(induct x)
  case (Em x)
  then show ?case
    using free_magma_embeds by force
next
  case (Op x1 x2)
  then show ?case
    by (meson free_magma.stable frm.set_intros(2,3) frm_set3 in_mono)
qed 

lemma frm_set4:
  "\<forall>y \<in> set_frm x. y \<in> X \<Longrightarrow> x \<in>(free_magma X)"
  by (simp add: free_magma_frm_set)


lemma ext_free_magma_eq_free_magma:
  "ext_free_magma X = free_magma X"
proof
  show "ext_free_magma X \<subseteq> free_magma X"
    using free_magma_frm_set by fastforce
  show "free_magma X \<subseteq> ext_free_magma X"
    by (simp add: frm_set3 subsetI)
qed

definition generator_image (\<open>'\<langle>_'\<rangle>\<close>) where "generator_image X = (\<eta>`X)"


section \<open>Length\<close>

fun l::"'a frm \<Rightarrow> nat" where
  "l (\<eta> x) = 1" |
  "l (x \<star> y) = (l x) + (l y)"

lemma len_gt_0:"l x > 0"
proof(induct x)
  case (Em x)
  then show ?case
    by simp
next
  case (Op x1 x2)
  then show ?case
    by simp 
qed

lemma len_lt:"x = a \<star> b \<Longrightarrow> l a < l x"
  by (simp add: len_gt_0)

lemma free_magma_cases2:
  assumes "x \<in> free_magma X"
  obtains "(\<exists>a \<in> X. x = \<eta> a) \<or> (\<exists>a \<in> free_magma X. \<exists>b\<in>free_magma X. (x = a \<star>b)) " 
using assms proof(induct x)
  case (embeds x)
  then show ?case
    by blast 
next
  case (stable x y)
  then show ?case
    by blast 
qed


lemma free_magma_cases2b:
  assumes "x \<in> free_magma X"
  obtains "(\<exists>a \<in> X. x = \<eta> a)"| " (\<exists>a \<in> free_magma X. \<exists>b\<in>free_magma X. (x = a \<star>b)) "
  using assms free_magma_cases2 by blast



lemma free_magma_cases2c:
  assumes "x \<in> free_magma X"
  obtains a where  "x = \<eta> a " "a \<in> X"|
  a b where "(x = a \<star>b)" "a \<in> free_magma X" "b\<in>free_magma X" 
  using assms free_magma.cases
  by blast



fun frm_set::"'a frm \<Rightarrow> 'a set" where
  "frm_set (\<eta> x) = {x}"|
  "frm_set (x \<star> y) = frm_set x \<union> frm_set y"



section \<open>Free magma Locale\<close>
locale free_magma_locale=fixes X::"'a set"
begin

lemma eta_inj1:
  "\<And>x x'. \<lbrakk>x \<in>X; x' \<in> X; \<eta> x = \<eta> x'\<rbrakk> \<Longrightarrow> x=x'" 
  by blast

lemma eta_inj2:
  "inj_on \<eta> X"  
  by (simp add: eta_inj1 inj_onI)

lemma eta_inj3:
  "\<lbrakk>x \<in>X; x' \<in> X; \<eta> x = \<eta> x'\<rbrakk> \<Longrightarrow> x=x'" 
  by blast

lemma eta_surj1:
  "\<And>y. y \<in> \<eta>`X \<Longrightarrow> (\<exists>x \<in> X. y = \<eta> x)" 
  by blast

lemma eta_surj2:
  "y \<in> \<eta>`X \<Longrightarrow> (\<exists>x \<in> X. y = \<eta> x)"
  by blast

lemma eta_bij:
  "bij_betw \<eta> X \<langle>X\<rangle>" 
  by (simp add: bij_betw_def eta_inj2 generator_image_def)

definition eta_inv where
  "eta_inv = (\<lambda>y.  if y \<in>  \<langle>X\<rangle>then (THE x. x \<in> X \<and> y = \<eta> x) else undefined)"

lemma eta_inv_simp[intro]:
  "y \<in> \<langle>X\<rangle> \<Longrightarrow> eta_inv y = (THE x. x \<in> X \<and> y = \<eta> x)"  
  by (simp add: eta_inv_def)

lemma eta_inv_unique1:
  assumes A0:"y \<in> \<langle>X\<rangle>" 
  obtains  x where "x \<in> X" and "y = \<eta> x" and "\<And>x'. x' \<in> X \<and> y = \<eta> x' \<Longrightarrow> x=x'"
  using A0 unfolding generator_image_def by blast

lemma eta_inv_unique2:
  assumes A0:"y \<in> \<langle>X\<rangle>" 
  obtains  x where "x \<in> X \<and> y = \<eta> x" and "\<forall>x'. x' \<in> X \<and> y = \<eta> x' \<longrightarrow> x=x'"
  using A0 unfolding generator_image_def by blast

lemma eta_inv_unique3:
  "y \<in> \<langle>X\<rangle> \<Longrightarrow> (\<exists>!x. x \<in> X \<and> y = \<eta> x)"
  using eta_inv_unique2[of y] by auto

lemma eta_inv_left:
  assumes A0:"x \<in> X"
  shows "eta_inv (\<eta> x) = x"
  using assms eta_inv_def generator_image_def by auto

lemma eta_inv_right:
  assumes A0:"y \<in> \<langle>X\<rangle>"
  shows "\<eta> (eta_inv y) = y"
  using assms eta_inv_left eta_inv_unique3 by blast

lemma eta_inv_inj1:
  " \<lbrakk>y \<in> \<langle>X\<rangle>;y' \<in> \<langle>X\<rangle>; eta_inv y = eta_inv y'\<rbrakk> \<Longrightarrow> y=y'" 
  using eta_inv_right[of y] eta_inv_right[of y'] by presburger

lemma eta_inv_inj2:
  "\<And>y y'. \<lbrakk>y \<in> \<langle>X\<rangle>;y' \<in> \<langle>X\<rangle>; eta_inv y = eta_inv y'\<rbrakk> \<Longrightarrow> y=y'" 
  using eta_inv_inj1 by presburger 

lemma eta_inv_inj3:
  "inj_on eta_inv  \<langle>X\<rangle>"
  using eta_inv_inj2 inj_onI by blast 

lemma eta_inv_surj1:
  "x \<in>X \<Longrightarrow> (\<exists>y \<in> \<langle>X\<rangle>. x = eta_inv y)"
  by (simp add: free_magma_locale.eta_inv_left generator_image_def) 

lemma eta_inv_surj2:
  "\<And>x. x \<in>X \<Longrightarrow> (\<exists>y \<in> \<langle>X\<rangle>. x = eta_inv y)"
  by (simp add: eta_inv_surj1)


lemma eta_inv_surj3:
  assumes A0:"y \<in> \<langle>X\<rangle>" 
  shows "eta_inv y \<in>X" 
proof-
  obtain x where "x \<in> X \<and> y = \<eta> x" and "\<forall>x'. x' \<in> X \<and> y = \<eta> x' \<longrightarrow> x=x'"
    using assms eta_inv_unique3 by blast
  then show ?thesis
    using eta_inv_left by force
qed

lemma eta_inv_surj4:"\<And>y. y \<in> \<langle>X\<rangle> \<Longrightarrow>eta_inv y \<in>X"
  by (simp add: eta_inv_surj3) 

lemma eta_inv_surj5:"eta_inv`\<langle>X\<rangle>  \<subseteq>X"
  using eta_inv_surj4 by blast

lemma eta_inv_surj6:"eta_inv`(\<langle>X\<rangle>) = X"
  using eta_inv_surj2 eta_inv_surj5 by blast

lemma "bij_betw eta_inv \<langle>X\<rangle> X"
  by (simp add: bij_betw_imageI eta_inv_inj3 eta_inv_surj6) 


end


context free_magma_locale
begin
abbreviation "M \<equiv> free_magma X"

sublocale is_magma:magma M Op
  by (simp add: magma.intro)

end

fun extend0::"('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>('a \<Rightarrow> 'b)  \<Rightarrow> ('a frm) \<Rightarrow> 'b"   where
  "extend0 Op' f (\<eta> x)  = f x" |
  "extend0 Op' f (x \<star> y) =  Op' (extend0 Op' f x) (extend0 Op' f y)"



section \<open>X/U Category\<close>

locale free_magma_forget_under=dom:free_magma_locale X + cod:magma Y "(\<cdot>)" 
  for f::"'a \<Rightarrow> 'b" and X::"'a set" and Y::"'b set" and codomain_law (infixl "\<cdot>" 70) +
  assumes into[intro,simp]:"x \<in> X \<Longrightarrow> f x \<in> Y"
begin

abbreviation extend1::"('a frm \<Rightarrow> 'b)"  ("M'(f')")
  where "M(f) \<equiv> (\<lambda>x. (extend0 (\<cdot>) f) x)"


lemma peen1:"x \<in> X \<Longrightarrow> (M(f) \<circ> \<eta>) x = f x" by simp
lemma peen2:  "\<And>x. x \<in> X \<Longrightarrow> (M(f) \<circ> \<eta>) x = f x"  using peen1 by blast 
lemma peen3:"\<lbrakk>x \<in> dom.M;y \<in> dom.M\<rbrakk> \<Longrightarrow> M(f) (x \<star> x') = (M(f) x) \<cdot> (M(f) x')" by auto
lemma peen3b:"\<And>x x'. \<lbrakk>x \<in> dom.M; x' \<in> dom.M\<rbrakk> \<Longrightarrow> M(f) (x \<star> x') = (M(f) x) \<cdot> (M(f) x')" using peen3 by blast
lemma peen4:"comm M(f) dom.M Op Y (\<cdot>)" using comm_def peen3b by blast

lemma mega_peen:
  assumes  "x \<in> dom.M"  shows "M(f) x \<in> Y"
  using assms by(induct x, auto)
 

lemma peen6:"\<And>x. x \<in> dom.M \<Longrightarrow> M(f) x \<in> Y"  using mega_peen by force

lemma peen7:"M(f)`dom.M \<subseteq> Y"  by (simp add: image_subset_iff peen6)

lemma peen8:"magma_homomorphism M(f) dom.M Op Y (\<cdot>)"
  by (simp add: cod.magma_axioms dom.is_magma.magma_axioms magma_homI peen4 peen6)



lemma peen9:
  assumes A0:"\<And>x. x \<in> X \<Longrightarrow> (M(f) (\<eta> x)) = (g (\<eta> x))" and
          A1:"\<And>x x'. \<lbrakk>x \<in> dom.M; x' \<in> dom.M\<rbrakk> \<Longrightarrow>g (x \<star> x') = (g x) \<cdot> (g x')" and 
          A2:"x \<in> dom.M"
  shows "M(f) x = g x"
  using A2 A0 A1 by(induct x; auto)


lemma peen11:
  assumes A0:"\<And>x. x \<in> X \<Longrightarrow> (M(f) (\<eta> x)) = (g  (\<eta> x))" and
          A1:"comm g dom.M (\<star>) Y (\<cdot>)"  and
          A2:"x \<in> dom.M"
        shows "M(f) x = g x"
  using A0 A1 A2  peen9[of g x] by (simp add: magma_homE)

end



lemma free_magma_inf0:
  assumes A0:"a \<in> (\<Inter>X \<in>\<X>. free_magma X)" 
  shows "a \<in> free_magma (\<Inter>\<X>)" using A0
proof(induct a)
  case (Em x)
  then obtain "\<eta> x \<in> \<Inter> (free_magma ` (\<X>))" and "\<forall>X \<in> \<X>. \<eta> x \<in> free_magma X"
    by auto
  then obtain "\<forall>X \<in> \<X>. x \<in> X" using free_magma_embeds[of x] by blast
  then show ?case
    by simp 
next
  case (Op a b)
  obtain "\<forall>X \<in> \<X>. a \<star> b \<in> free_magma X"
    using Op.prems by auto
  obtain "\<forall>X \<in> \<X>. a \<in> free_magma X" and "\<forall>X \<in> \<X>. b \<in> free_magma X" 
    using Op.prems INT_iff[of _ free_magma \<X>] free_magmaE by metis
  then obtain "a \<in>free_magma (\<Inter> \<X> )" and "b \<in> free_magma (\<Inter> \<X> )"
    using Op.hyps(1,2) by blast
  then show ?case
    by simp
qed

lemma free_magma_iso:assumes A0:"X \<subseteq> X' "
  shows "free_magma X \<subseteq> free_magma X'"
  using A0 free_magma.induct[of _ X "\<lambda>x. x \<in> free_magma X'"] by blast

lemma free_magma_inf1:
  assumes A0: "a \<in> free_magma (\<Inter>\<X>)"
  shows"a \<in> (\<Inter>X \<in>\<X>. free_magma X)"  using A0
  using Inter_lower free_magma_iso by fastforce

lemma free_magma_inf:"free_magma (\<Inter>\<X>) = (\<Inter>X \<in>\<X>. free_magma X)"
  by(intro subset_antisym, auto elim!: free_magma_inf1 free_magma_inf0)



section \<open>Free Magma Functor\<close>
locale free_magma_funct=dom:free_magma_locale X + cod:free_magma_locale Y
  for f::"'a \<Rightarrow> 'b" and X::"'a set" and Y::"'b set"+
  assumes set_hom[intro!, simp]:"\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y"
begin

abbreviation extension ("M'(_')") where "extension g\<equiv> (\<lambda>x. frm.map_frm g x)"

lemma extendo_peen:
  assumes A0:"\<And>x. x \<in> X \<Longrightarrow> (r \<circ> g) x = id x" and A1:"x \<in> free_magma X"
  shows "frm.map_frm (r \<circ> g) x= frm.map_frm id x "
  using A0 A1 free_magma_frm_set[of _ X] frm.map_cong0[of x "r \<circ> g" "id"] by blast

lemma extendo_peen2:
  assumes A0:"\<And>y. y \<in> Y \<Longrightarrow> (g \<circ> r) y = id y" and A1:"y \<in> free_magma Y"
  shows "frm.map_frm (g \<circ> r) y= frm.map_frm id y"
  using A0 A1 free_magma_frm_set[of _ Y] frm.map_cong0[of y "g \<circ> r" "id"] by blast

lemma is_hom1:"\<lbrakk>x \<in> dom.M;x' \<in> dom.M\<rbrakk> \<Longrightarrow> (M(f) x )\<star> (M(f) x') = M(f) (x \<star> x')"
  by simp
lemma is_hom2:"comm M(f) dom.M Op cod.M Op"  by (simp add: comm_def)


lemma inj_onI1:
  assumes A0:"inj_on f X"
  shows "inj_on M(f) dom.M"
proof-
  obtain g where B0:"\<And>x. x \<in> X \<Longrightarrow> (g \<circ> f) x = id x"
    using A0 comp_def[of _ f] the_inv_into_f_f[of f X] by auto
  have B1:"\<And>x. x \<in> dom.M \<Longrightarrow> (M(g) \<circ> M(f)) x = M(g \<circ> f) x"
    by (simp add: frm.map_comp)
  have B2:"\<And>x. x \<in> X \<Longrightarrow>  M(g \<circ> f) (\<eta> x) = M(id) (\<eta> x)"
    using B0 by auto
  have B3:"\<And>x. x \<in> dom.M \<Longrightarrow>  (M(g) \<circ> M(f)) x = id x"
  proof-
    fix x assume A1:"x \<in> dom.M"
    then have "(M(g) \<circ> M(f)) x = M(g \<circ> f) x"
      using B1 by auto
    also have "... = M(id) x"
      using A1 B0 extendo_peen by blast
    also have "... = id x"
      by (simp add: frm.map_id0)
    then show "(M(g) \<circ> M(f)) x = id x"
      using calculation by auto
  qed
  then show ?thesis
    using inj_on_inverseI by auto
qed


lemma surj1:
  assumes A0:"Y=f`X" and A1:"y \<in> cod.M"
  shows "\<exists>x \<in> dom.M. M(f) x = y"
  using A1 proof(induct)
  case (embeds x)
  then show ?case
    using A0 free_magma.embeds[of _ X] image_iff[of _ f X]  frm.simps(9)[of f] by blast
next
  case (stable x y)
  then show ?case
    using frm.simps(10) by blast 
qed

lemma surj2:
  assumes A0:"x \<in> dom.M"
  shows "M(f) x \<in> cod.M"
  using A0 by(induct x; auto)



lemma surj_onI1:
  assumes A0:"Y= f`X"
  shows " cod.M = (M(f)`dom.M)"
proof-
  let ?s="inv_into X f"
  have B0:"\<And>y. y \<in> Y \<Longrightarrow> (f \<circ> ?s) y = id y"
    by (simp add: Hilbert_Choice.f_inv_into_f assms)
  have B1:"\<And>y. y \<in> cod.M \<Longrightarrow> (M(f) \<circ> M(?s)) y = M(f \<circ> ?s) y"
    by (simp add: frm.map_comp)
  have B2:"\<And>y. y \<in> Y\<Longrightarrow>  M(f \<circ> ?s) (\<eta> y) = M(id) (\<eta> y)"
    using B0 by auto
  have B3:"\<And>y. y \<in> cod.M \<Longrightarrow>  (M(f) \<circ> M(?s)) y = id y"
  proof-
    fix y assume A1:"y \<in> cod.M"
    then have "(M(f) \<circ> M(?s)) y = M(f \<circ> ?s) y"
      using B1 by auto
    also have "... = M(id) y"
      using A1 B0 extendo_peen2 by blast
    also have "... = id y"
      by (simp add: frm.map_id0)
    then show "(M(f) \<circ> M(?s)) y = id y"
      using calculation by auto
  qed
  have B4:"\<And>y. y \<in> cod.M \<Longrightarrow> M(?s) y \<in> dom.M"
  proof-
    fix y assume A1:"y \<in>cod.M" 
    show "M(?s) y \<in> dom.M"
    using A1 proof(induct)
    case (embeds x)
    then show ?case
        by (simp add: assms inv_into_into) 
    next
      case (stable x y)
      then show ?case
        by simp 
    qed
  qed
  show ?thesis
  proof
    show "cod.M \<subseteq>M(f)`dom.M"
    proof
      fix y assume A1:"y \<in> cod.M"
      then obtain  "M(f) (M(?s) y) = y" and "M(?s) y \<in> dom.M"
        using A1 B3 B4 by auto
      then show "y \<in> M(f)`dom.M"
        using image_iff by fastforce
    qed
    show "M(f)` dom.M \<subseteq> cod.M"
      using surj2 by force
  qed
qed


lemma bij_betw_lifting:
  assumes A0:"bij_betw f X Y"
  shows "bij_betw M(f) dom.M cod.M"
  using A0 unfolding  bij_betw_def
  by (simp add: inj_onI1 surj_onI1)

end



lemma aut_stable1:
  assumes A0:"comm f (free_magma X) Op (free_magma X) Op" and
          A1:"bij_betw  f (free_magma X)  (free_magma X)" 
        shows "f`(\<eta>`X) \<subseteq> \<eta>`X" and
              "(f \<circ> \<eta>)`X \<subseteq> \<eta>`X"
proof-
  show "f`(\<eta>`X) \<subseteq> \<eta>`X" 
  proof
    let ?M="(free_magma X)"
    fix x assume A4:"x \<in> f`\<eta>`X"
    then obtain u where B0:"u \<in> X" and B1:"x = f (\<eta> u)" by blast
    have  B2:"x \<in> free_magma X"
      using  B0 B1 A1 bij_betw_imp_surj_on[of f ?M ?M]  free_magma.embeds by fastforce
    have B0d:"\<eta> u \<in> ?M"
      by (simp add: B0)
    have B0e:"inj_on f ?M"
      using A1 bij_betw_def by blast
    show "x \<in> \<eta> ` X"
    proof(cases x)
      case (Em x1)
      then obtain x1 where "x1 \<in> X" and "x = \<eta> x1"
        by (metis B2 free_magma_embeds)
      then show ?thesis
        by simp 
    next
      case (Op x21 x22)
      then obtain A3:"x \<notin> (\<eta>`X)" and A4:"\<And>a. a \<in> X \<Longrightarrow> x \<noteq> \<eta> a"
        by blast
      then obtain x21 x22 where B3:"x21 \<in>?M" and B4:"x22\<in>?M" and B5:"x=Op x21 x22"
        by (metis B2 Op free_magmaE) 
      then obtain B6:"\<exists>a \<in> free_magma X. x21 = f a" and B7:"\<exists>b \<in> free_magma X. x22 = f b"
        using A1 bij_betw_imp_surj_on[of f ?M ?M] by blast
      then obtain a b where B8:"a\<in>?M" and B9:"b\<in>?M" and B10:"x21=f a" and B11:"x22=f b" and  B12:"a\<star>b\<in>?M"
         using free_magma.stable by blast
      then obtain B13:"(f a)\<star>(f b) = f (a\<star> b)" and B14:"f (\<eta> u ) = f (a\<star> b)"
        using A0 B1 B5 magma_homE by fastforce
      then obtain "\<eta> u  = a\<star>b"
        using B14 B0e by (simp add: B0d B12 inj_on_eq_iff)
      then have False
        by simp
      then show ?thesis
        by simp 
    qed
  qed
  then show "(f \<circ> \<eta>)`X \<subseteq> \<eta>`X"
    by (simp add: image_comp)
qed


lemma aut_stable4:
  assumes A0:"comm f (free_magma X) Op (free_magma X) Op" and
          A1:"bij_betw  f (free_magma X)  (free_magma X)"
  shows  aut_stable4c:"magma_isomorphism.f_inv f (free_magma X)`(\<eta>`X) \<subseteq> \<eta>`X"  and
         aut_stable4a:"(inv_into (free_magma X) f)`(\<eta>`X) \<subseteq> \<eta>`X" and
         aut_stable4b:"\<And>a. a \<in> X \<Longrightarrow> (\<exists>b \<in> X. f (\<eta> b) = \<eta> a)"
proof-
  let ?g="inv_into (free_magma X) f"
  interpret iso:magma_isomorphism f "free_magma X" Op "free_magma X" Op
    apply(unfold_locales)
    apply simp
    apply (simp add: A0)
    using A1 bij_betwE apply blast
    by (simp add: A1)
  have iso_eq:"?g = iso.f_inv"
    using iso.f_inv_def by auto
  have B0:"comm iso.f_inv (free_magma X) Op (free_magma X) Op"
    by (simp add: iso.inv_hom)
  have B1:"bij_betw iso.f_inv (free_magma X)  (free_magma X)"
    by (simp add: iso.inv_bij)
  then have B2:"iso.f_inv`(\<eta>`X) \<subseteq> \<eta>`X"
    using B0 aut_stable1 by blast
  then show P0:"magma_isomorphism.f_inv f (free_magma X)`(\<eta>`X) \<subseteq> \<eta>`X"
    by auto
  then show P1:"(inv_into (free_magma X) f)`(\<eta>`X) \<subseteq> \<eta>`X"
    using iso_eq by presburger
  show "\<And>a. a \<in> X \<Longrightarrow>  (\<exists>b \<in> X. f (\<eta> b) = \<eta> a)"
  proof-
    fix a assume A2:"a \<in> X"
    have B3: "iso.f_inv (\<eta> a) \<in> \<eta>`X"
      using B2 A2 by blast
    then show "\<exists>b \<in> X. f (\<eta> b) = \<eta> a"
    proof-
      have "\<eta> a \<in> free_magma X"
        using A2 by force
      then have "\<eta> a = f (inv_into (free_magma X) f (\<eta> a))"
        using A1 bij_betw_inv_into_right by fastforce
      then show ?thesis
        using B3 iso.f_inv_def by auto
    qed
  qed
qed


section \<open>Automorphisms\<close>

definition set_automorphisms :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) set" where
  "set_automorphisms X \<equiv> {f. bij_betw f X X}"

definition magma_automorphisms::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) set" where
  "magma_automorphisms X op \<equiv> {f. bij_betw f X X \<and> comm f X op X op}"

context magma
begin
interpretation free_magma_magma:magma "free_magma X" "Op"  by (unfold_locales, simp)
end


subsection \<open>Automorphism of Free Magma\<close>
locale free_magma_aut=dom:free_magma_locale X
  for \<phi>::"'a frm \<Rightarrow> 'a frm" and X::"'a set" +
  assumes bij:"bij_betw \<phi> dom.M dom.M" and
          comm:"comm \<phi> dom.M Op dom.M Op"
begin


interpretation iso:magma_isomorphism \<phi> dom.M Op dom.M Op
  by (simp add: bij comm dom.is_magma.magma_axioms magma_iso_intro)

definition f::"'a \<Rightarrow> 'a" where "f \<equiv> (\<lambda>x. dom.eta_inv (\<phi> (\<eta> x)))"
abbreviation \<psi>::"'a frm \<Rightarrow> 'a frm" where "\<psi> \<equiv> inv_into dom.M \<phi>"

lemma f_eq:"f = (dom.eta_inv \<circ> \<phi> \<circ> \<eta>)" using f_def by auto


lemma f_inj0:"inj_on \<phi> dom.M"
  using bij bij_betw_def by blast


lemma gen_sub:"(\<eta>`X) \<subseteq> dom.M"
  by blast

lemma f_inj1:"inj_on \<phi> (\<eta>`X)"
  by (meson f_inj0 gen_sub inj_on_subset)

lemma f_inj2:"inj_on (\<phi> \<circ> \<eta>) X"
  by (simp add: comp_inj_on dom.eta_inj2 f_inj1)

lemma f_inj3:"(\<phi> \<circ> \<eta>)`X \<subseteq> \<eta>`X"
  using aut_stable1(2) bij comm by blast

lemma f_inj4:"inj_on dom.eta_inv ((\<phi> \<circ> \<eta>)`X)"
  by (metis dom.eta_inv_inj3 f_inj3 generator_image_def inj_on_subset)

lemma f_inj5: "inj_on (dom.eta_inv \<circ> (\<phi> \<circ> \<eta>)) X"
  using comp_inj_on f_inj2 f_inj4 by blast

lemma f_inj6:"inj_on f X"
  by (simp add: comp_assoc f_eq f_inj5)

lemma f_surj:"f`X \<subseteq> X"
proof-
  have "\<eta> ` X = \<langle>X\<rangle>"
    by (simp add: bij_betw_imp_surj_on dom.eta_bij)
  then have "(\<phi> \<circ> \<eta>) ` X \<subseteq> \<langle>X\<rangle>"
    using f_inj3 by argo
  then show ?thesis
    using dom.eta_inv_surj6 f_eq by auto
qed

lemma gen_cong:
  assumes A0:"x \<in> X"
  shows "(free_magma_funct.extension f) (\<eta> x) = \<phi> (\<eta> x) "
  using assms
proof-
  have "\<phi> (\<eta> x) = \<phi> (\<eta> x) \<and> \<phi> (\<eta> x) \<in> \<eta> ` X"
    using assms aut_stable1 bij comm by blast
  then show "(free_magma_funct.extension f) (\<eta> x) = \<phi> (\<eta> x) "
    by (simp add: free_magma_locale.eta_inv_right generator_image_def f_def)
qed

lemma is_bij_btw:
  "bij_betw f X X"
  unfolding bij_betw_def proof
  show "inj_on f X"
    by (simp add: f_inj6)
  show "f ` X = X"
  proof
    show left:"f`X \<subseteq> X"
      using f_surj by force
    show "X \<subseteq> f`X"  
    proof
      fix a assume A3:"a \<in> X"
      have "\<exists>b \<in> X. \<phi> (\<eta> a) = \<eta> b"
        using A3 f_inj3 by auto
      have B0:"\<eta> a \<in> dom.M"
        by (simp add: A3)
      have "\<phi> ( \<psi> (\<eta> a)) = \<eta> a"
        by (meson B0 bij bij_betw_inv_into_right)
      have "\<exists>b \<in> X. a = f b"
        by (metis A3 aut_stable4b bij comm dom.eta_inv_right dom.eta_inv_surj2 f_def)
      then show "a \<in> f`X"
        by blast
    qed
  qed
qed

lemma is_set_aut:"f \<in>set_automorphisms X"
  by (simp add: is_bij_btw set_automorphisms_def)


lemma aut_stable3:"(\<eta>`X) \<subseteq> \<phi>`(\<eta>`X) "
  by (metis aut_stable4a bij bij_betw_def comm gen_sub image_inv_into_cancel image_mono)

lemma aut_stable5:
  "(\<eta>`X) = \<phi>`(\<eta>`X) "
  using aut_stable3 f_inj3 by auto

end



section \<open>Free Submagmas\<close>


subsection \<open>Free Magma of Subset\<close>
locale free_magma_submagma=tmp:free_magma_funct id A X
  for X::"'a set" and A::"'a set"+
  assumes sub:"A \<subseteq> X"
begin

abbreviation N  where "N  \<equiv> magma.cl tmp.cod.M Op (\<eta>`A)"
abbreviation N' where "N' \<equiv> tmp.dom.M"(*M(A)*)
abbreviation M  where "M  \<equiv> tmp.cod.M"(*M(X)*)
abbreviation f  where "f  \<equiv> M(id)"
 (* f (\<eta> a) = (\<eta> a)
    f (x \<star> y) = (f x) \<star> (f y)                           
*)

interpretation nmag:magma N Op
  by (simp add: magma.intro tmp.cod.is_magma.cl_def)

interpretation npmag:magma N' Op
  by (simp add: tmp.dom.is_magma.magma_axioms)

lemma inclusion_inj:"inj_on id A" 
  by simp

lemma extension_inj:"inj_on f N'"
  by (simp add: tmp.inj_onI1) 

lemma extension_bij1:"bij_betw f N' (f`N')"
  by (simp add: extension_inj inj_on_imp_bij_betw)

lemma ext_sub0:
  assumes A0:"x \<in> N'"
  shows "x \<in> N"
  using A0 proof(induct x)
  case (embeds a)
  then obtain "a \<in> A" and "\<eta> a \<in> \<eta>`A"
    by simp
  then show ?case
    using sub tmp.cod.is_magma.cl_def by auto 
next
  case (stable a1 a2)
  then show ?case
    by blast 
qed

lemma ext_sub1:
  assumes A0:"x \<in> N"
  shows "x \<in> N'"
  using A0 proof(induct x)
  case (Em a)
  then have "\<eta> a \<in> N"
    by simp
  then show ?case
    by (metis free_magma.embeds frm.distinct(1) image_subsetI in_mono sub tmp.cod.is_magma.magma_cl_cases)
next
  case (Op a1 a2)
  then show ?case
  proof -
    have "\<forall>A. \<eta> ` (A::'a set) \<subseteq> free_magma A"
      by blast
    then show ?thesis
      by (metis Op.prems antisym ext_sub0 free_magma.stable subsetI tmp.cod.is_magma.cl_magma_stable_ub2)
  qed
qed

lemma ext_sub2:"(f`N') \<subseteq> N"
  by (simp add: ext_sub0 frm.map_id0 subsetI) 



lemma ext_sub3:"N \<subseteq> (f`N')"
  by (simp add: ext_sub1 frm.map_id0 subsetI) 

  
lemma inc_comm:"comm f N' Op N Op"
  by (simp add: commI)

lemma ext_eq:"f`N' = N"
  using ext_sub2 ext_sub3 by blast

lemma extension_bij2:"bij_betw f N' N"
  using ext_eq extension_bij1 by force

lemma inc_iso:"magma_isomorphism f N' Op N Op"
  by (simp add: extension_bij2 inc_comm magma_iso_intro nmag.magma_axioms tmp.dom.is_magma.magma_axioms)

lemma inc_sub:"submagma (M(id)`(N')) M Op"
  by (simp add: free_magma_iso frm.map_id0 sub submagmaI tmp.cod.is_magma.magma_axioms)


end

subsection \<open>Submagma of a Free Magma\<close>
locale free_submagma_magma=
  fixes X::"'a set" and N::"'a frm set" 
  assumes sub:"submagma N (free_magma X) Op"
begin

abbreviation M where "M \<equiv> free_magma X"
abbreviation B where "B \<equiv> N - ((\<Union>a\<in>N. \<Union>b \<in> N. {Op a b}))"
abbreviation Y where "Y \<equiv> free_magma B"
abbreviation f where "f \<equiv> (free_magma_forget_under.extend1 (id::('a frm \<Rightarrow> 'a frm)) Op)"

lemma B_iff:"y \<in> B \<longleftrightarrow> y \<in> N \<and> (\<forall>a \<in> N. \<forall>b \<in> N. y \<noteq> a \<star> b)"
  by(auto)

lemma B_memE1:"y \<in> B \<Longrightarrow> (y \<in> N)" by auto
lemma B_memE2:"y \<in> B \<Longrightarrow> a \<in> N \<Longrightarrow> b \<in> N \<Longrightarrow> y \<noteq> a \<star> b" by auto
lemma B_memE3:"y \<in> B \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> N;b \<in> N\<rbrakk> \<Longrightarrow> y \<noteq> a \<star> b)" by auto
lemma B_memI:"y \<in> N \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> N;b \<in> N\<rbrakk> \<Longrightarrow> y \<noteq> a \<star> b) \<Longrightarrow> y \<in> B" by auto


lemma inc_bij:"inj_on (id::('a frm \<Rightarrow> 'a frm))  B"
  by simp

lemma l1:"magma Y (\<star>)"
  by (simp add: magma.intro)

lemma l2:"magma N (\<star>)"
  by (meson magma.intro sub submagma.subfun)

lemma l3:"comm f Y (\<star>) N (\<star>)"
  by (simp add: commI)


lemma l4:"\<And>x::'a frm frm. x \<in> free_magma B \<Longrightarrow> f x \<in> N"
proof-
  fix x::"'a frm frm" assume A0:"x \<in> Y"
  show "f x \<in> N"
  using A0 proof(induct)
    case (embeds x)
    then show ?case
      by auto 
  next
    case (stable x y)
    then show ?case
      by (simp add: l2 magma.closed) 
  qed
qed

   
lemma l5:"magma_homomorphism_axioms f Y (\<star>) N (\<star>)"
  using l3 l4 magma_homomorphism_axioms_def by blast

interpretation ext_hom:magma_homomorphism f Y Op N Op
  apply(unfold_locales)
  apply blast
  apply (simp add: l2 magma.closed)
  using l3 apply blast
  using l4 by blast

lemma l6:"\<lbrakk>a \<in> B; b \<in> B; f (\<eta> a) = f (\<eta> b) \<rbrakk> \<Longrightarrow> a = b"
  by fastforce


lemma free_magma_rcancellative:"\<lbrakk>a \<in> free_magma X;b \<in> free_magma X; c \<in> free_magma X; a\<star>b=a\<star>c\<rbrakk> \<Longrightarrow> b =c"
  by fastforce

lemma free_magma_lcancellative:"\<lbrakk>a \<in> free_magma X;b \<in> free_magma X; c \<in> free_magma X; b\<star>a=c\<star>a\<rbrakk> \<Longrightarrow> b =c"
  by fastforce

lemma l7:"inj_on f Y"
proof(rule inj_onI)
  fix x y::"'a frm frm"  assume A0:"x \<in> Y" and A1:"y \<in> Y" and A2:"f x = f y"
  show "x = y"
   using A0 A1 A2 proof(induct x arbitrary: y)
   case (embeds x)
   then show ?case
   proof(cases y)
     case (Em x1)
     then show ?thesis
       using embeds.prems(2) by fastforce
   next
     case (Op x21 x22)
     then obtain B0:"y = x21 \<star> x22"
       by auto
     then obtain B1:"f (\<eta> x) = f y" and B2:"f y = f (x21 \<star> x22)" and B3:"f (x21 \<star> x22) = (f x21) \<star> (f x22)"
       using embeds.prems(2) extend0.simps(2) by blast
     then obtain "f (\<eta> x) = (f x21) \<star> (f x22)"
       by force
     then obtain a b where "a \<in>Y" and "b \<in> Y" and "\<eta> x = a \<star> b"
       using Op embeds.hyps embeds.prems(1) free_magma.cases[of y B] by auto
     show ?thesis
       using \<open>\<eta> (x::'a frm) = (a::'a frm frm) \<star> (b::'a frm frm)\<close> by auto
   qed
 next
   case (stable x1 x2)
   then obtain B0:"x1 \<in> Y" and B1:"x2 \<in> Y" and B2:"y \<in> Y" and B3:"f (x1 \<star> x2) = f y" and 
               B4:"\<And>z. \<lbrakk>z \<in> Y; f x1 = f z\<rbrakk> \<Longrightarrow> x1 = z" and 
               B5:"\<And>z. \<lbrakk>z \<in> Y; f x2 = f z\<rbrakk> \<Longrightarrow> x2 = z"
     by blast
   then have B6:"f (x1 \<star> x2) = (f x1) \<star> (f x2)"
     by simp
   show "x1 \<star> x2 = y"
   proof(cases y)
     case (Em b)
     then obtain B7:"b \<in> B" and B8:"y = \<eta> b"
       using Em B2 free_magma_embeds[of b B] by argo
     then obtain "f y = b"
       by force
     then have " (f x1) \<star> (f x2) = b"
       using B3 by auto
     then have False
       using B0 B1 B7 by blast
     then show ?thesis
       by simp
   next
     case (Op y1 y2)
     then obtain B7: "f x1 = f y1" and B8:"f x2 = f y2" and B9:"y = y1 \<star> y2"
       using B3 by auto
     then obtain "x1 = y1" and "x2 = y2"
       using B2 B4[of y1] B5[of y2] free_magmaE by blast
     then show ?thesis
       by (simp add: Op)
   qed
 qed
qed

lemma l8:"f`Y=N" 
proof
  show "f ` Y\<subseteq> N"
    using l4 by force
  show "N \<subseteq> f`Y"
  proof-
    have "\<And>y. y \<in> N \<Longrightarrow> (\<exists>a \<in> Y. y = f a)"
    proof-
      fix y assume A0:"y \<in> N"
      then have A1:"y \<in> M"
        using sub submagma.sub[of N M Op y] by auto
      show  "(\<exists>a \<in> Y. y = f a)"
      using A0
      proof(induct y)
        case (Em b)
        then obtain "b \<in> X" and "(\<eta> b) \<in> N" 
          by (meson free_magma_embeds sub submagma.sub)
        then obtain "\<eta> (\<eta> b) \<in> Y" and "f (\<eta> (\<eta> b)) = (\<eta> b)"
          by fastforce
        then show "\<exists>a\<in>free_magma B. \<eta> b = f a"
          by force
      next
        case (Op y1 y2)
        then show ?case 
        proof(cases "y1 \<in> N \<and> y2 \<in> N")
          case True
          then obtain a1 where B0:"a1 \<in> Y" and B1:"y1 = f a1"
            using Op.hyps(1) by blast
          obtain a2 where B2:"a2 \<in> Y" and B3:"y2 = f a2"
            using True Op.hyps(2) by blast
          then obtain "a1 \<star> a2 \<in> Y" and "f (a1 \<star> a2) = (f a1) \<star> (f a2)"
            using B0 by simp
          then obtain "y1 \<star> y2 = f (a1 \<star> a2)"
            using B1 B3 by argo
          then show ?thesis
            using \<open>(a1::'a frm frm) \<star> (a2::'a frm frm) \<in> free_magma B\<close> by blast
        next
          case False
          then obtain "y1 \<star> y2 \<in> B" and B4:"\<eta> (y1 \<star> y2) \<in> Y" and B5:"y1 \<star> y2 = f (\<eta> (y1 \<star> y2))"
            by (simp add: Op.prems)
          show ?thesis
            using B4 B5 by(rule rev_bexI)
        qed
      qed
    qed
    then show ?thesis by blast
  qed
qed


lemma inc_iso:"magma_isomorphism f Y Op N Op"
proof(rule magma_isomorphism.intro)
  show "magma_homomorphism f (free_magma B) (\<star>) N (\<star>)"
    by (simp add: l1 l2 l5 magma_homomorphism_def)
  show "magma_isomorphism_axioms f (free_magma B) N"
    unfolding magma_isomorphism_axioms_def
    using bij_betw_imageI l7 l8 by blast
qed
end

section \<open>Magma Generated by Single Element\<close>
locale singleton_magma=fixes X::"'a set" and x::"'a frm"
  assumes elem:"x \<in> free_magma X"
begin

abbreviation "M \<equiv> (free_magma X)"
abbreviation "Cl \<equiv> magma.cl M Op"

definition deez ("M'(x')") where "M(x) \<equiv> Cl {x}"

lemma is_magma:"magma M(x) Op"
  by (simp add: deez_def magma.cl_def magma.intro)

lemma sub:"M(x) \<subseteq> M"
  by (simp add: deez_def magma.cl_magma_sub magma.intro)

interpretation Mx_magma:magma "M(x)" Op
  by (simp add: deez_def magma.cl_def magma.intro)

interpretation Mx_sub:submagma"M(x)" M Op
  by (simp add: magma.intro sub submagmaI)

interpretation Mx_free_sub:free_submagma_magma X "M(x)"
  by (simp add: Mx_sub.submagma_axioms free_submagma_magma_def)

abbreviation deez2 ("N'(x')") where "N(x) \<equiv> free_submagma_magma.Y M(x)"


end



lemma sugma:
  fixes X::"'a set" and x::"'a frm" and  y::"'a frm" 
  defines "Mx \<equiv> magma.cl (free_magma X) Op {x}" 
  defines "My \<equiv> magma.cl (free_magma X) Op {y}"
  assumes A0:"x \<in> free_magma X" and A1:"y \<in> free_magma X" and
          A2:"w \<in> Mx \<inter> My"  and  A3:"\<forall>w' \<in>  Mx \<inter> My.  \<not>((l w') < (l w))" and
          A4:"w \<noteq> y"
  shows dat_boi:"w=x" and
        zucc:"Mx \<subseteq> My"
proof-
  show P0:"w = x"
  proof-
    have B0:"magma (free_magma X) Op"
      by (simp add: Mx_def My_def magma.cl_def magma.intro)
    obtain B0b:"w \<in> Mx" and B0c:"w \<in> My" and B0d:"{x} \<subseteq> (free_magma X)" and B0e:"{y} \<subseteq> (free_magma X)"
      using A0 A1 A2 by blast
    interpret m:magma "(free_magma X)" Op
      by (simp add: B0)
    have B7:"w \<notin> {y}"
      by (simp add: A4)
    have B8:"w \<in> {x}"
    proof(rule ccontr)
      assume C0:"w \<notin> {x}"
      then obtain a b where C1:"a \<in> Mx" and C2:"b \<in> Mx" and C3:"w = a \<star> b"
        using B0 B0b B0d Mx_def magma.magma_cl_non_gen[of "free_magma X" Op "{x}" w] by blast
      obtain a' b' where C4:"a' \<in> My" and C5:"b' \<in> My" and C6:"w = a' \<star> b'"
        using B0 B0c B7 B0e My_def magma.magma_cl_non_gen[of "free_magma X" Op "{y}" w] by blast
      then obtain C7:"a=a'" and C8:"b=b'"
        by (simp add: C3)
      then obtain C9:"a \<in> Mx \<inter> My" and "l a < l w"
        using C1 C3 C4 len_lt by fastforce
      then show False
        using A3 by blast
    qed
    then show "w=x"
      by simp
  qed
  show P1:"Mx \<subseteq> My"
  proof-
    have "{x} \<subseteq> My"
      using A2 P0 by force
    then show "Mx \<subseteq> My"
      by (simp add: Mx_def My_def magma.cl_magma_stable_ub magma.cl_stable magma.intro)
  qed
qed

lemma scale_daddy:
  fixes X::"'a set" and x::"'a frm" and  y::"'a frm" 
  assumes A0:"x \<in> free_magma X" and A1:"y \<in> free_magma X" 
  defines "Mx \<equiv> magma.cl (free_magma X) Op {x}" 
  defines "My \<equiv> magma.cl (free_magma X) Op {y}"
  shows " (Mx \<inter> My = {}) \<or> (Mx \<subseteq> My) \<or> (My \<subseteq> Mx) "
proof-
  let ?dirty_mike="l`(Mx \<inter> My)"
  let ?dirty_dan="(\<lambda>k. k \<in>?dirty_mike)"
  have done_making_league_of_legends_videos:"Mx \<inter> My \<noteq> {} \<Longrightarrow> (Mx \<subseteq> My) \<or> (My \<subseteq> Mx) "
  proof-
    assume fleisch:"Mx \<inter> My \<noteq> {}"
    then have "?dirty_mike \<noteq> {}" by simp
    then obtain k where di:"k \<in> ?dirty_mike" and cks:"k = Least ?dirty_dan"
      using LeastI[of ?dirty_dan] all_not_in_conv[of ?dirty_mike] by presburger
    then obtain w where outfo:"w \<in> Mx \<inter> My" and rharambe:"l w = k"
      by blast
    then have clean_this_up:"\<forall>w' \<in>  Mx \<inter> My.  \<not>((l w') < (l w))"
      using cks image_eqI not_less_Least[of _ ?dirty_dan] by metis
    then show "(Mx \<subseteq> My) \<or> (My \<subseteq> Mx)"
    proof(cases "w \<noteq> y")
      case True
      then show ?thesis using sugma(2)
        using A0 A1 Mx_def My_def clean_this_up outfo by blast
    next
      case False
      then show ?thesis
        by (metis A0 A1 Int_commute Mx_def My_def clean_this_up outfo subsetI zucc) 
    qed
  qed
  then show ?thesis
    by auto
qed
    
    
  



end

