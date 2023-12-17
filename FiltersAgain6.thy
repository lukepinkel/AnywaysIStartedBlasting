theory FiltersAgain6
  imports Main "./Closures"
begin

hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65)

declare [[show_types]]



definition is_inhabited::"'X set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

lemma is_inhabited_imp:
  "\<And>X. is_inhabited X \<Longrightarrow> \<exists>x. x \<in> X"
  by (simp add: ex_in_conv is_inhabited_def)

definition is_downdir::"'X::ord set \<Rightarrow> bool" where
   "is_downdir X \<equiv> (\<forall>a b. (a \<in> X) \<longrightarrow> ( b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b)))"

lemma is_downdir_imp:
  assumes "is_downdir X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
  using assms is_downdir_def by blast

definition is_upclosed::"'X::ord set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

lemma is_upclosed_imp:
  assumes "is_upclosed X"
  shows "\<And>a b. (a \<le> b \<and> a \<in> X) \<Longrightarrow> b \<in> X"
  using assms is_upclosed_def by blast

lemma upsets_moore_family:
  "is_moore_family {E::('X::order_top set). is_upclosed E}"
proof-
  let ?C="{E::('X::order_top set). is_upclosed E}"
  have B0:"\<forall>(a::'X::order_top set). (\<exists>m \<in> (principal_filter_in a ?C). (\<forall>x \<in> (principal_filter_in a ?C). m \<le> x))"
  proof
    fix A::"'X::order_top set"
    let ?Pa="{E::('X::order_top set). is_upclosed E \<and> A \<subseteq> E}"
    have B01:"is_upclosed (Inf ?Pa)"
      by (simp add: is_upclosed_def)
    have B02:"\<forall>E \<in> ?Pa. (Inf ?Pa) \<le> E"
      by blast
    have B03:"Inf?Pa \<in>  (principal_filter_in A ?C)"
      by (simp add: B01 le_Inf_iff principal_filter_def principal_filter_in_def)
    have B04:"?Pa = principal_filter_in A ?C"
      by (simp add: Collect_conj_eq principal_filter_def principal_filter_in_def)
    have B05:"\<forall>x \<in> ?Pa. (Inf ?Pa) \<le> x"
      by blast
    show "(\<exists>m \<in> (principal_filter_in A ?C). (\<forall>x \<in> (principal_filter_in A ?C). m \<le> x))"
      using B03 B04 by auto
  qed
  show ?thesis
    by (metis B0 empty_iff is_moore_family_def is_upclosed_def mem_Collect_eq)
qed


definition is_pisystem::"'X::{ord,inf} set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"


lemma is_pisystem_imp:
  assumes "is_pisystem X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (inf a b) \<in> X"
  using assms is_pisystem_def by blast


definition is_filter::"'X::ord set \<Rightarrow> bool" where 
  "is_filter F \<equiv> (is_downdir F \<and> is_upclosed F \<and> is_inhabited F)"

context fixes F::"'X::order set"
begin
lemma principal_filter_iso:
  assumes "is_upclosed F"
  shows "\<forall>a. a \<in> F \<longleftrightarrow> ((principal_filter a) \<subseteq> F)"
  by (metis assms is_upclosed_imp mem_Collect_eq order_refl principal_filter_def subset_eq)

end



lemma filter_topped:
  fixes F::"'X::order_top set"
  assumes A0:"is_filter F"
   shows "top \<in> F"
proof-
  have B0:"is_inhabited F"
    using A0 is_filter_def by auto
  have B1:"is_upclosed F"
    using is_filter_def assms by blast
  obtain x where B2:"x \<in> F"
    using B0 is_inhabited_def by fastforce
  have B3:"x \<le> top"
    by simp
  show ?thesis
    using B1 B2 B3 is_upclosed_def by blast
qed



lemma set_filter_topped:
  assumes A0:"is_filter F" shows "UNIV \<in> F"
  by (simp add: assms filter_topped)


lemma filter_improper_iff:
  fixes F::"'X::order_bot set"
  assumes A0:"is_filter F"
  shows "bot \<in> F \<longleftrightarrow> F=UNIV"
proof
  assume L:"bot \<in> F"
  have LB0:"\<forall>x. x \<in> F"
    using is_filter_def L assms bot.extremum is_upclosed_imp by blast
  show "F=UNIV"
    using LB0 by blast
  next
  assume R:"F=UNIV"
  show "bot \<in> F"
    by (simp add: R)
qed
  

lemma set_filter_improper_iff:
  assumes A0:"is_filter (F::('X set set))" 
  shows "{} \<in> F \<longleftrightarrow> F=Pow(UNIV)"
  by (simp add: assms filter_improper_iff)


definition binary_filter_sup::"'X::{ord, inf} set \<Rightarrow> 'X::{ord, inf} set \<Rightarrow> 'X::{ord, inf} set" where
  "binary_filter_sup A B = {x. \<exists>a \<in> A. \<exists>b \<in> B. (inf a b) \<le> x}"

definition filter_closure::"'X::complete_semilattice_inf set \<Rightarrow> 'X::complete_semilattice_inf set" where
  "filter_closure A \<equiv> {a. \<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a}"

lemma filter_closure_obtains0:
  "\<And>x. x \<in> filter_closure A \<longleftrightarrow> (\<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> x)"
  by (simp add: filter_closure_def)

lemma filter_closure_extensive:
  fixes A::"'X::complete_semilattice_inf set"
  shows " A \<subseteq> filter_closure A"
proof-
  have B0:"\<forall>a \<in> A. Inf {a} \<le> a"
    by (simp add: complete_semilattice_inf_class.Inf_lower)
  have B1:"\<forall>a \<in> A. {a} \<in> Pow(A) \<and> (finite {a}) \<and> ({a} \<noteq> {})"
    by simp
  have B2:"\<forall>a \<in> A. a \<in> (filter_closure A)"
    using B0 B1 filter_closure_def by blast
  show ?thesis
    by (simp add: B2 subset_iff)
qed

lemma filter_closure_isotone:
  fixes A::"'X::complete_semilattice_inf set" and  
        B::"'X::complete_semilattice_inf set"
  assumes A0:"A \<subseteq> B"
  shows "(filter_closure A) \<subseteq> (filter_closure B)"
proof
  fix x assume A1:"x \<in> (filter_closure A)"
  obtain S1 where A2:"S1 \<in> (Pow A) \<and> (finite S1) \<and> (S1 \<noteq> {}) \<and> (Inf S1) \<le> x"
    by (meson A1 filter_closure_obtains0)
  have B0:"S1 \<in> Pow  B"
    using A2 assms by blast
  obtain S2 where A3:"S2 \<in> (Pow B) \<and> (finite S2) \<and> (S2 \<noteq> {}) \<and> (Inf S2) \<le> x"
    using A2 B0 by blast
  show "x \<in> (filter_closure B)"
    using A2 B0 filter_closure_obtains0 by auto
qed




context fixes X::"'X::semilattice_inf set"
begin

lemma downdir_inf:
  assumes A0:"is_downdir X" and A1:"is_upclosed X"
  shows "\<And>(a::'X) b. (a \<in> X \<and> b \<in> X) \<longrightarrow> ((inf a b) \<in> X)"
proof
  fix a b assume A2:"(a \<in> X \<and> b \<in> X)"
  obtain c where A3:"c \<in> X \<and> (c \<le> a) \<and> (c \<le> b)"
    using A0 A2 is_downdir_imp by blast
  have B0:"c \<le> (inf a b)"
     by (simp add: A3)
  show "(inf a b) \<in> X"
    using A1 A3 B0 is_upclosed_imp by blast
qed

lemma downdir_up_pisystem:
  assumes "is_upclosed X"
  shows "(is_downdir X) \<longleftrightarrow> (is_pisystem X)"
proof
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AL:"?L"
  show "?R"
    by (simp add: AL assms downdir_inf is_pisystem_def)
  next
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AR:"?R"
  show "?L"
  proof-
    have ARB0:"\<And>a b. (a \<in> X \<and> b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix a b assume ARA0:"(a \<in> X \<and> b \<in> X)"
      have ARB1:"(inf a b) \<in> X"
        by (simp add: AR ARA0 is_pisystem_imp)
      have ARB2:"(inf a b) \<le> a \<and> (inf a b) \<le> b"
        by simp 
      show "(\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
        using ARB1 ARB2 by blast
    qed
    show ?thesis
      by (simp add: ARB0 is_downdir_def)
  qed
qed

lemma filter_in_semilattice_inf_iff:
  assumes "X \<noteq> {}"
  shows "is_filter X \<longleftrightarrow> (\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
proof-
  have LtR:"is_filter X \<longrightarrow> (\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
  proof
    assume LA0:"is_filter X"
    have LA1:"is_pisystem X"
      using is_filter_def LA0 downdir_up_pisystem by blast
    have LA2:"is_upclosed X"
      using is_filter_def LA0 by blast
    show "(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
    proof-
      have LB0:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longrightarrow> (inf x y) \<in> X)"
        by (simp add: LA1  is_pisystem_imp)
      have LB1:"(\<forall>x y.  (inf x y) \<in> X \<longrightarrow> (x \<in> X \<and> y \<in> X))"
        by (metis LA2 inf.cobounded1 inf.cobounded2 is_upclosed_imp)
      show ?thesis
        using LB0 LB1 by blast
    qed
  qed
  have RtL:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)\<longrightarrow> is_filter X"
    by (metis is_filter_def assms downdir_up_pisystem inf.absorb_iff2 is_inhabited_def is_pisystem_def is_upclosed_def)
  show ?thesis
    using LtR RtL by blast
qed

end

context fixes X::"'X::lattice set"
begin

lemma upclosed_in_lattice_iff:
  assumes "X \<noteq> {}"
  shows "is_upclosed X \<longleftrightarrow> (\<forall>x z. x \<in> X \<longrightarrow> (sup x z) \<in> X)"
  by (metis inf_sup_ord(3) is_upclosed_def sup.commute sup.orderE)
  
end


context complete_semilattice_inf
begin

lemma infs_eq:
  "inf x (Inf F) = Inf {x, Inf F}"
proof-
  let ?R=" Inf {x, Inf F}"
  let ?L="inf x (Inf F)"
  have B0:"?R \<le> x \<and> ?R \<le> Inf F"
    by (simp add: local.Inf_lower)
  have B1:"?L \<le> ?R"
    using local.Inf_greatest by fastforce
  have B2:"?L \<le> x \<and> ?L \<le> Inf F"
    by simp
  have B3:"?R \<le> ?L"
    by (simp add: B0)
  show ?thesis
    using B1 B3 local.dual_order.eq_iff by auto
qed

lemma infs_insert:
  "Inf {x, Inf F} = Inf (insert x F)"
proof-
  have B0:"\<forall>y \<in> (insert x F). Inf {x, Inf F} \<le> y"
    by (metis infs_eq insertCI insertE local.Inf_lower local.inf.coboundedI2)
  have B1:"\<forall>y \<in>  (insert x F).  Inf (insert x F) \<le> y"
    by (simp add: local.Inf_lower)
  have B2:"Inf {x, Inf F} \<le> Inf (insert x F)"
    using B0 local.Inf_greatest by blast
  have B3:"\<forall>y \<in> {x, Inf F}. (Inf (insert x F)) \<le> y"
    by (simp add: local.Inf_greatest local.Inf_lower)
  have B4:"Inf (insert x F) \<le> Inf {x, Inf F}"
    using B3 local.Inf_greatest by blast
  show ?thesis
    by (simp add: B2 B4 local.dual_order.eq_iff)
qed
  

lemma finite_meet_in_set:
  fixes C::"'a set"
  assumes A0: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (inf a1 a2) \<in> C" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> C"
  shows "(Inf E) \<in> C"
  using A1 A2 A3 
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    then show ?case
    proof-
      have S0:"Inf {x} \<le> x"
        by (simp add: local.Inf_lower)
      have S1:"x \<le> x"
        by simp
      have S2:"x \<le> Inf {x}"
        using local.Inf_greatest by fastforce
      have S3:"Inf {x} = x"
        by (simp add: S0 S2 local.dual_order.eq_iff)
      show S4:"Inf {x} \<in> C"
        using S3 singleton by force
    qed
  next
    case (insert x F)
    have P0:"x \<in> C"
      using insert.prems by auto
    have P1: "F \<subseteq> C" 
      using insert.prems by auto
    have P2:"inf x (Inf F) \<in> C"
      by (simp add: A0 P0 P1 insert.hyps(4))
    have P4:"Inf (insert x F) = inf x (Inf F)"
      by (simp add: infs_eq infs_insert)
    then show ?case
      by (simp add: P2 P4)
qed

end


lemma filter_closure_idempotent:
  fixes A::"'X::complete_semilattice_inf set"  
  shows "(filter_closure A) = (filter_closure (filter_closure A))"
proof-
  have B0:"(filter_closure(filter_closure A)) \<subseteq> filter_closure A"
  proof
    fix x assume A0:"x \<in> (filter_closure(filter_closure A))"
    obtain Ex where A1:"(Ex\<in>Pow( (filter_closure A)) \<and>  finite Ex \<and>  Ex \<noteq> {} \<and>  (Inf Ex) \<le> x)"
      by (meson A0 filter_closure_obtains0)
    have B1:"\<forall>y \<in> Ex. (\<exists>Ey \<in> Pow(A). finite Ey \<and> Ey \<noteq> {} \<and> (Inf Ey) \<le> y)"
      by (metis A1 UnionI Union_Pow_eq filter_closure_obtains0)
    define g where "g=(\<lambda>y. SOME Ey. Ey \<in> Pow(A) \<and> finite Ey \<and> Ey \<noteq> {} \<and> (Inf Ey) \<le> y)"
    have B2:"\<forall>y \<in>  Ex. ((g y) \<in> Pow(A) \<and> (finite (g y)) \<and> (g y \<noteq> {}) \<and> (Inf (g y)) \<le> y)"
      by (metis (mono_tags, lifting) B1 g_def someI)
    define E where "E=(\<Union>(g`Ex))"
    have B3:"E \<in> Pow (A) \<and> finite E \<and> E \<noteq> {}"
      using A1 B2 E_def by auto
    have B4:"\<forall>y \<in> Ex. (Inf E) \<le> (Inf (g y))"
      by (metis E_def UnionI Union_Pow_eq complete_semilattice_inf_class.Inf_greatest complete_semilattice_inf_class.Inf_lower image_subset_iff subset_Pow_Union)
    have B5:"\<forall>y \<in> Ex. (Inf E) \<le> y"
      using B2 B4 order.trans by blast
    have B6:"(Inf E) \<le> (Inf Ex)"
      by (simp add: B5 complete_semilattice_inf_class.Inf_greatest)
    have B7:"(Inf E) \<le> x"
      using A1 B6 order.trans by blast
    show "x \<in> filter_closure A"
      using B3 B7 filter_closure_obtains0 by blast
  qed
  show ?thesis
    by (simp add: B0 filter_closure_extensive set_eq_subset)
qed

lemma filter_closure_is_closure:
  "is_closure filter_closure"
proof-
  have A0:"is_extensive filter_closure"
    by (simp add: filter_closure_extensive is_extensive_def)
  have A1:"is_isotone filter_closure"
    by (simp add: filter_closure_isotone is_isotone_def)
  have A3:"is_idempotent filter_closure"
    using filter_closure_idempotent is_idempotent_def by blast
  show ?thesis
    by (simp add: A0 A1 A3 is_closure_def)
qed

definition filter_sup::"'X::complete_semilattice_inf set set \<Rightarrow> 'X::complete_semilattice_inf set" where
  "filter_sup EF \<equiv> filter_closure(Sup(EF))"




    

end