theory GaloisConnectionsAgain
  imports Main "./Posets" 
begin
declare [[show_types]]


definition relation_to_fgc::"('X \<times> 'Y) set \<Rightarrow> (('X set) \<Rightarrow> ('Y set))" where
  "relation_to_fgc R = (\<lambda>(A::('X set)). {(y::'Y). \<forall>x \<in> A. (x, y) \<in> R}) "

definition relation_to_ggc::"('X \<times> 'Y) set \<Rightarrow> (('Y set) \<Rightarrow> ('X set))" where
  "relation_to_ggc R = (\<lambda>(B::('Y set)). {(x::'X). \<forall>y \<in> B. (x, y) \<in> R}) "

definition is_gc2::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "is_gc2 f g \<equiv> (comp_extensive f g) \<and> (antitone f) \<and> (antitone g)"

definition is_join_dual::"('X::{Sup,order} \<Rightarrow> 'Y::{Inf,order}) \<Rightarrow> bool" where
  "is_join_dual f \<equiv> (\<forall>A. ( (f (Sup A)) = (Inf (f`(A))) ))"

definition join_dual_partner::"('X::{Sup,order} \<Rightarrow> 'Y::{Inf,order}) \<Rightarrow> ('Y::{Inf,order} \<Rightarrow> 'X::{Sup,order})" where
  "join_dual_partner f = (\<lambda>y::('Y::{Inf,order}). Sup {x::('X::{Sup,order}). y \<le> (f x)})"

definition is_gc4::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "is_gc4 f g \<equiv> \<forall>(x::('X::order)). \<forall>(y::('Y::order)). y \<le> (f x) \<longleftrightarrow> x \<le> (g y)"


lemma finite_ne_subset_induct[consumes 3, case_names singleton insert]:
  assumes "finite F"
      and "F \<noteq> {}"
      and "F \<subseteq> X"
      and singleton: "\<And>x . P {x}"
      and insert: "\<And>x E . finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow> E \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<notin> E \<Longrightarrow> P E \<Longrightarrow> P (insert x E)"
    shows "P F"
  using assms(1-3)
  apply (induct rule: finite_ne_induct)
  apply (simp add: singleton)
  by (simp add: insert)


lemma gc2_iff_gc4:
  "is_gc2 f g \<longleftrightarrow> is_gc4 f g"
proof-
  have LtR:"is_gc2 f g \<longrightarrow> is_gc4 f g"
  proof
    assume A0:"is_gc2 f g "
    have LR:"\<And>x y.  y \<le> (f x) \<longrightarrow> x \<le> (g y)"
    proof
      fix x y assume A1:"y \<le> f x"
      have B0:"(g (f x)) \<le> g y"
        using A0 A1 antitone_def is_gc2_def by auto
      have B1:"x \<le> (g (f x))"
        using A0 comp_extensive_def is_gc2_def by blast
      have B2:"... \<le> g y"
        by (simp add: B0)
      show "x \<le> g y"
        using B1 B2 by auto
    qed
    have RL:"\<And>x y.  x \<le> (g y) \<longrightarrow> y \<le> (f x)"
    proof
      fix x y assume A2:"x \<le> g y"
      have B3:"(f (g y)) \<le> f x"
        using A0 A2 antitone_def is_gc2_def by auto
      have B4:"y \<le> (f (g y))"
        using A0 comp_extensive_def is_gc2_def by blast
      have B5:"... \<le> f x"
        by (simp add: B3)
      show "y \<le> f x"
        using B4 B5 by auto
    qed
    show "is_gc4 f g"
      by (metis LR RL is_gc4_def)
  qed
  have RtL:"is_gc4 f g \<longrightarrow> is_gc2 f g"
  proof
    assume A3:"is_gc4 f g"
    have B6:"\<forall>x. x \<le> (g (f x))"
      using A3 is_gc4_def by blast
    have B7:"\<forall>y. y \<le> (f (g y))"
      using A3 is_gc4_def by auto
    have B8:"\<And>x1 x2. x1 \<le> x2 \<longrightarrow> (f x2) \<le> (f x1)"
      by (meson B6 A3 dual_order.trans is_gc4_def)
    have B9:"\<And>y1 y2. y1 \<le> y2 \<longrightarrow> (g y2) \<le> (g y1)"
      by (meson B7 A3 dual_order.trans is_gc4_def)
    show "is_gc2 f g"
      by (simp add: B6 B7 B8 B9 antitone_def comp_extensive_def is_gc2_def)
  qed
  show ?thesis
    using LtR RtL by blast
qed

lemma gc2_imp_join_dual:
  fixes f::"('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)"
  fixes g::"('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)"
  assumes A0:"is_gc2 f g"
  shows "is_join_dual f"
proof-
  have B0:"is_gc4 f g" using assms gc2_iff_gc4 by blast 
  have B1:"\<forall>A. (\<forall>a \<in> A. (f (Sup(A))) \<le> (f a))"
    by (meson antitone_def assms complete_lattice_class.Sup_upper is_gc2_def)
  have B2:"\<forall>A. (\<forall>a \<in> A. (f (Sup(A))) \<le> (Inf (f`A)))"
    by (simp add: B1 INF_greatest)
  have B3:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (\<forall>a \<in> A. (y \<le> (f a)))"
    by (simp add: le_INF_iff)
  have B4:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (\<forall>a \<in> A. (a \<le> (g y)))"
    by (meson B0 B3 is_gc4_def)
  have B5:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> ((Sup A) \<le> (g y))"
    by (simp add: B4 Sup_le_iff)
  have B6:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (y \<le> (f (Sup A)))"
    using B0 B5 is_gc4_def by blast
  show ?thesis
    by (meson B6 antisym dual_order.refl is_join_dual_def)
qed

lemma join_dual_imp_gc2:
  fixes f::"('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)"
  fixes g::"('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)"
  assumes A0:"is_join_dual f"
  shows "is_gc2 f (join_dual_partner f)"
proof-
  let ?g="(join_dual_partner f)"
  have B0:"\<And>x1 x2. (x1 \<le> x2) \<longrightarrow> (f x2) \<le> (f x1)"
  proof
    fix x1 x2 assume A1:"(x1::('X::complete_lattice)) \<le> (x2::('X::complete_lattice))"
    have B00:"Sup {x1, x2} = x2"
      using A1 le_iff_sup by auto
    have B01:"(f x2) = (f (Sup {x1, x2}))"
      using B00 by auto
    have B01:"... = (Inf {(f x1), (f x2)})"
      by (metis (mono_tags, lifting) assms image_insert image_is_empty is_join_dual_def)
    have B02:"... \<le> (f x1)"
      by simp
    show "(f x2) \<le> (f x1)"
      using B00 B01 B02 by auto
  qed
  have B1:"\<And>y1 y2. (y1 \<le> y2) \<longrightarrow> (?g y2) \<le> (?g y1)"
  proof
    fix y1 y2 assume A2:"(y1::('Y::complete_lattice)) \<le> (y2::('Y::complete_lattice))" 
    let ?B2="{x::('X::complete_lattice). y2 \<le> (f x)}"
    let ?B1="{x::('X::complete_lattice). y1 \<le> (f x)}"
    have B10:"(?g y2) = Sup ?B2"
      by (simp add: join_dual_partner_def)   
    have B11:"(?g y1) = Sup ?B1"
      by (simp add: join_dual_partner_def)   
    have B12:"?B2 \<subseteq> ?B1"
      using A2 by force
    have B13:"(?g y2) \<le> (?g y1)"
      by (simp add: B10 B11 B12 Sup_subset_mono)
    show "(?g y2) \<le> (?g y1)"
      by (simp add: B13)
  qed
  have B2:"\<And>(y::('Y::complete_lattice)). y \<le> (f (?g y))"
    by (metis assms is_join_dual_def join_dual_partner_def le_INF_iff mem_Collect_eq)
  have B3:"\<And>(x::('X::complete_lattice)). x \<le> (?g (f x))"
    by (simp add: complete_lattice_class.Sup_upper join_dual_partner_def)
  have B4:"(comp_extensive f ?g)"
    by (simp add: B2 B3 comp_extensive_def)
  have B5:"(antitone f) \<and> (antitone ?g)"
    by (simp add: B0 B1 antitone_def)
  show ?thesis
    by (simp add: B4 B5 is_gc2_def)
qed
      


end