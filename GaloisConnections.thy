theory GaloisConnections
  imports Main "./Posets"
begin

section Definitions

definition fully_supremum_dual :: "('X::complete_lattice \<Rightarrow> 'Y::complete_lattice) \<Rightarrow> bool" where
"fully_supremum_dual f \<equiv> \<forall>A. f (Sup A) = Inf (f ` A)"

definition fully_supremum_dual2 :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set  \<Rightarrow> bool" where
"fully_supremum_dual2 f X Y \<equiv> \<forall>A.( HasASup1 A X) \<longrightarrow> f (Sup1 A X) = Inf1 (f ` A) Y"

definition g_from_f :: "('X::complete_lattice \<Rightarrow> 'Y::complete_lattice) \<Rightarrow> ('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)" where
"g_from_f f y \<equiv> Sup {x. y \<le> f x}"

definition g_from_f2 :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set  \<Rightarrow> ('Y::order \<Rightarrow> 'X::order)" where
"g_from_f2 f X  y \<equiv> Sup1 {x. y\<le> f x} X"

definition f_from_R :: "('X \<times> 'Y) set \<Rightarrow> ('X set \<Rightarrow> 'Y set)" where
"f_from_R R A \<equiv> {y. \<forall>x \<in> A. (x, y) \<in> R}"

definition g_from_R :: "('X \<times> 'Y) set \<Rightarrow> ('Y set \<Rightarrow> 'X set)" where
"g_from_R R B \<equiv> {x. \<forall>y \<in> B. (x, y) \<in> R}"

definition g_from_f_pf:: "('X::complete_lattice \<Rightarrow> 'Y::complete_lattice) \<Rightarrow> ('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)" where
  "((g_from_f_pf f) b) \<equiv> (Sup {x. (b\<le> f x)})"

definition g_from_f_pf2:: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set  \<Rightarrow> ('Y::order \<Rightarrow> 'X::order)" where
  "((g_from_f_pf2 f) X  b) \<equiv> (Sup1 {x. (b\<le> f x)} X)"

definition GC1 :: "('X \<times> 'Y) set \<Rightarrow> ('X set \<Rightarrow> 'Y set) \<Rightarrow> ('Y set \<Rightarrow> 'X set) \<Rightarrow> bool" where
"GC1 R f g \<equiv> f = f_from_R R \<and> g = g_from_R R"

definition GC2 :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
"GC2 f g \<equiv>  antitone f \<and> antitone g \<and> comp_extensive f g"

definition GC3 :: "('X::complete_lattice \<Rightarrow> 'Y::complete_lattice) \<Rightarrow> ('Y::complete_lattice \<Rightarrow> 'X::complete_lattice) \<Rightarrow> bool" where
"GC3 f g \<equiv> fully_supremum_dual f \<and>  fully_supremum_dual g"

definition GC3_2 :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set  \<Rightarrow> ('Y::order \<Rightarrow> 'X::order)  \<Rightarrow> bool" where
"GC3_2 f X Y g  \<equiv> fully_supremum_dual2  f X Y  \<and>  fully_supremum_dual2 g Y X"

definition GC3b :: "('X::complete_lattice \<Rightarrow> 'Y::complete_lattice) \<Rightarrow> bool" where
"GC3b f \<equiv> fully_supremum_dual f"

definition GC3b2 :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow>  bool" where
"GC3b2 f X Y \<equiv> fully_supremum_dual2 f X Y"


definition GC3c :: "('X::complete_lattice \<Rightarrow> 'Y::complete_lattice) \<Rightarrow> ('Y::complete_lattice \<Rightarrow> 'X::complete_lattice) \<Rightarrow> bool" where
"GC3c f g \<equiv> fully_supremum_dual f \<and>  g= g_from_f f "

definition GC3c_2 :: "('X::order \<Rightarrow> 'Y::order)  \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set  \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
"GC3c_2 f X Y g \<equiv> fully_supremum_dual2 f X Y  \<and>  g= g_from_f2 f X "


definition GC4 :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
"GC4 f g \<equiv>  \<forall>x y. (y \<le> f x) \<longleftrightarrow> (x \<le> g y)"


definition GC4_2 :: "('X::order \<Rightarrow> 'Y::order)  \<Rightarrow>  'X::order set \<Rightarrow> 'Y::order set  \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
"GC4_2 f X Y g \<equiv>  \<forall>x \<in> X. \<forall>y\<in>Y. (y \<le> f x) \<longleftrightarrow> (x \<le> g y)"


section Lemmas

lemma GC2_imp_GC4: "GC2 f g \<Longrightarrow> GC4 f g"
proof -
  assume GC2: "GC2 f g"
  from GC2 have antitone_f: "antitone f" and antitone_g: "antitone g" and comp_extensive: "comp_extensive f g"
    unfolding GC2_def by simp_all
  show "GC4 f g"
  unfolding GC4_def
  proof (clarify)
    fix x y
    show "(y \<le> f x) = (x \<le> g y)"
    proof
      assume "y \<le> f x"
      hence "g (f x) \<le> g y" using antitone_g unfolding antitone_def by blast
      moreover have "x \<le> g (f x)" using comp_extensive unfolding comp_extensive_def by blast
      ultimately show "x \<le> g y" by simp
    next
      assume "x \<le> g y"
      hence "f (g y) \<le> f x" using antitone_f unfolding antitone_def by blast
      moreover have "y \<le> f (g y)" using comp_extensive unfolding comp_extensive_def by blast
      ultimately show "y \<le> f x" by simp
    qed
  qed
qed


lemma GC4_imp_antitone_f:
  assumes "GC4 f g"
  shows "antitone f"
  by (metis (no_types, lifting) GC4_def antitone_def assms dual_order.refl order_trans)

lemma GC4_imp_antitone_g:
  assumes "GC4 f g"
  shows "antitone g"
  by (metis (no_types, lifting) GC4_def antitone_def assms dual_order.refl order_trans)

lemma GC4_imp_antitone:
  assumes "GC4 f g"
  shows "antitone f \<and> antitone g"
  using GC4_imp_antitone_f GC4_imp_antitone_g assms by blast

lemma GC4_imp_compext:
  assumes "GC4 f g"
  shows "comp_extensive f g"
proof -
  obtain aa :: "('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a" where
    "comp_extensive f g \<or> \<not> aa g f \<le> g (f (aa g f))"
    by (metis GC4_def assms comp_extensive_def order_refl)
  then show ?thesis
    using GC4_def assms by auto
qed


lemma GC4_imp_GC2:
  assumes "GC4 f g"
  shows "GC2 f g"
  using GC2_def GC4_imp_antitone_f GC4_imp_antitone_g GC4_imp_compext assms by blast

lemma GC4_iff_GC2: "GC4 f g \<longleftrightarrow> GC2 f g"
  using GC2_imp_GC4 GC4_imp_GC2 by auto

lemma GC4_imp_fully_supremum_dual:
  assumes "GC4 f g"
  shows "fully_supremum_dual f"
  by (smt (verit, ccfv_threshold) GC4_def Inf_eqI Sup_le_iff Sup_least assms ball_imageD dual_order.refl fully_supremum_dual_def imageE)


lemma GC2_imp1:
  assumes A0:"GC2 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  shows " \<forall>A. f (Sup A) \<le> Inf (f ` A)"
  by (metis (full_types) GC2_imp_GC4 GC4_def Sup_upper assms le_INF_iff order_refl order_trans)

lemma GC4_imp_fully_supremum_dual2:
  assumes "GC4 f g"
  shows "fully_supremum_dual f"
  using GC4_imp_fully_supremum_dual assms by auto

lemma GC3_imp_f_antitone:
  assumes "GC3 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))" 
  shows " ((x1::'X::complete_lattice)\<le>(x2::'X::complete_lattice)) \<longrightarrow> ((f x2) \<le> (f x1))"
proof-
  have Q0:"(x1::'X::complete_lattice)\<le>(x2::'X::complete_lattice) \<longrightarrow> (Sup {x1, x2}=x2)"
    by (simp add: le_iff_sup)
  have Q1:"((x1::'X::complete_lattice)\<le>(x2::'X::complete_lattice)) \<longrightarrow> (f (Sup {x1, x2}) = Inf(f`{x1, x2}))"
    using GC3_def assms fully_supremum_dual_def by blast
  have Q2:"((x1::'X::complete_lattice)\<le>(x2::'X::complete_lattice)) \<longrightarrow> (f x2 = f (Sup {x1, x2}))"
    using Q0 by auto
  have Q3:"((x1::'X::complete_lattice)\<le>(x2::'X::complete_lattice)) \<longrightarrow> (Inf(f`{x1, x2}) \<le> f x1)"
    by auto
  have Q4:"((x1::'X::complete_lattice)\<le>(x2::'X::complete_lattice)) \<longrightarrow> ((f x2) \<le>  (f x1))"
  proof -
    have "Sup {x1, x2} = x2 \<or> \<not> x1 \<le> x2"
      using Q0 by blast
    then show ?thesis
      using Q1 Q3 by presburger
  qed
  with Q4 show ?thesis by auto 
qed

lemma GC2_imp_equiv1:
  assumes A0:"GC2 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  shows "((y::'Y::complete_lattice) \<le> Inf(f`(A::'X::complete_lattice set))) \<longleftrightarrow> (y::'Y::complete_lattice) \<le> f (Sup((A::'X::complete_lattice set)))"
  by (metis GC2_imp_GC4 GC4_imp_fully_supremum_dual2 assms fully_supremum_dual_def)

lemma GC2_imp_equiv2:
  assumes A0:"GC2 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  shows "((x::'X::complete_lattice) \<le> Inf(g`(B::'Y::complete_lattice set))) \<longleftrightarrow> (x::'X::complete_lattice) \<le> g (Sup((B::'Y::complete_lattice set)))"
  by (metis GC2_imp_GC4 GC4_def GC4_imp_fully_supremum_dual2 assms fully_supremum_dual_def)


lemma GC2_imp_equiv3:
  assumes A0:"GC2 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  shows "Inf(f`(A::'X::complete_lattice set)) =  f (Sup((A::'X::complete_lattice set)))"
  using GC2_imp1 GC2_imp_equiv1 assms order_antisym order_refl by blast

lemma GC2_imp_equiv4:
  assumes A0:"GC2 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  shows "Inf(g`(B::'Y::complete_lattice set)) =  g (Sup((B::'Y::complete_lattice set)))"
  by (meson GC2_imp_equiv2 assms dual_order.refl order_antisym)


lemma GC2_imp_GC3:
  assumes A0:"GC2 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  shows "GC3 (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)) (g::('Y::complete_lattice \<Rightarrow> 'X::complete_lattice))"
  by (metis GC2_imp_GC4 GC2_imp_equiv4 GC3_def GC4_imp_fully_supremum_dual2 assms fully_supremum_dual_def)

lemma GC3_imp_anti:
  assumes A0:"GC3b (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice))"
  shows "antitone f"
  by (smt (verit, ccfv_threshold) GC3b_def INF_insert Sup_empty Sup_insert antitone_def assms fully_supremum_dual_def inf_le1 le_iff_sup sup_bot.right_neutral)

lemma GC3_imp_extensive1:
  assumes A0:"GC3b (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice))" and
          A1:"g = g_from_f f"
  shows "\<forall>x. x \<le> g (f x)"
  by (simp add: A1 Sup_upper g_from_f_def)
  
lemma GC3_imp_extensive2:
  assumes A0:"GC3b (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice))" and
          A1:"g = g_from_f f"
  shows "\<forall>y. y \<le> f (g y)"
  by (smt (verit) A0 A1 GC3b_def fully_supremum_dual_def g_from_f_def le_INF_iff mem_Collect_eq)

lemma GC3_imp_extensive3:
  assumes A0:"GC3b (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice))" and
          A1:"g = g_from_f f"  
  shows "comp_extensive f g"
  by (simp add: A0 A1 GC3_imp_extensive1 GC3_imp_extensive2 comp_extensive_def)

lemma GC3b_imp_GC2:
  assumes A0:"GC3b (f::('X::complete_lattice \<Rightarrow> 'Y::complete_lattice))" and
          A1:"g = g_from_f f" 
  shows "GC3 f g"
  by (smt (verit, ccfv_threshold) A0 A1 GC2_def GC2_imp_GC3 GC3_imp_anti GC3_imp_extensive2 GC3_imp_extensive3 Sup_upper antitone_def g_from_f_def mem_Collect_eq order_trans)
end