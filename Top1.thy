theory Top1
  imports Main "./PartialOrders" "./FiltersAgain14"
begin

definition is_cup_closed_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_cup_closed_in A X \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> (\<Union>E) \<in> A)"

definition is_fcap_closed_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_fcap_closed_in A X \<equiv> (\<forall>E. E \<subseteq> A \<and> finite E \<longrightarrow> (\<Inter>E) \<in> A)"

definition is_topology_on::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "is_topology_on T X \<equiv> (X \<in> T) \<and> ({} \<in>  T) \<and>  (is_cup_closed_in T X ) \<and>  (is_fcap_closed_in T X)"

definition is_nhood_system::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_nhood_system N X \<equiv> (\<forall>x \<in> X. (\<forall>V \<in> N x. x \<in> V) \<and> is_pfilter (N x) \<and> 
                          (\<forall>V \<in> N x. \<exists>W \<in> N x.  W \<subseteq> X \<and> (\<forall>y \<in> W. V \<in> N y)) \<and> 
                          (\<forall>x \<in> X. N x \<in> Pow (Pow X)) \<and>
                          (\<forall>x. x\<notin> X \<longrightarrow> N x = undefined )) \<and>
                          X \<noteq> {}"


definition is_topology_on2::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "is_topology_on2 T X \<equiv> (T \<in> Pow(Pow X)) \<and> (X \<in> T) \<and> ({} \<in>  T) \<and>  (is_cup_closed_in T X ) \<and>  (is_fcap_closed_in T X)"


definition topologies_on::"'a set \<Rightarrow> 'a set set set" where
  "topologies_on X \<equiv> {T. is_topology_on T X}"

definition topology_generated_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_in E X = (SupIn {E} (topologies_on X))"

definition nhoods_of::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "nhoods_of x T X \<equiv> {V.  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V)}"

definition top_from_nhoods::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "top_from_nhoods N X \<equiv> {V. (\<forall>x \<in> V. V \<in> N x)}"

definition nhoods_from_top::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set set)" where
  "nhoods_from_top T X \<equiv> (\<lambda>x. {V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V})"

definition nhoods_from_top2::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set set)" where
  "nhoods_from_top2 T X \<equiv> (\<lambda>x. if x \<in> X then {V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V} else undefined)"

definition top_from_nhoods2::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "top_from_nhoods2 N X \<equiv> {V \<in> Pow X. (\<forall>x \<in> V. V \<in> N x)}"


lemma topologies_on_mem_iff:
  "\<And>T. T \<in> topologies_on X \<longleftrightarrow> is_topology_on T X"
  by (simp add: topologies_on_def)

lemma nhoods_of_mem_iff:
  "\<And>N. N \<in> nhoods_of x T X \<longleftrightarrow> (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (simp add: nhoods_of_def)

lemma nhoods_of_imp2:
  "\<And>N. N \<in> nhoods_of x T X \<Longrightarrow> x \<in> N"
  by (meson in_mono nhoods_of_mem_iff)

lemma nhoods_of_imp3:
  "\<And>N. N \<in> nhoods_of x T X \<Longrightarrow>  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (meson in_mono nhoods_of_mem_iff)

lemma top_from_nhoods2_mem_imp:
  "\<And>V. V \<in> top_from_nhoods2 N X \<Longrightarrow>  V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
  by (simp add: top_from_nhoods2_def)

lemma nhoods_from_top2_mem_imp:
  "\<And>V x. x \<in> X \<Longrightarrow> V \<in> nhoods_from_top2 T X x \<Longrightarrow>  (\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V)"
  by (simp add: nhoods_from_top2_def)



lemma is_fcap_closedb:
  fixes A::"'a set set"
  assumes A0:"is_fcap_closed_in A X"
  shows "\<And>x1 x2. (x1 \<in> A \<and> x2 \<in> A) \<Longrightarrow> x1 \<inter> x2 \<in> A"
proof-
  fix x1 x2 assume A1:"x1 \<in> A \<and> x2 \<in> A"
  have B0:"{x1, x2} \<subseteq> A"
    by (simp add: A1)
  have B1:"finite {x1, x2}"
    by simp
  have B2:"\<Inter>{x1, x2} = x1 \<inter> x2"
    by simp
  show "x1 \<inter> x2 \<in> A"
    by (metis B0 B1 B2 assms is_fcap_closed_in_def)
qed


lemma nhoods_is_pfilter:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on T X" and A1:"x \<in> X"
  shows "is_pfilter (nhoods_of x T X)"
proof-
  let ?Nx="(nhoods_of x T X)"
  have B0:"is_proper ?Nx"
    by (metis Set.set_insert UNIV_I is_proper_def nhoods_of_imp2)
  have B1:"is_downdir ?Nx"
  proof-
    have B10:"\<And>a b. (a \<in> ?Nx \<and> b \<in> ?Nx) \<longrightarrow> (\<exists>c  \<in> ?Nx. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix Va Vb assume A2:"(Va \<in> ?Nx \<and> Vb \<in> ?Nx)"
      obtain Ua where A3:"Ua \<in> T \<and> x \<in> Ua \<and> Ua \<subseteq> Va"
        by (meson A2 nhoods_of_imp3)
      obtain Ub where A4:"Ub \<in> T \<and> x \<in> Ub \<and> Ub \<subseteq> Vb"
        by (meson A2 nhoods_of_imp3)
      have B11:"Ua \<inter> Ub \<in> T"
        using A0 A3 A4 is_fcap_closedb is_topology_on_def by blast
      have B12:"Ua \<inter> Ub \<in> T \<and> x \<in> Ua \<inter> Ub \<and> Ua \<inter> Ub \<subseteq> Va \<and> Ua \<inter> Ub \<subseteq> Vb"
        by (simp add: A3 A4 B11 inf.coboundedI1 inf.coboundedI2)
      show "(\<exists>c  \<in> ?Nx. (c \<le> Va) \<and>  (c \<le> Vb))"
        by (meson A2 B12 Pow_iff nhoods_of_mem_iff order_refl subset_trans)
    qed
    show ?thesis
      by (simp add: B10 is_downdir_def)
  qed
  have B2:"is_upclosed ?Nx"
  proof-
    have B20:"\<And>a b. (a \<le> b \<and>  a \<in> ?Nx) \<longrightarrow>  b \<in> ?Nx"
    proof
      fix Va Vb assume A5:"Va \<le> Vb \<and> Va \<in> ?Nx"
      obtain Ua where A6:"Ua \<in> T \<and> x \<in> Ua \<and> Ua \<subseteq> Va"
        by (meson A5 nhoods_of_imp3)
      have B21:"Ua \<subseteq> Vb"
        using A5 A6 by auto
      show "Vb \<in> ?Nx"
        by (meson A5 dual_order.trans nhoods_of_mem_iff)
    qed
   show ?thesis
     by (meson B20 is_upclosed_def)
  qed
  have B3:"is_inhabited ?Nx"
    by (metis A0 A1 empty_iff is_inhabited_def is_topology_on_def nhoods_of_mem_iff order_refl)
  show ?thesis
    by (simp add: B0 B1 B2 B3 PartialOrders.is_filter_def is_pfilter_def)
qed

lemma top_from_nhoods_inv:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on T X"
  shows "top_from_nhoods (nhoods_from_top T X) X = T" (is "?L = ?R")
proof-
  define N where "N= (nhoods_from_top T X)"
  have B0:"\<And>V. V \<in> ?L \<longleftrightarrow> V \<in> ?R"
  proof
    fix V assume A1:"V \<in> ?L"
    have B01:"(\<forall>x \<in> V. V \<in> N x)"
      using A1 N_def top_from_nhoods_def by force
    have B02:"\<forall>x \<in> V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
      by (smt (verit) B01 N_def mem_Collect_eq nhoods_from_top_def)
    define F where "F=(\<lambda>x. (SOME U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V))"
    have B03:"\<forall>x \<in> V. F x \<in> T \<and> x \<in> (F x) \<and> (F x) \<subseteq> V"
      by (metis (mono_tags, lifting) B02 F_def someI)
    have B04:"\<Union>(F`V) \<subseteq> V"
      using B03 by blast
    have B05:"\<Union>(F`V) \<supseteq> V"
      using B03 by blast
    have B06:"\<Union>(F`V) =V"
      using B04 B05 by blast
    have B07:"\<forall>U \<in> (F`V). U \<in> T"
      using B03 by blast
    have B08:"V \<in> T"
      by (metis A0 B06 B07 is_cup_closed_in_def is_topology_on_def subsetI)
    show "V \<in> ?R"
      by (simp add: B08)
   next
    fix V assume A1:"V \<in> ?R"
    show "V \<in> ?L"
      by (smt (verit, del_insts) A1 mem_Collect_eq nhoods_from_top_def order_refl top_from_nhoods_def)
  qed
  show ?thesis
    using B0 by blast
qed


lemma top_from_nhoods_inv2:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on2 T X"
  shows "top_from_nhoods2 (nhoods_from_top2 T X) X = T" (is "?L = ?R")
proof-
  define N where "N= (nhoods_from_top2 T X)"
  have B0:"?L \<subseteq> ?R"
  proof
    fix V assume A1:"V \<in> ?L"
    have B01:"V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
      by (metis (mono_tags, lifting) A1 CollectD N_def top_from_nhoods2_def)
    have B02:"\<forall>x \<in> V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
      by (metis A1 Pow_iff nhoods_from_top2_mem_imp subsetD top_from_nhoods2_mem_imp)
    define F where "F=(\<lambda>x. (SOME U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V))"
    have B03:"\<forall>x \<in> V. F x \<in> T \<and> x \<in> (F x) \<and> (F x) \<subseteq> V"
      by (metis (mono_tags, lifting) B02 F_def someI)
    have B04:"\<Union>(F`V) \<subseteq> V"
      using B03 by blast
    have B05:"\<Union>(F`V) \<supseteq> V"
      using B03 by blast
    have B06:"\<Union>(F`V) =V"
      using B04 B05 by blast
    have B07:"\<forall>U \<in> (F`V). U \<in> T"
      using B03 by blast
    have B08:"V \<in> T"
      by (metis B06 B07 assms is_cup_closed_in_def is_topology_on2_def subsetI)
    show "V \<in> ?R"
      by (simp add: B08)
  qed
  have B1:"?R \<subseteq> ?L"
  proof
    fix V assume A1:"V \<in> ?R"
    have B10:"V \<subseteq> X"
      by (meson A1 PowD assms in_mono is_topology_on2_def)
    show "V \<in> ?L"
    proof(cases "V = {}")
      case True
      then show ?thesis
        by (simp add: top_from_nhoods2_def)
    next
      case False
      obtain x where A2:"x \<in> V"
        using False by blast
      have B11:"\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
        using A1 A2 by blast
      then show ?thesis
        by (smt (verit, ccfv_threshold) A1 B10 CollectI PowI nhoods_from_top2_def subset_iff top_from_nhoods2_def)
    qed
  qed
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed

lemma nhoods_from_top_inv2:
  fixes X::"'a set" and N::"('a \<Rightarrow> 'a set set)" and x::"'a"
  assumes A0:"is_nhood_system N X" and A1:"x \<in> X"
  shows "(nhoods_from_top2 (top_from_nhoods2 N X) X)(x) = N(x)"
proof-
  define T where A2:"T=top_from_nhoods2 N X"
  define L where "L=(nhoods_from_top2 (top_from_nhoods2 N X) X)"
  have B0:"\<And>V. V \<in> L x \<longrightarrow> V \<in> N x"
  proof
    fix V assume A3:"V \<in> L x"
    obtain U where B1:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (metis A1 A2 A3 L_def nhoods_from_top2_mem_imp)
    have B2:" (\<forall>y \<in> U. U \<in> N y)"
      using A2 B1 top_from_nhoods2_mem_imp by blast
    have B3:"U \<in> N x"
      by (simp add: B1 B2)
    have B4:"U \<subseteq> V"
      by (simp add: B1)
    have B5:"is_pfilter (N x)"
      using A2 assms is_nhood_system_def by fastforce
    have B6:"V \<in> N x"
      using B1 B3 B5 is_filter_def is_pfilter_def is_upclosed_imp by blast
    show "V \<in> N x"
        by (simp add: B6)
  qed
  have B7:"\<And>V. V \<in> N x \<longrightarrow> V \<in> L x"
  proof
    fix V assume A4:"V \<in> N x"
    define U where A5:"U={y \<in> X. V \<in> N y}"
    have B7:"x \<in> U"
      by (smt (verit, del_insts) A2 A4 A5 CollectD CollectI L_def is_filter_def assms is_nhood_system_def is_pfilter_def is_upclosed_imp nhoods_from_top_def top_from_nhoods_def)
    have B8:"U \<subseteq> V"
      using A0 A5 is_nhood_system_def by fastforce
    have B9:"(\<And>y. y \<in> U \<longrightarrow> U \<in> N y)"
      proof
        fix y assume A6:"y \<in> U"
        obtain W where A7:"W \<in> N y \<and>  W \<subseteq> X \<and> (\<forall>z \<in> W.  V \<in> N z)"
          by (smt (verit) A0 A5 A6 CollectD is_nhood_system_def)
        have B10:"W \<subseteq> U"
          using A5 A7 by blast
        have B110:"W \<in> N y \<and> is_filter(N y) \<and> W \<subseteq> U "
          by (metis (no_types, lifting) A0 A5 A6 A7 B10 CollectD is_nhood_system_def is_pfilter_def)
        have B11:"U \<in> N y"
          using B110 is_filter_def is_upclosed_imp by blast
        show "U \<in> N y"
          using B11 by force
      qed
    have B120:"U \<in> Pow X \<and> (\<forall>u \<in> U.  V \<in> N u)"
      using A5 by blast
    have B121:"U \<in> T"
      using A2 B120 B9 top_from_nhoods2_def by force
    have B122:"x \<in> U \<and> U \<subseteq> V"
      by (simp add: B7 B8)
    have B12:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (simp add: B121 B122)
    show "V \<in> L x"
      by (metis (no_types, lifting) A1 A2 B12 CollectI L_def nhoods_from_top2_def)
  qed
  show ?thesis
    using B0 B7 L_def by blast
qed
  
lemma nhoods_from_top_inv0:
  fixes X::"'a set" and N::"('a \<Rightarrow> 'a set set)" and x::"'a"
  assumes A0:"is_nhood_system N X" and A1:"x \<in> X"
  shows "(nhoods_from_top (top_from_nhoods N X) X)(x) = N(x)"
proof-
  define T where A2:"T=top_from_nhoods N X"
  define L where "L=(nhoods_from_top (top_from_nhoods N X) X)"
  have B0:"\<And>V. V \<in> L x \<longrightarrow> V \<in> N x"
  proof
    fix V assume A3:"V \<in> L x"
    obtain U where B1:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
     by (smt (verit, best) A2 A3 L_def mem_Collect_eq nhoods_from_top_def)
    have B2:" (\<forall>y \<in> U. U \<in> N y)"
      using A2 B1 top_from_nhoods_def by fastforce
    have B3:"U \<in> N x"
      by (simp add: B1 B2)
    have B4:"U \<subseteq> V"
      by (simp add: B1)
    have B5:"is_pfilter (N x)"
      using A2 assms is_nhood_system_def by fastforce
    have B6:"V \<in> N x"
      using B1 B3 B5 is_filter_def is_pfilter_def is_upclosed_imp by blast
    show "V \<in> N x"
        by (simp add: B6)
  qed
  have B7:"\<And>V. V \<in> N x \<longrightarrow> V \<in> L x"
  proof
    fix V assume A4:"V \<in> N x"
    define U where A5:"U={y \<in> X. V \<in> N y}"
    have B7:"x \<in> U"
      by (smt (verit, del_insts) A2 A4 A5 CollectD CollectI L_def is_filter_def assms is_nhood_system_def is_pfilter_def is_upclosed_imp nhoods_from_top_def top_from_nhoods_def)
    have B8:"U \<subseteq> V"
      using A0 A5 is_nhood_system_def by fastforce
    have B9:"(\<And>y. y \<in> U \<longrightarrow> U \<in> N y)"
    proof
      fix y assume A6:"y \<in> U"
      obtain W where A7:"W \<in> N y \<and>  W \<subseteq> X \<and> (\<forall>z \<in> W.  V \<in> N z)"
        by (smt (verit) A0 A5 A6 CollectD is_nhood_system_def)
      have B10:"W \<subseteq> U"
        using A5 A7 by blast
      have B11:"U \<in> N y"
        by (metis A0 A5 A6 A7 B10 CollectD is_filter_def is_nhood_system_def is_pfilter_def is_upclosed_imp)
      show "U \<in> N y"
        using B11 by force
    qed
    have B12:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (simp add: A2 B7 B8 B9 top_from_nhoods_def)
    show "V \<in> L x"
      by (metis (no_types, lifting) A2 B12 CollectI L_def nhoods_from_top_def)
  qed
  show ?thesis
    using B0 B7 L_def by blast
qed
  
                                                         
end