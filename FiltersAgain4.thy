theory FiltersAgain4
  imports Main "./Posets" "./GaloisConnectionsAgain"
begin

definition is_inhabited::"'X set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

definition is_downdir::"'X::ord set \<Rightarrow> bool" where
   "is_downdir X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b)))"

definition is_upclosed::"'X::ord set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

definition is_pisystem::"'X::semilattice_inf set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"

definition is_filter::"'X::semilattice_inf set \<Rightarrow> bool" where 
  "is_filter F \<equiv> (is_pisystem F \<and> is_upclosed F \<and> is_inhabited F)"

definition filter_set::"'X::semilattice_inf set set" where
   "filter_set = {F. is_filter F}"

definition fmc::"'X::semilattice_inf set \<Rightarrow> 'X::semilattice_inf set \<Rightarrow> 'X::semilattice_inf set" where
    "fmc A B = {x. \<exists>a \<in> A. \<exists>b \<in> B. (inf a b) \<le> x}"

definition fgn::"'X::{semilattice_inf,Inf} set \<Rightarrow> 'X::{semilattice_inf,Inf} set" where
  "fgn A \<equiv> {a. \<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a}"

definition filsup::"'X::{semilattice_inf,Inf} set set \<Rightarrow> 'X::{semilattice_inf,Inf} set" where
   "filsup EF \<equiv> fgn (\<Union>EF)"


lemma fmc_iff:
  "\<forall>x. x \<in> fmc A B \<longleftrightarrow> (\<exists>a \<in> A. \<exists>b \<in> B. (inf a b) \<le> x)"
  using fmc_def by blast

lemma fmc_as0:
  "fmc A B \<subseteq> fmc B A"
proof
  fix x assume A0:"x \<in> fmc A B "
  obtain a b where A1:"(a \<in> A) \<and> (b \<in> B) \<and> ((inf a b) \<le> x)"
    by (meson A0 fmc_iff)
  have B0:"(inf b a) \<le> x"
    by (simp add: A1 inf_commute)
  show "x \<in> fmc B A"
    using A1 B0 fmc_iff by blast
qed

lemma fmc_as1:
  "fmc A B = fmc B A"
  by (simp add: fmc_as0 subset_antisym)


lemma semilatt_inf_filter_sup0:
  fixes F1::"('X::semilattice_inf set)" and
        F2::"('X::semilattice_inf set)"
  assumes A0:"is_filter F1 \<and> is_filter F2"
  shows " F1 \<subseteq> fmc F1 F2 \<and> F2 \<subseteq> fmc F1 F2"
proof-
  have P0:"F1 \<subseteq> fmc F1 F2"
  proof
    fix x assume A1:"x \<in> F1"
    have B0:"is_inhabited F2"
      using A0 FiltersAgain4.is_filter_def by auto
    obtain y where A2:"y \<in> F2"
      using A0 FiltersAgain4.is_filter_def is_inhabited_def by fastforce
    have B1:"inf x y \<le> x"
      by simp
    show "x \<in> fmc F1 F2"
      using A1 A2 B1 fmc_def by blast
  qed
  have P1:"F2 \<subseteq> fmc F1 F2"
  proof
    fix x assume A3:"x \<in> F2"
    have B0:"is_inhabited F1"
      using A0 FiltersAgain4.is_filter_def by auto
    obtain y where A2:"y \<in> F1"
      using A0 FiltersAgain4.is_filter_def is_inhabited_def by fastforce
    have B1:"inf x y \<le> x"
      by simp
    show "x \<in> fmc F1 F2"
      using A2 A3 fmc_iff by fastforce
  qed
  show ?thesis
      by (simp add: P0 P1)
qed

lemma semilatt_inf_filter_sup1:
  fixes F1::"('X::semilattice_inf set)" and
        F2::"('X::semilattice_inf set)" and
        F3::"('X::semilattice_inf set)"
  assumes A0:"is_filter F1 \<and> is_filter F2 \<and>  is_filter F3" and
          A1:"F1 \<subseteq> F3 \<and> F2 \<subseteq> F3" 
  shows "fmc F1 F2 \<subseteq> F3"
proof
  fix x assume A2:"x \<in> fmc F1 F2"
  show "x \<in> F3"
    by (meson A0 A1 A2 FiltersAgain4.is_filter_def fmc_iff is_pisystem_def is_upclosed_def subsetD)
qed

lemma semilatt_inf_filter_sup2:
  fixes F1::"('X::semilattice_inf set)" and
        F2::"('X::semilattice_inf set)"
  assumes A0:"is_filter F1 \<and> is_filter F2"
  shows "is_filter (fmc F1 F2)"
proof-
  let ?F="fmc F1 F2"
  have P0:"is_inhabited ?F"
  proof-
    have B0:"is_inhabited F1 \<and> is_inhabited F2"
      using FiltersAgain4.is_filter_def assms by auto
    obtain x y where B1:"x \<in> F1 \<and> y \<in> F2"
      using B0 is_inhabited_def by fastforce
    have B2:"inf x y \<in> ?F"
      using B1 fmc_iff by blast
    show ?thesis
      using B2 is_inhabited_def by auto
  qed
  have P1:"is_pisystem ?F"
  proof-
    have B3:"\<And>a b. (a \<in> ?F \<and>  b \<in> ?F) \<longrightarrow> (inf a b) \<in> ?F"
    proof
      fix a b assume A1:"a \<in> ?F \<and> b \<in> ?F"
      obtain a1 a2 where A2:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> inf a1 a2 \<le> a"
        by (meson A1 fmc_iff)
      obtain b1 b2 where A3:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> inf b1 b2 \<le> b"
        by (meson A1 fmc_iff)
      have B4:"inf (inf a1 a2) (inf b1 b2) = inf (inf (inf a1 b1) a2) b2"
        by (simp add: inf_commute inf_left_commute)
      have B5:"... = inf (inf a1 b1) (inf a2 b2)"
        by (simp add: inf_assoc)
      have B6:"(inf a1 b1) \<in> F1 \<and> (inf a2 b2) \<in> F2 \<and>  inf (inf a1 b1) (inf a2 b2) \<le> inf a b "
        by (metis A2 A3 B4 B5 FiltersAgain4.is_filter_def assms inf_mono is_pisystem_def)
      show "(inf a b) \<in> ?F"
        using B6 fmc_iff by blast
     qed
     show ?thesis
       by (simp add: B3 is_pisystem_def)
  qed 
  have P2:"is_upclosed ?F"
  proof-
    have P2B0:"\<And>x y. (y \<in> ?F \<and>  y \<le> x) \<longrightarrow> x \<in> ?F"
    proof
    fix x y assume P2A0:"y \<in> ?F \<and> y \<le> x"
    show "x \<in> ?F"
      by (meson P2A0 fmc_iff order.trans)
    qed
    show ?thesis
      using P2B0 is_upclosed_def by blast
  qed
  show ?thesis
    by (simp add: FiltersAgain4.is_filter_def P0 P1 P2)
qed

lemma filter_topped:
  fixes F::"'X::{semilattice_inf,order_top} set"
  assumes A0:"is_filter F"
  shows "top \<in> F"
proof-
  have B0:"is_inhabited F"
    using FiltersAgain4.is_filter_def assms by blast
  obtain x where A1:"x \<in> F"
    using B0 is_inhabited_def by fastforce
  have B1:"x \<le> top" 
    by simp
  show ?thesis
    using A1 B1 FiltersAgain4.is_filter_def assms is_upclosed_def by blast
qed
  


lemma filter_inf_is_filter:
  fixes EF::"'X::{semilattice_inf,order_top} set set"
  assumes "\<forall>F \<in> EF. is_filter F"
  shows "is_filter (\<Inter>EF)"
proof-
  let ?I="(\<Inter>EF)"
  have B0:"\<forall>F \<in> EF. top \<in> F"
    by (simp add: assms filter_topped)
  have P0:"is_inhabited ?I"
    using B0 is_inhabited_def by fastforce
  have P1:"is_pisystem ?I"
    by (meson FiltersAgain4.is_filter_def Inter_iff assms is_pisystem_def)
  have P2:"is_upclosed ?I"
    by (meson FiltersAgain4.is_filter_def Inter_iff assms is_upclosed_def)
  show ?thesis
    by (simp add: FiltersAgain4.is_filter_def P0 P1 P2)
qed


lemma filter_inf1:
  fixes EF::"'X::{semilattice_inf,order_top} set set"
  assumes "\<forall>F \<in> EF. is_filter F"
  shows "\<forall>F \<in> EF. (\<Inter>EF) \<subseteq> F"
  by auto

lemma filter_inf2:
  fixes EF::"'X::{semilattice_inf,order_top} set set" and
        H::"'X::{semilattice_inf,order_top} set"
  assumes A0:"\<forall>F \<in> EF. is_filter F" and 
          A1:"is_filter H" and
          A2:"\<forall>F \<in> EF. H \<subseteq> F"
  shows "H \<subseteq> (\<Inter>EF)"
  by (simp add: A2 Inter_greatest)

lemma filter_sup_is_filter:
  fixes EF::"'X::{semilattice_inf,Inf} set set"
  assumes A0:"\<forall>F \<in> EF. is_filter F" and
          A1:"EF \<noteq> {}" and
          Inf_lower:"\<And>(x::'X::{semilattice_inf,Inf}) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
          Inf_grlow:"\<And>z A. (\<And>(x::'X::{semilattice_inf,Inf}). x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" 
  shows "is_filter (filsup EF)"
proof-
  let ?U="\<Union>EF"
  let ?S="filsup EF"
  have P0:"is_inhabited ?S"
  proof-
    have P00:"\<forall>F \<in> EF. is_inhabited F"
      using A0 FiltersAgain4.is_filter_def by auto
    obtain F where P0A0:"F \<in> EF"
      using A1 by auto
    obtain x where P0A1:"x \<in> F"
      using A0 FiltersAgain4.is_filter_def P0A0 is_inhabited_def by fastforce
    have P0B0:"Inf {x} \<le> x"
      by (simp add: local.Inf_lower)
    have P0B1:"{x} \<in> Pow((\<Union>EF))"
      using P0A0 P0A1 by blast
    have B0B2:"finite {x}"
      by simp
    have P0B3:"x \<in> ?S"
      by (smt (verit) B0B2 P0B0 P0B1 empty_not_insert fgn_def filsup_def mem_Collect_eq)
    show ?thesis
      using P0B3 is_inhabited_def by auto
  qed
  have P1:"is_pisystem ?S"
  proof-
    have B3:"\<And>a b. (a \<in> ?S \<and>  b \<in> ?S) \<longrightarrow> (inf a b) \<in> ?S"
    proof
      fix a b assume B3A0:"a \<in> ?S \<and>  b \<in> ?S"
      obtain Ea where B3A1:"Ea \<in> Pow(?U) \<and> Ea \<noteq> {} \<and> finite Ea \<and> (Inf Ea) \<le> a"
        by (smt (verit) B3A0 fgn_def filsup_def mem_Collect_eq)
      obtain Eb where B3A2:"Eb \<in> Pow(?U) \<and> Eb \<noteq> {} \<and> finite Eb \<and> (Inf Eb) \<le> b"
        by (smt (verit) B3A0 fgn_def filsup_def mem_Collect_eq)
      have B30:"Inf (Ea \<union> Eb) \<le> a"
        by (meson B3A1 Inf_grlow UnI1 dual_order.trans local.Inf_lower)
      have B31:"Inf (Ea \<union> Eb) \<le> b"
        by (meson B3A2 Inf_grlow UnCI dual_order.trans local.Inf_lower)
      have B32:"Inf (Ea \<union> Eb) \<le> inf a b"
        by (simp add: B30 B31)
      let ?Ec="Ea \<union> Eb"
      have B33:"?Ec \<in> Pow(?U) \<and> ?Ec \<noteq> {} \<and> finite ?Ec \<and> (Inf ?Ec) \<le> (inf a b)"
        using B32 B3A1 B3A2 by blast
      show "(inf a b) \<in> ?S"
        by (smt (verit) B33 fgn_def filsup_def mem_Collect_eq)
    qed
    show ?thesis
      by (simp add: B3 is_pisystem_def)
   qed
   have P2:"is_upclosed ?S"
     by (smt (verit, del_insts) dual_order.trans fgn_def filsup_def is_upclosed_def mem_Collect_eq)
   show ?thesis
     by (simp add: FiltersAgain4.is_filter_def P0 P1 P2)
qed
    
lemma filter_sup_is_upper:
  fixes EF::"'X::{semilattice_inf,Inf} set set"
  assumes A0:"\<forall>F \<in> EF. is_filter F" and
          A1:"EF \<noteq> {}" and
          Inf_lower:"\<And>(x::'X::{semilattice_inf,Inf}) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
          Inf_grlow:"\<And>z A. (\<And>(x::'X::{semilattice_inf,Inf}). x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" 
  shows "\<forall>F \<in> EF. F \<subseteq> filsup EF"
proof
  fix F assume A2:"F \<in> EF"
  show "F \<subseteq> filsup EF"
  proof 
    fix x assume A3:"x \<in> F"
    have P0B0:"Inf {x} \<le> x"
      by (simp add: local.Inf_lower)
    have P0B1:"{x} \<in> Pow((\<Union>EF))"
      using A2 A3 by blast
    have B0B2:"finite {x}"
      by simp
    show "x \<in> filsup EF"
      by (smt (verit) B0B2 P0B0 P0B1 empty_iff fgn_def filsup_def mem_Collect_eq singletonI)
  qed
qed



lemma finite_join_in_set:
  fixes C::"'X::{semilattice_inf,Inf} set"
  assumes Inf_lower:"\<And>(x::'X::{semilattice_inf,Inf}) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
          Inf_grlow:"\<And>z A. (\<And>(x::'X::{semilattice_inf,Inf}). x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" and
          A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (inf a1 a2) \<in> C"and 
          A3:"finite E" and A4:"E \<noteq> {}" and A5:"E \<subseteq> C"
  shows "(Inf E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x) with assms show ?case
      by (metis Inf_fin.coboundedI Inf_fin.singleton dual_order.eq_iff finite.emptyI finite_insert insert_subset)
    next case (insert x F)
    then have "(Inf (insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C" using insert.prems by auto
      have P1: "F \<subseteq> C" using insert.prems by auto
      with A2 have P2:"inf x (Inf F) \<in> C" by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(Inf F) \<in> C" using P1 by blast
      have P4:"Inf (insert x F) = inf x (Inf F)"
      proof-
        have B0:"Inf (insert x F) \<le>  (Inf F)"
          by (simp add: Inf_grlow local.Inf_lower)
        have B1:"inf x (Inf F) = Inf {x, Inf F}"
        proof-
          have "Inf {x, Inf F} \<le> x"
            by (simp add: local.Inf_lower)
          have "Inf {x, Inf F} \<le> Inf F"
            by (simp add: local.Inf_lower)
          have "inf x (Inf F) \<le> x"
            by simp
          have "inf x (Inf F) \<le> Inf F"
            by simp
          have "Inf {x, Inf F} \<le> inf x (Inf F)"
            by (simp add: \<open>Inf {x::'X, Inf (F::'X set)} \<le> Inf F\<close> \<open>Inf {x::'X, Inf (F::'X set)} \<le> x\<close>)
          have "Inf {x, Inf F} \<ge> inf x (Inf F)"
            using Inf_grlow by fastforce
          show ?thesis
            using \<open>Inf {x::'X, Inf (F::'X set)} \<le> inf x (Inf F)\<close> \<open>inf (x::'X) (Inf (F::'X set)) \<le> Inf {x, Inf F}\<close> order_antisym_conv by blast
        qed
        have "Inf {x, Inf F} = Inf (insert x F)"
        proof-
          have "\<forall>y \<in> (insert x F). Inf {x, Inf F} \<le> y"
            by (metis B1 inf.coboundedI2 insert_iff local.Inf_lower)
          have "\<forall>y \<in>  (insert x F).  Inf (insert x F) \<le> y"
            by (simp add: local.Inf_lower)
          show ?thesis
            by (metis B0 B1 Inf_grlow \<open>\<forall>y::'X\<in>insert (x::'X) (F::'X set). Inf {x, Inf F} \<le> y\<close> antisym_conv insertI1 le_inf_iff local.Inf_lower)
        qed
        show ?thesis
          by (simp add: B1 \<open>Inf {x::'X, Inf (F::'X set)} = Inf (insert x F)\<close>)
      qed
      then show "(Inf (insert x F)) \<in> C"  by (simp add: P2)
    qed
    show ?case
      using \<open>Inf (insert x F) \<in> C\<close> by auto
  qed
qed


lemma filter_sup_is_least_upper:
  fixes EF::"'X::{semilattice_inf,Inf} set set" and
         H::"'X::{semilattice_inf,Inf} set"
  assumes A0:"\<forall>F \<in> EF. is_filter F" and
          A1:"EF \<noteq> {}" and
          A2:"is_filter H" and
          A3:"\<forall>F \<in> EF. F \<subseteq> H" and
          Inf_lower:"\<And>(x::'X::{semilattice_inf,Inf}) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
          Inf_grlow:"\<And>z A. (\<And>(x::'X::{semilattice_inf,Inf}). x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"        
  shows "filsup EF \<subseteq> H"
proof
  fix x assume A4:"x \<in> filsup EF" 
  obtain Ex where A5:"Ex \<in> Pow(\<Union>EF) \<and> Ex \<noteq> {} \<and> finite Ex \<and> (Inf Ex) \<le> x"
    by (smt (verit) A4 fgn_def filsup_def mem_Collect_eq) 
  have B0:"Ex \<subseteq> \<Union>EF"
    using A5 by blast
  have B1:"... \<subseteq> H"
    by (simp add: A3 Sup_le_iff)
  
  show "x \<in> H"

(*
locale filter_of_sets = 
  fixes EF::"'X set set set"
  assumes "\<forall>F \<in> EF. is_filter F"
begin

definition Inf::"'X set set set \<Rightarrow> 'X set set"
  where "Inf ES = (\<Inter>ES)"

definition Sup::"'X set set set \<Rightarrow> 'X set set"
  where "Sup ES = (fgenby ES)"

definition inf::"'X set set \<Rightarrow> 'X set set \<Rightarrow> 'X set set" where
  "inf F1 F2 = Inf {F1, F2}"

definition sup::"'X set set \<Rightarrow> 'X set set \<Rightarrow> 'X set set" where
  "sup F1 F2 = Sup {F1, F2}"

definition top::"'X set set" where
  "top = Pow UNIV"

definition bot::"'X set set" where
  "bot = {UNIV}"

lemma sup_gt:
  assumes "\<forall>F \<in> ES. is_filter F"
  shows "\<forall>F \<in> ES. F \<subseteq> (fgenby ES)"
  by (metis Sup_le_iff filter_generated_by_def order_trans pfmc_extensive upc_extensive)

lemma inf_eq:
  "inf F1 F2 = F1 \<inter> F2"
  by (simp add: Inf_def inf_def)

lemma fgen_extensive:
  "\<forall>ES. \<forall>F \<in> ES. F \<subseteq> fgenby ES"
  by (metis Sup_le_iff filter_generated_by_def order_trans pfmc_extensive upc_extensive)

lemma fgen_sup:
  fixes ES
  assumes A0:"is_filter G" and A1:"\<forall>F \<in> ES. is_filter F" and A2:"(\<forall>F \<in> ES. F \<subseteq> G)"
  shows "(fgenby ES) \<subseteq> G"
proof(cases " ES \<noteq> {} \<and> ES \<noteq> {{}}")
  case True
  then show ?thesis
  proof-
  have th:"\<forall>a \<in> (fgenby ES). a \<in> G"
  proof
  let ?UN="(\<Union>ES)"
  fix a assume LtR_A0:"a \<in> (fgenby ES)"
  have LtR_A00:"a \<in> upclosure(pfmc ?UN)"
    using LtR_A0 filter_generated_by_def by blast
  obtain b where LtR_A1:"b \<in> (pfmc ?UN) \<and> a \<supseteq> b "
    by (metis LtR_A0 filter_generated_by_def in_upclosure_imp)
  obtain F where LtR_A2:"(F \<in> Pow(?UN)) \<and> (finite F) \<and> b=(\<Inter>F)"
    by (smt (verit, ccfv_threshold) CollectD LtR_A1 proper_finite_meet_closure_def)
  have LtR_B0:"F \<subseteq> ?UN" using LtR_A2 by blast
  have LtR_B1:"\<forall>f \<in> F. \<exists>E \<in> ES. f \<in> E"
    using LtR_B0 by auto
  have LtR_B2:"\<forall>f \<in> F.  f \<in> G"
    using A2 LtR_B1 by fastforce
  have LtR_B3:"F \<subseteq> G"
    by (simp add: LtR_B2 subsetI)
  have LtR_B4:"(\<Inter>F) \<in> G"
    by (metis A0 Inter_empty LtR_A2 LtR_B3 filter_iff_pisystem_with_univ finite_intersections_in_set is_pisystem_def)
  have LtR_B5:"(\<Inter>F) =b"
    by (simp add: LtR_A2)
  have LtR_B6:"... \<subseteq> a" 
    by (simp add: LtR_A1)
  show "a \<in> G"
    using A0 FiltersAgain3.is_filter_def LtR_B4 LtR_B5 LtR_B6 is_upclosed_def by blast
  qed
  show ?thesis
    by (simp add: subsetI th)
  qed
next
  case False
  then show ?thesis
    by (smt (verit) A1 CollectD FiltersAgain3.is_filter_def Union_Pow_eq all_not_in_conv empty_Union_conv empty_subsetI filter_generated_by_def insertI1 is_inhabited_def proper_finite_meet_closure_def upclosure_def)
qed

lemma fgen_sup2:
  assumes A0:"is_filter G \<and> is_filter F1 \<and> is_filter F2" and A1:"F1 \<subseteq> G \<and> F2 \<subseteq> G"
  shows "(fgenby {F1, F2}) \<subseteq> G"
  by (simp add: A0 A1 fgen_sup)

lemma fgen_sup3:
  assumes A0:"is_filter G \<and> is_filter F1 \<and> is_filter F2" and A1:"F1 \<subseteq> G \<and> F2 \<subseteq> G"
  shows "(sup F1 F2) \<subseteq> G"
  by (simp add: A0 A1 Sup_def fgen_sup2 sup_def)
                    



end

sublocale filter_of_sets \<subseteq> complete_lattice filter_of_sets.Inf
                                             filter_of_sets.Sup
                                             filter_of_sets.inf
                                             "(\<subseteq>)" "(\<subset>)"
                                             filter_of_sets.sup
                                             filter_of_sets.bot
                                             filter_of_sets.top
proof unfold_locales
fix x::"'a set set" fix y::"'a set set"
show "filter_of_sets.inf x y \<subseteq> x"
  by (metis Inter_lower equals0D filter_of_sets.Inf_def filter_of_sets.inf_def filter_of_sets.intro insertI1)
show "filter_of_sets.inf x y \<subseteq> y"
  by (metis Inter_lower empty_iff filter_of_sets.Inf_def filter_of_sets.inf_def filter_of_sets.intro insert_iff)
show "x \<subseteq> filter_of_sets.sup x y"
  by (metis Sup_insert Un_subset_iff empty_iff filter_generated_by_def filter_of_sets.Sup_def filter_of_sets.intro filter_of_sets.sup_def pfmc_extensive sup.orderE upc_extensive)
show "y \<subseteq> filter_of_sets.sup x y"
  by (metis (no_types, opaque_lifting) Sup_insert Un_subset_iff empty_iff filter_generated_by_def filter_of_sets.Sup_def filter_of_sets.intro filter_of_sets.sup_def pfmc_extensive sup.orderE upc_extensive)
fix z::"'a set set"
show "x \<subseteq> y \<Longrightarrow> x \<subseteq> z \<Longrightarrow> x \<subseteq> filter_of_sets.inf y z"
  by (metis Int_subset_iff empty_iff filter_of_sets.inf_eq filter_of_sets.intro)
show "y \<subseteq> x \<Longrightarrow> z \<subseteq> x \<Longrightarrow> filter_of_sets.sup y z \<subseteq> x"

end
*)
end