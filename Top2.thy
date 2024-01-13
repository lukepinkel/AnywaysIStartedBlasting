theory Top2
  imports Main "./PartialOrders" "./FiltersAgain14"
begin


definition top_u1::"'a set set \<Rightarrow> bool" where
  "top_u1 T \<equiv> (\<forall>E. E \<subseteq> T \<longrightarrow> \<Union>E \<in> T )"

(*top_i1 cannot work for the local definition as \<Inter>\<emptyset> is interpreted as InfIn \<emptyset> UNIV = UNIV so 
  thats one choice out of the way
*)

definition top_i1::"'a set set \<Rightarrow> bool" where
  "top_i1 T \<equiv> (\<forall>E. (finite E \<and> E \<subseteq> T) \<longrightarrow> \<Inter>E \<in> T )"

definition top_i2::"'a set set \<Rightarrow> bool" where
  "top_i2 T \<equiv> (\<forall>E. (finite E \<and> E \<subseteq> T \<and> E \<noteq> {}) \<longrightarrow> \<Inter>E \<in> T )"

definition top_i3::"'a set set \<Rightarrow> bool" where
  "top_i3 T \<equiv> (\<forall>a1 a2. (a1 \<in> T \<and> a2 \<in> T) \<longrightarrow> a1 \<inter> a2 \<in> T)"

definition is_base1_for_topology::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_base1_for_topology B T \<equiv> B \<subseteq> T \<and> (\<forall>U \<in>T.  (\<exists>E \<in> Pow B. U=\<Union>E))"

definition is_base2_for_topology::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_base2_for_topology B T \<equiv> (B \<subseteq> T) \<and> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U))"

definition is_base_3_covering::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base_3_covering B X \<equiv>   (B \<in> Dpow X) \<and> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"

definition is_base_3_intercont::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base_3_intercont B X \<equiv> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"

definition is_base3_for_topology::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base3_for_topology B X \<equiv> is_base_3_covering B X \<and> is_base_3_intercont B X"


definition basis_element_int_npt::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a  \<Rightarrow> 'a set)" where
  "basis_element_int_npt B X \<equiv>  \<lambda>U1 U2 x. SOME U3. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2 \<and>  U3 \<in> B"

definition basis_element_npt::"'a set set \<Rightarrow>  ('a set \<Rightarrow> 'a  \<Rightarrow> 'a set)" where
  "basis_element_npt B \<equiv>  \<lambda>U x. SOME B3. (x \<in> B3) \<and> (B3 \<subseteq> U) \<and>  (B3 \<in> B)"

definition basis_element_pt::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a  \<Rightarrow> 'a set)" where
  "basis_element_pt B X \<equiv>  \<lambda>x. SOME B3. x \<in> B3 \<and>  B3 \<in> B"


definition is_nhood_system_in::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_nhood_system_in N X \<equiv> (\<forall>x. is_pfilter_in (N x) X \<and>
                             (\<forall>V \<in> N x. x \<in> V \<and> 
                               (\<exists>W \<in> N x. (\<forall>y \<in> W. V \<in> N y))))"

definition is_topology_on::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "is_topology_on T X \<equiv> (T \<in> Dpow X) \<and> (top_u1 T) \<and> (top_i3 T) \<and> (X \<in> T)"


definition top_from_nhoods::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "top_from_nhoods N X \<equiv> {V \<in> Pow X. (\<forall>x \<in> V. V \<in> N x)}"

definition nhoods_of::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "nhoods_of x T X \<equiv> {V.  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V)}"

definition topologies_on::"'a set \<Rightarrow> 'a set set set" where
  "topologies_on X \<equiv> {T. is_topology_on T X}"

definition finer_topologies::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set set" where
  "finer_topologies E X \<equiv> {T. is_topology_on T X \<and> E \<subseteq> T}"

definition topology_generated_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_in E X \<equiv> (SupIn {E} (topologies_on X))"


definition topology_generated_by_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_by_in E X \<equiv> \<Inter>(finer_topologies E X)"


definition top_sup1::"'a set set set \<Rightarrow>'a set \<Rightarrow> 'a set set" where
  "top_sup1 ET X \<equiv> topology_generated_in (\<Union>ET) X"

definition top_sup2::"'a set set set \<Rightarrow>'a set \<Rightarrow> 'a set set" where
  "top_sup2 ET X \<equiv> (\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T})"


definition nhoods_from_top::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set set)" where
  "nhoods_from_top T X \<equiv> (\<lambda>x. if x \<in> X then {V \<in> Pow X. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V} else undefined)"

definition nhood_base_from_base::"'a set set \<Rightarrow> 'a set \<Rightarrow>  ('a \<Rightarrow> 'a set set)" where
  "nhood_base_from_base B X \<equiv> (\<lambda>x. if x \<in> X then {Bx \<in> B. x \<in> Bx} else undefined)"

definition is_nhood_base::"('a \<Rightarrow> 'a set set) \<Rightarrow> ('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_nhood_base B N X \<equiv>  (\<forall>x \<in> X. \<forall>V \<in> N x. \<exists>b\<in> B x.  x \<in> b \<and> b \<subseteq> V)"

definition cofinite_sets_in::"'a set \<Rightarrow> 'a set set" where
  "cofinite_sets_in X \<equiv> {U. U \<in> Pow X \<and>  (finite (X - U) \<or> U={})}"

definition cocountable_sets_in::"'a set \<Rightarrow> 'a set set" where
  "cocountable_sets_in X \<equiv> {U. U \<in> Pow X \<and>  (is_countable (X - U) \<or> U={})}"

definition particular_point_top::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "particular_point_top a X \<equiv> {U. U \<in> Pow X \<and>  ((a \<in> U) \<or> U={})}"

definition excluded_point_top::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "excluded_point_top a X \<equiv> {U. U \<in> Pow X \<and>  a \<notin>  U \<or> U=X}"


lemma top_u1_imp_contains_empty:
  "\<And>T. top_u1 T \<Longrightarrow> {} \<in> T"
  by (metis Sup_empty empty_subsetI top_u1_def)

lemma top_i1_imp_contains_carrier:
  "\<And>T. top_i1 T \<Longrightarrow> UNIV \<in> T"
  using top_i1_def by force


lemma top_i3_induct:
  assumes A0:"top_i3 T" and A1:"finite E" and A2:"E \<noteq> {}" and A3:"E \<subseteq> T"
  shows "(\<Inter>E) \<in> T"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    by simp 
next
  case (insert x F)
  then show ?case
    using A0 top_i3_def by auto
qed

lemma top_i3_finite_ne:
  assumes "top_i3 T"
  shows "\<And>E. E \<in> Fpow_ne T \<Longrightarrow> (\<Inter>E) \<in> T"
  by (simp add: Fpow_def assms top_i3_induct)

lemma top_i3_i2:
  "top_i3 T \<Longrightarrow> top_i2 T"
  by (simp add: top_i2_def top_i3_induct)


lemma trivial_in_top:
  "is_topology_on T X \<Longrightarrow> ({} \<in> T) \<and> (X \<in> T)"
  by (simp add: is_topology_on_def top_u1_imp_contains_empty)

lemma carrier_is_top_un:
  "is_topology_on T X \<Longrightarrow> \<Union>T = X"
  by (meson Pow_iff cSup_eq_maximum is_topology_on_def subsetD)

lemma trivial_top:
  fixes X::"'a set"
  shows "is_topology_on {{}, X} X"
proof-
  define T where "T= {{}, X}"
  have T0:"T \<in> Dpow X"
    by (simp add: T_def)
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
    using T_def top_i3_def by fastforce
  have T3:"X \<in> T"
    by (simp add: T_def)
  show ?thesis
    using T1 T2 T_def is_topology_on_def by auto
qed

lemma discrete_top:
  fixes X::"'a set"
  shows "is_topology_on (Pow X) X"
proof-
  define T where "T=Pow X"
  have T0:"T \<in> Dpow X"
    by (simp add: T_def)
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
    using T_def top_i3_def by fastforce
  have T3:"X \<in> T"
    by (simp add: T_def)
  show ?thesis
    using T1 T2 T_def is_topology_on_def by auto
qed


lemma trivial_is_top:
  "{{}, X} \<in> (topologies_on X)"
  by (simp add: topologies_on_def trivial_top)

lemma discrete_is_top:
  "Pow X\<in> (topologies_on X)"
  by (simp add: discrete_top topologies_on_def)

lemma discrete_greater:
  "\<And>T. T \<in> topologies_on X \<Longrightarrow> T \<le> (Pow X)"
  by (simp add: is_topology_on_def topologies_on_def)

lemma trivial_least:
  "\<And>T. T \<in> topologies_on X \<Longrightarrow> T \<ge> {{} ,X}"
  by (simp add: topologies_on_def trivial_in_top)

lemma topologies_top:
  "is_min {{}, X} (topologies_on X)"
  by (metis is_min_iff trivial_is_top trivial_least)

lemma topologies_bot:
  "is_max (Pow X) (topologies_on X)"
  by (simp add: discrete_greater discrete_is_top is_max_iff)

lemma topologies_inf_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows  "(\<Inter>ET) \<in> topologies_on X \<and> is_inf_in (\<Inter>ET) ET (topologies_on X)"
 proof-
  have B0:"\<forall>T \<in> ET. is_topology_on T X"
    using A1 topologies_on_def by fastforce
  have B1:"\<forall>T \<in> ET. top_u1 T \<and> top_i3 T \<and> X \<in> T"
    using B0 is_topology_on_def by blast
  define I where  "I=(\<Inter>ET)"
  have T0:"I \<in> Dpow X"
    by (simp add: A0 A1 I_def Inf_less_eq discrete_greater)
  have T1:"top_u1 I"
  proof-
    have T13:"\<And>E. E \<subseteq> I \<longrightarrow> \<Union>E \<in> I"
    proof
      fix E assume A2:"E \<subseteq> I"
      have T10:"\<forall>x. x \<in> E \<longrightarrow> (\<forall>T \<in> ET. x \<in> T) "
        using A2 I_def by auto
      have T11:"(\<forall>T \<in> ET. E \<subseteq> T) "
        using T10 by blast
      have T12:"(\<forall>T \<in> ET. (\<Union>E) \<in> T)"
        by (meson B1 T11 top_u1_def)
      show "\<Union>E \<in> I"
        using I_def T12 by fastforce
    qed
    show ?thesis
      by (simp add: T13 top_u1_def)
  qed
  have T2:"top_i3 I"
  proof-
    have T13:"\<And>a1 a2. (a1 \<in> I \<and> a2 \<in> I) \<longrightarrow> a1 \<inter> a2 \<in> I"
    proof
      fix a1 a2  assume T13A0:"(a1 \<in> I \<and> a2 \<in> I) "
      have T13B0:"\<forall>T \<in> ET. a1 \<in> T \<and> a2 \<in> T"
        using I_def T13A0 by blast
      have T13B1:"\<forall>T \<in> ET. a1 \<inter> a2 \<in> T"
        by (meson B1 T13B0 top_i3_def)
      show "a1 \<inter> a2 \<in> I"
        by (simp add: I_def T13B1)
    qed
    show ?thesis
      by (simp add: T13 top_i3_def)
  qed
  have T3:"X \<in> I"
    by (simp add: B1 I_def)
  have B3:"I \<in> topologies_on X"
    by (metis T0 T1 T2 T3 is_topology_on_def mem_Collect_eq topologies_on_def)
  have B4:"\<forall>T. T \<in> ET \<longrightarrow> I \<le> T"
    by (simp add: I_def Inter_lower)
  have B5:"\<And>S. (\<And>T. T \<in> ET \<Longrightarrow> S\<le> T) \<Longrightarrow> S \<le> I"
    by (simp add: I_def Inter_greatest)
  have B6:"is_inf_in I ET (topologies_on X)"
    by (simp add: B3 B4 B5 is_inf_in_if3)
  show ?thesis
    using B3 B6 I_def by blast
qed

lemma generated_topology1:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "X \<in> T"
  apply(simp add:T_def topology_generated_by_in_def finer_topologies_def)
  using is_topology_on_def by blast

lemma in_finer_top_imp:
  "Ea \<subseteq> \<Inter>(finer_topologies E X) \<Longrightarrow> T \<in> finer_topologies E X \<Longrightarrow> Ea \<subseteq> T"
  by (simp add: le_Inf_iff)

lemma in_finer_top_imp1:
  "T \<in> finer_topologies E X \<Longrightarrow> is_topology_on T X \<and> (E \<subseteq> T)"
  by (simp add: finer_topologies_def)

lemma in_finer_top_imp2:
  "T \<in> finer_topologies E X \<Longrightarrow> T \<in> Dpow X"
  by (simp add: finer_topologies_def is_topology_on_def)

lemma in_iner_top_imp3:
  "\<And>x. x \<in> \<Inter>(finer_topologies E X) \<Longrightarrow> (\<And>S. S \<in> (finer_topologies E X) \<Longrightarrow> x \<in> S)"
  using InterE by blast

lemma generated_topology2:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "top_u1 T"
  apply(auto simp add:T_def topology_generated_by_in_def top_u1_def)
proof-
  let ?F="(finer_topologies E X)"
  fix Ea Xa::"'a set set" assume A0:"Ea \<subseteq> \<Inter>?F" assume A1:"Xa \<in> ?F"
  have B0:"Ea \<subseteq> Xa"
    using A0 A1 by blast
  have B1:"top_u1 Xa"
    using A1 in_finer_top_imp1 is_topology_on_def by blast
  show "\<Union>Ea \<in> Xa"
    using B0 B1 top_u1_def by blast
qed

lemma generated_topology3:
  fixes Xa E::"'a set set" and  a1 a2 X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes A0:"\<And>S. S \<in> (finer_topologies E X) \<Longrightarrow> (a1 \<in> S \<and> a2 \<in> S)" and A1:"Xa \<in> (finer_topologies E X)"
  shows "a1 \<inter> a2 \<in> Xa"
proof-
  have B0:"\<And>S. S \<in> (finer_topologies E X) \<longrightarrow> (a1 \<inter> a2 \<in> S)"
    by (meson assms(2) in_finer_top_imp1 is_topology_on_def top_i3_def)
  show ?thesis
    using A1 B0 by blast
qed


lemma generated_topology4:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "top_i3 T"
  apply(auto simp add:T_def topology_generated_by_in_def top_i3_def)
  by (meson in_finer_top_imp1 is_topology_on_def top_i3_def)

lemma generated_topology5:
  fixes E::"'a set set" and X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes A1:"(finer_topologies E X) \<noteq> {}"
  shows "T \<in> Dpow X"
  apply(auto simp add:T_def topology_generated_by_in_def)
  by (metis A1 DiffI Diff_eq_empty_iff Union_Pow_eq Union_upper empty_iff equals0I in_finer_top_imp1 is_topology_on_def)


lemma generated_topology6:
  fixes E::"'a set set" and X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes "E \<in> Dpow X"
  shows A1:"(finer_topologies E X) \<noteq> {}"
  using assms(2) discrete_top finer_topologies_def by fastforce

lemma generated_topology_is_topology:
  assumes A0:"E \<in> Dpow X"
  shows "is_topology_on (topology_generated_by_in E X) X"
  apply(simp add:is_topology_on_def)
  by (meson PowD assms generated_topology1 generated_topology2 generated_topology4 generated_topology5 generated_topology6)

lemma generated_topology_upper0:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "E \<subseteq> T"
  apply(auto simp add: T_def)
  by (metis in_finer_top_imp1 le_Inf_iff subsetD topology_generated_by_in_def)

lemma generated_topology_upper1:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "\<And>Ei. Ei \<in> {E}  \<Longrightarrow> E \<le> T"
  using A0 T_def generated_topology_upper0 by blast


lemma generated_topology_least1:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  assumes A0:"is_topology_on S X" and A1:"E \<subseteq> S"
  shows "T \<subseteq> S"
  by (auto simp add: T_def A0 finer_topologies_def local.A1 topology_generated_by_in_def)

lemma generated_topology_least2:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "\<And>S. S \<in> topologies_on X \<and> E \<le> S \<Longrightarrow> T \<le> S"
  by (metis A0 T_def generated_topology_least1 mem_Collect_eq topologies_on_def)


lemma generated_topology_is_sup_in:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "has_sup_in {E} (topologies_on X) \<and> is_sup_in T {E} (topologies_on X)"
  proof-
    have B0:"T \<in> ub_set_in {E} (topologies_on X)"
      by (metis A0 CollectI T_def generated_topology_is_topology generated_topology_upper0 singletonD topologies_on_def ub_set_in_elm)
    have B1:"\<And>S. S \<in> ub_set_in {E} (topologies_on X) \<Longrightarrow> T \<le> S"
      by (metis A0 T_def generated_topology_least2 singletonI ub_set_in_mem)
    have B2:"is_sup_in T {E} (topologies_on X)"
      by (simp add: B0 B1 is_min_iff is_sup_in_def)
    have B3:"has_sup_in {E} (topologies_on X)"
      by (meson B0 B1 has_min_iff has_sup_in_def)
    show ?thesis
      by (simp add: B2 B3)
qed

lemma generated_topology_is_sup_in2:
 assumes A0:"E \<in> Dpow X"
 shows  "(topology_generated_by_in E X) = (topology_generated_in E X)"
  by (metis assms generated_topology_is_sup_in is_sup_in_sup_eq topology_generated_in_def)


lemma topologies_sup_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows "(\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T}) \<in> topologies_on X \<and>
         (is_sup_in (\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T}) ET (topologies_on X)) "
proof-
  define U where "U=({T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T})"
  have B0:"(Pow X) \<in> U"
    by (simp add: A1 Sup_le_iff U_def discrete_greater discrete_top)
  have B1:"U \<noteq> {}"
    using B0 by force
  have B2:"(\<Inter>U) \<in> topologies_on X"
    by (metis (no_types, lifting) B1 U_def mem_Collect_eq topologies_inf_closed topologies_on_def)
  have B3:"\<forall>T. is_topology_on T X \<and>  (\<Union>ET) \<subseteq> T \<longrightarrow> (\<Inter>U) \<subseteq> T"
    by (simp add: Inter_lower U_def)
  have B4:"\<forall>T \<in> ET. T \<subseteq> (\<Inter>U)"
    using U_def by blast
  have B5:" (is_sup_in (\<Inter>U) ET (topologies_on X))"
    by (metis B2 B3 B4 Sup_least is_sup_in_if3 mem_Collect_eq topologies_on_def)
  show ?thesis
    using B2 B5 U_def by auto
qed
  

lemma topologies_has_sup:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows "has_sup_in ET (topologies_on X)"
proof-
  have B0:"is_sup_in (top_sup2 ET X) ET (topologies_on X)"
    by (simp add: A0 A1 top_sup2_def topologies_sup_closed)
  have B1:"has_sup_in ET (topologies_on X)"
    using B0 has_sup_in_def is_min_imp_has_min is_sup_in_imp1 by blast
  show ?thesis
    by (simp add: B1)
qed  



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

lemma top_from_nhoods_mem_imp:
  "\<And>V. V \<in> top_from_nhoods N X \<Longrightarrow>  V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
  by (simp add: top_from_nhoods_def)

lemma nhoods_from_top_mem_imp1:
  "\<And>V x. x \<in> X \<Longrightarrow> V \<in> nhoods_from_top T X x \<Longrightarrow>  (\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V)"
  by (simp add: nhoods_from_top_def)

lemma nhood_system_imp_subset:
  assumes "is_nhood_system_in N X" 
  shows "\<And>x V. x \<in> X \<Longrightarrow> V \<in> (N x) \<Longrightarrow> V \<subseteq> X"
  by (meson assms is_filter_in_def is_nhood_system_in_def is_pfilter_in_def)


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
        by (meson A0 A3 A4 is_topology_on_def top_i3_def)
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
  have B0:"?L \<subseteq> ?R"
  proof
    fix V assume A1:"V \<in> ?L"
    have B01:"V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
      using A1 N_def top_from_nhoods_mem_imp by blast
    have B02:"\<forall>x \<in> V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
      by (metis A1 Pow_iff nhoods_from_top_mem_imp1 subsetD top_from_nhoods_mem_imp)
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
      by (metis A0 B06 B07 is_topology_on_def subsetI top_u1_def)
    show "V \<in> ?R"
      by (simp add: B08)
  qed
  have B1:"?R \<subseteq> ?L"
  proof
    fix V assume A1:"V \<in> ?R"
    have B10:"V \<subseteq> X"
      by (meson A1 PowD assms in_mono is_topology_on_def)
    show "V \<in> ?L"
    proof(cases "V = {}")
      case True
      then show ?thesis
        by (simp add: top_from_nhoods_def)
    next
      case False
      obtain x where A2:"x \<in> V"
        using False by blast
      have B11:"\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
        using A1 A2 by blast
      then show ?thesis
        by (smt (verit, ccfv_threshold) A1 B10 CollectI PowI nhoods_from_top_def subset_iff top_from_nhoods_def)
    qed
  qed
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed

lemma nhoods_from_top_inv:
  fixes X::"'a set" and N::"('a \<Rightarrow> 'a set set)" and x::"'a"
  assumes A0:"is_nhood_system_in N X" and A1:"x \<in> X"
  shows "(nhoods_from_top (top_from_nhoods N X) X)(x) = N(x)"
proof-
  define T where A2:"T=top_from_nhoods N X"
  define L where "L=(nhoods_from_top (top_from_nhoods N X) X)"
  have B0:"\<And>V. V \<in> L x \<longrightarrow> V \<in> N x"
  proof
    fix V assume A3:"V \<in> L x"
    obtain U where B1:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (metis A1 A2 A3 L_def nhoods_from_top_mem_imp1)
    have B2:" (\<forall>y \<in> U. U \<in> N y)"
      using A2 B1 top_from_nhoods_mem_imp by blast
    have B3:"U \<in> N x"
      by (simp add: B1 B2)
    have B4:"U \<subseteq> V \<and> V \<subseteq> X"
      by (metis (no_types, lifting) A1 A3 B1 CollectD L_def PowD nhoods_from_top_def)
    have B5:"is_pfilter_in (N x) X"
      using A2 assms is_nhood_system_in_def by fastforce
    have B6:"V \<in> N x"
      by (meson B3 B4 B5 is_filter_in_def is_pfilter_in_def is_upclosed_in_imp)
    show "V \<in> N x"
        by (simp add: B6)
  qed
  have B7:"\<And>V. V \<in> N x \<longrightarrow> V \<in> L x"
  proof
    fix V assume A4:"V \<in> N x"
    have A40:"V \<subseteq> X"
      by (meson A0 A1 A4 nhood_system_imp_subset)
    define U where A5:"U={y \<in> X. V \<in> N y}"
    have B7:"x \<in> U"
      by (simp add: A1 A4 A5)
    have B8:"U \<subseteq> V"
      using A0 A5 is_nhood_system_in_def by fastforce
    have B9:"(\<And>y. y \<in> U \<longrightarrow> U \<in> N y)"
      proof
        fix y assume A6:"y \<in> U"
        have A61:"V \<in> N y"
          using A5 A6 by blast
        obtain W where A7:"(W \<in> N y \<and> (\<forall>z \<in> W. V \<in> N z))"
          by (metis A0 A61 is_nhood_system_in_def)
        have B10:"W \<subseteq> U"
        proof
          fix z assume A8:"z \<in> W"
          have B101:"V \<in> N z"
            by (simp add: A7 A8)
          show "z \<in> U"
            using A0 A5 A6 B101 is_nhood_system_in_def nhood_system_imp_subset by fastforce
        qed
        have B110:"W \<in> N y \<and> is_pfilter_in (N y) X \<and> W \<subseteq> U "
          using A0 A7 B10 is_nhood_system_in_def by fastforce
        have B11:"U \<in> N y"
          by (meson A61 B110 B8 dual_order.trans is_filter_in_def is_pfilter_in_def is_upclosed_in_imp)
        show "U \<in> N y"
          using B11 by force
      qed
    have B120:"U \<in> Pow X \<and> (\<forall>u \<in> U.  V \<in> N u)"
      using A5 by blast
    have B121:"U \<in> T"
      using A2 B120 B9 top_from_nhoods_def by force
    have B122:"x \<in> U \<and> U \<subseteq> V"
      by (simp add: B7 B8)
    have B12:"V \<in> Pow X \<and> U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (simp add: A40 B121 B7 B8)
    show "V \<in> L x"
      by (metis (no_types, lifting) A1 A2 B12 CollectI L_def nhoods_from_top_def)
  qed
  show ?thesis
    using B0 B7 L_def by blast
qed




lemma is_base1_for_topology_imp:
   "is_base1_for_topology B T \<Longrightarrow> U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. U=\<Union>E)"
  by (simp add: is_base1_for_topology_def)

lemma is_base2_for_topology_imp0:
  "is_base2_for_topology B T \<Longrightarrow> (B \<subseteq> T) \<and> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U))"
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_if0:
  "(B \<subseteq> T) \<Longrightarrow> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U)) \<Longrightarrow> is_base2_for_topology B T "
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_imp1:
  "is_base2_for_topology B T \<Longrightarrow>  U \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow>  (\<exists>Bx \<in> B. (x \<in> Bx \<and> Bx \<subseteq> U))"
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_imp2:
  assumes "is_base2_for_topology B T" "U \<in> T" "x \<in> U"
  obtains Bx where "Bx \<in> B  \<and> x \<in> Bx \<and> Bx \<subseteq> U"
  by (meson assms(1) assms(2) assms(3) is_base2_for_topology_imp1)

lemma is_base_3_covering_imp1:
  "is_base_3_covering B X \<Longrightarrow>  (B \<in> Dpow X)"
  by (simp add: is_base_3_covering_def)

lemma is_base_3_covering_imp2:
  "is_base_3_covering B X  \<Longrightarrow> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"
  by (simp add: is_base_3_covering_def)

lemma is_base_3_covering_obtains:
  assumes "is_base_3_covering B X"  and "x \<in> X" obtains U where "U \<in> B \<and> x \<in> U"
  using assms(1) assms(2) is_base_3_covering_imp2 by blast


lemma is_base_3_covering_if:
  "(B \<in> Dpow X) \<Longrightarrow>  (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U) \<Longrightarrow>  is_base_3_covering B X"
  by (simp add: is_base_3_covering_def)


lemma is_base_3_intercont_imp1:
  "is_base_3_intercont B X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"
  by (simp add: is_base_3_intercont_def)

lemma is_base_3_intercont_if:
  " (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)) \<Longrightarrow> is_base_3_intercont B X "
  by (simp add: is_base_3_intercont_def)


lemma is_base_3_intercont_if2:
  "(\<And>x U1  U2. x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B \<Longrightarrow> (\<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)) \<Longrightarrow> is_base_3_intercont B X "
  by (simp add: is_base_3_intercont_def)


lemma is_base_3_intercont_obtains1:
  assumes "is_base_3_intercont B X" and "U1 \<in> B \<and> U2 \<in> B" and "x \<in> U1 \<inter> U2"
  obtains U3 where "U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
  by (meson assms(1) assms(2) assms(3) is_base_3_intercont_imp1)


lemma is_base3_for_topology_imp0:
  "is_base3_for_topology B X \<Longrightarrow> is_base_3_intercont B X"
  by (simp add: is_base3_for_topology_def)

lemma is_base3_for_topology_imp1:
  "is_base3_for_topology B X \<Longrightarrow> is_base_3_covering B X"
  by (simp add: is_base3_for_topology_def)

lemma is_base3_for_topology_imp2:
   "is_base3_for_topology B X \<Longrightarrow> B \<in> Dpow X"
   by (simp add: is_base3_for_topology_def is_base_3_covering_def)

lemma is_base3_for_topology_imp3:
   "is_base3_for_topology B X \<Longrightarrow> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"
    by (simp add: is_base3_for_topology_def is_base_3_covering_def)

lemma is_base3_for_topology_imp3b:
  "is_base3_for_topology B X \<Longrightarrow> x \<in> X  \<Longrightarrow>  \<exists>U \<in> B. x \<in> U"
  by (simp add: is_base3_for_topology_imp3)


lemma is_base3_for_topology_imp4:
   "is_base3_for_topology B X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"
    by (simp add: is_base3_for_topology_def is_base_3_intercont_def)

lemma is_base3_for_topology_imp4b:
   "is_base3_for_topology B X \<Longrightarrow>  U1 \<in> B \<and> U2 \<in> B \<and> x \<in> U1 \<inter> U2 \<Longrightarrow> (\<exists>U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)"
    by (simp add: is_base3_for_topology_def is_base_3_intercont_def)

lemma is_base_3_intercont_imp4c:
  assumes "is_base_3_intercont B X" and "U1 \<in> B \<and> U2 \<in> B \<and> x \<in> U1 \<inter> U2"
  shows "\<exists>U3. U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
  by (meson assms(1) assms(2) is_base_3_intercont_imp1)

lemma is_base3_for_topology_imp5:
  "is_base3_for_topology B X \<Longrightarrow> b \<in> B \<Longrightarrow> b \<subseteq> X"
  using is_base3_for_topology_imp2 by fastforce

lemma is_base3_for_topology_imp6:
  "is_base3_for_topology B X \<Longrightarrow> V \<in> Pow B \<Longrightarrow> (\<Union>V) \<in> Pow X"
  using is_base3_for_topology_imp2 by fastforce

lemma is_base3_for_topology_if:
   " is_base_3_covering B X \<Longrightarrow> is_base_3_intercont B X   \<Longrightarrow>is_base3_for_topology B X"
    by (simp add: is_base3_for_topology_def)

lemma base_intercont_imp_pset_downdir:
  assumes "is_base_3_intercont B X" "x \<in> X"
  shows "is_downdir (nhood_base_from_base B X x)"
  apply( simp add:is_downdir_def nhood_base_from_base_def)
  by (metis Int_iff assms(1) assms(2) is_base_3_intercont_imp1 le_infE)



lemma basis_element_pt_props:
  assumes A0:"is_base2_for_topology B T"
  defines "f \<equiv> basis_element_npt B"
  shows "\<And>U x. (U \<in> T \<and> x \<in> U) \<longrightarrow> (f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U"
proof
    fix U x assume A1:"U \<in> T \<and> x \<in> U"
    obtain Bx where B1:"Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> U"
      by (meson A0 A1 is_base2_for_topology_imp2)
    show "(f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U"
    apply( simp add:f_def basis_element_npt_def)
      by (metis (mono_tags, lifting) \<open>\<And>thesis::bool. (\<And>Bx::'a::type set. Bx \<in> (B::'a::type set set) \<and> (x::'a::type) \<in> Bx \<and> Bx \<subseteq> (U::'a::type set) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> someI2_ex)
qed


lemma basis_element_pt_props2:
  assumes A0:"is_base2_for_topology B T"
  defines "f \<equiv> basis_element_npt B"
  shows "\<And>U. U \<in> T \<Longrightarrow> (\<forall>x. x \<in> U \<longrightarrow> (f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U)"
  by (metis A0 basis_element_pt_props f_def)


lemma basis_element_pt_props3:
  assumes A0:"is_base2_for_topology B T" and A1:"U \<in> T"
  defines "f \<equiv> (\<lambda>x. ((basis_element_npt B) U x))"
  shows "(\<Union>(f`U)) =U "
  using A0 A1 basis_element_pt_props f_def by fastforce


lemma basis_element_npt_props:
  assumes "is_base3_for_topology B X"
  defines "f \<equiv> basis_element_pt B X"
  shows "\<And>x. x \<in> X \<longrightarrow> (f x) \<in> B \<and> x \<in> (f x)"
proof
    fix x assume A0:"x \<in> X"
    show "(f x) \<in> B \<and> x \<in> (f x)"
    apply(simp add:f_def basis_element_pt_def)
      by (metis (no_types, lifting) A0 assms(1) is_base3_for_topology_imp3 someI_ex)
qed

lemma basis_element_int_npt_props0:
  assumes "is_base3_for_topology B X"
  defines "f \<equiv> basis_element_int_npt B X"
  shows "\<And>U1 U2 x. U1 \<in> B \<and> U2 \<in> B  \<and> x \<in> U1 \<inter> U2 \<longrightarrow> ((f U1 U2 x) \<in> B \<and> ((f U1 U2 x) \<subseteq> U1 \<inter> U2) \<and> x \<in> (f U1 U2 x))"
proof
    fix U1 U2 x assume A0:"U1 \<in> B \<and> U2 \<in> B  \<and> x \<in> U1 \<inter> U2"
    let ?U3="(f U1 U2 x)"
    have B0:"\<exists>U3. U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
      by (meson A0 assms(1) is_base3_for_topology_imp4b)
    have B1:"is_base_3_intercont B X"
      by (simp add: assms(1) is_base3_for_topology_imp0)
    show "?U3 \<in> B \<and> (?U3 \<subseteq> U1 \<inter> U2) \<and> x \<in> ?U3"
    apply(simp add:f_def basis_element_int_npt_def)
      by (metis (mono_tags, lifting) B0 Int_subset_iff tfl_some)
qed

lemma un_all_pts:
  assumes "\<And>x. x \<in> U \<longrightarrow> (x \<in> V x) \<and> (V x \<subseteq> U)"
  shows "(\<Union>x \<in> U. V x) = U"
  using assms by fastforce

lemma basis_element_int_npt_props1:
  assumes "is_base3_for_topology B X" "(b1 \<in> B \<and> b2 \<in> B)"
  shows "\<exists>V \<in> Pow B.  b1 \<inter> b2 = (\<Union>V)"
proof-
  define V where A2:"V = (\<lambda>x. (basis_element_int_npt B X) b1 b2 x)"
  have B0:"\<And>x. x \<in> b1 \<inter> b2 \<longrightarrow> (x \<in> V x) \<and> (V x \<subseteq> b1 \<inter> b2)"
    by (metis A2 assms(1) assms(2) basis_element_int_npt_props0)
  have B1:"(\<Union>x \<in> b1 \<inter> b2. V x) = b1 \<inter> b2 "
    using B0 by blast
  have B2:"V`(b1 \<inter> b2) \<in> Pow B \<and>   b1 \<inter> b2 = (\<Union>(V`(b1 \<inter> b2)))"
    by (metis B1 PowI \<open>V::'a::type \<Rightarrow> 'a::type set \<equiv> basis_element_int_npt (B::'a::type set set) (X::'a::type set) (b1::'a::type set) (b2::'a::type set)\<close> assms(1) assms(2) basis_element_int_npt_props0 image_subset_iff)
  show ?thesis
    using B2 by auto
qed  

lemma is_base3_for_topology_imp7:
  assumes A0:"is_base3_for_topology B X" 
  shows "X \<in> (arb_sup_cl B)"
proof-
  define U where "U=basis_element_pt B X"
  have B0:"\<And>x. x \<in> X \<longrightarrow> x \<in> U x \<and>  U x \<in> B"
    by (simp add: U_def assms basis_element_npt_props)
  have B1:"\<And>x. x \<in> X \<longrightarrow> (U x) \<subseteq> X"
    using B0 assms is_base3_for_topology_imp5 by blast
  have B2:"(\<Union>x \<in> X. U x) = X"
    using B0 B1 by blast
  have B8:"U`X \<subseteq> B"
    using B0 by blast
  show ?thesis
    by (metis B2 B8 arb_sup_cl_extensive arb_sup_cl_idemp3 dual_order.trans)
qed
  
lemma base34_generates_top:
  assumes "is_base3_for_topology B X"
  shows " is_topology_on (arb_sup_cl B) X" 
proof-
  define T where "T=(arb_sup_cl B)"
  have T0:"X \<in> arb_sup_cl B"
    by (simp add: assms is_base3_for_topology_imp7)
  have T1:"top_u1 T"
    apply(simp add: top_u1_def)
    by (simp add: T_def arb_sup_cl_idemp3)
  have T2:"top_i3 T"
  proof-
    have T20:"\<And>a1 a2. a1 \<in> T \<and> a2 \<in> T \<longrightarrow> a1 \<inter> a2 \<in> T "
    proof
      fix a1 a2 assume A0:"a1 \<in> T \<and> a2 \<in> T" 
      obtain B1 B2 where B1:"a1 = (\<Union>B1) \<and> B1 \<subseteq> B  \<and> a2=\<Union>B2 \<and> B2 \<in> Pow B"
        by (metis A0 PowD T_def arb_sup_cl_mem_iff sup_un_sets)
      have B2:"a1 \<inter> a2 = (\<Union>b1 \<in> B1. (\<Union>b2 \<in> B2. b1 \<inter> b2 ))"
        using B1 by auto
       define f where "f= basis_element_int_npt B X"
      have B3:"\<And>b1 b2. (b1 \<in> B1 \<and> b2 \<in> B2) \<longrightarrow> (\<exists>V \<in> Pow B.  b1 \<inter> b2 = (\<Union>V))"
        by (meson B1 PowD assms basis_element_int_npt_props1 subsetD)
      have B4:"\<And>b1 b2. (b1 \<in> B1 \<and> b2 \<in> B2) \<longrightarrow> b1 \<inter> b2 \<in> arb_sup_cl B"
        by (simp add: B3 arb_sup_cl_sets)
      have B5:"a1 \<inter> a2 \<in> arb_sup_cl (arb_sup_cl B)"
        by (metis (mono_tags, lifting) B2 B4 arb_sup_cl_idemp arb_sup_cl_idemp3 image_subsetI)
      show " a1 \<inter> a2 \<in> T"
        using B5 T_def arb_sup_cl_idemp2 by blast
      qed
   show ?thesis
     by (simp add: T20 top_i3_def)
  qed
  have T4:"T \<in> Dpow X"
  apply(simp add: T_def)
    by (metis PowD PowI Sup_subset_mono T0 Union_Pow_eq arb_sup_cl_imp1 assms 
        complete_lattice_sup_exists is_base3_for_topology_imp2 subsetI subset_antisym)
  show ?thesis
    using T0 T1 T2 T4 T_def is_topology_on_def by auto
qed

  

lemma is_base1_for_topology_imp2:
   "is_base1_for_topology B T \<Longrightarrow> U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. has_sup E \<and> U= SupUn E)"
  by (simp add: complete_lattice_sup_exists has_sup_un_sets is_base1_for_topology_def)

lemma is_base1_for_topology_if:
  "(\<And>U. U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. U=\<Union>E)) \<Longrightarrow> B \<subseteq> T \<Longrightarrow> is_base1_for_topology B T "
  by (simp add: is_base1_for_topology_def)
    
lemma is_base1_for_topology_if_arb_sup_cl:
  assumes"is_base1_for_topology B T" and "is_topology_on T X"
  shows "T=arb_sup_cl B"        
proof-
  have L:"T \<subseteq> arb_sup_cl B"
    using arb_sup_cl_mem_iff assms is_base1_for_topology_imp2 by fastforce
  have R:"arb_sup_cl B \<subseteq> T"
  proof
    fix V assume A0:"V \<in> arb_sup_cl B"
    obtain E where B0:"E \<in> Pow B \<and> V=(\<Union>E)"
      by (metis A0 arb_sup_cl_mem_iff sup_un_sets)
    have B1:"E \<in> Pow T"
      using B0 assms(1) is_base1_for_topology_def by blast
    show "V \<in> T"
      by (metis B0 B1 PowD assms(2) is_topology_on_def top_u1_def)
  qed
  show ?thesis
    using L R by blast
qed

lemma given_top_base1_imp_base2:
  assumes A0:"is_topology_on T X" and A1:"X \<noteq> {}" and A2:"is_base1_for_topology B T "
  shows "is_base2_for_topology B T"
proof-
  have B0:"B \<subseteq> T"
    using A2 is_base1_for_topology_def by blast
  have B1:"\<forall>U \<in> T. \<forall>x \<in> U. \<exists>Bx \<in> B. x \<in> Bx \<and> Bx \<subseteq> U"
    proof
      fix U assume A3:"U \<in> T"
      obtain E where B2:"E \<subseteq> B \<and> U=Sup E"
        by (meson A2 A3 PowD is_base1_for_topology_imp)
      show "\<forall>x \<in>  U. \<exists>Bx\<in>B. x \<in> Bx \<and> Bx \<subseteq> U"
        proof
          fix x assume A4:"x \<in> U"
          obtain Ex where B3:"Ex \<in> E \<and> x \<in> Ex"
            using A4 B2 by blast
          have B4:"Ex \<subseteq> U \<and> x \<in> Ex"
            by (simp add: B2 B3 Sup_upper)
          show "\<exists>Bx \<in> B. x \<in> Bx \<and> Bx \<subseteq> U"
            using B2 B4 by blast
       qed
     qed
  show ?thesis
    by (simp add: B0 B1 is_base2_for_topology_if0)
qed

lemma given_top_base1_if_base2:
  assumes A0:"is_topology_on T X" and A1:"X \<noteq> {}" and A2:"is_base2_for_topology B T "
  shows "is_base1_for_topology B T"
proof-
  have B0:"B \<subseteq> T"
    by (simp add: A2 is_base2_for_topology_imp0)
  have B1:"\<forall>U \<in> T. \<exists>E \<in> Pow B. U = \<Union> E"
  proof
    fix U assume A3:"U \<in> T"
    define f where B2:"f \<equiv> (\<lambda>x. ((basis_element_npt B) U x))"
    have B3:"(f`U) \<in> Pow B"
      using A2 A3 B2 basis_element_pt_props by fastforce
    have B4:"\<Union>(f`U) = U "
      using A2 A3 B2 basis_element_pt_props3 by blast
    show B2:"\<exists>E \<in> Pow B. U =  \<Union> E"
      by (metis B3 B4)
  qed
  show ?thesis
    by (simp add: B0 B1 is_base1_for_topology_if)
qed
     
lemma base34_generates_by_base1:
  assumes A0:"is_base3_for_topology B X" 
  defines "T \<equiv> {U \<in> Pow X. (\<forall>x. x \<in> U \<longrightarrow> (\<exists>Bx. x \<in> Bx \<and>  Bx \<in> B \<and> Bx \<subseteq> U))}"
  shows "is_topology_on T X"
proof-
  have T0:"X \<in> T"
  apply(simp add: T_def)
    by (meson Pow_iff assms(1) in_dpow_iff is_base3_for_topology_imp2 is_base3_for_topology_imp3)
  have T1:"top_u1 T" 
     apply(simp add:top_u1_def T_def )
    by (smt (verit, best) Ball_Collect Sup_le_iff Union_upper dual_order.trans)
  have T2:"top_i3 T"
    proof-
      have B0: "\<And>a1 a2. (a1 \<in> T \<and> a2 \<in> T) \<longrightarrow> a1 \<inter> a2 \<in> T"
      proof 
         fix a1 a2 assume A1:" (a1 \<in> T \<and> a2 \<in> T)" 
         have B6:"\<And>x. x \<in> a1 \<inter> a2 \<longrightarrow> (\<exists>Bx. Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> a1 \<inter> a2)"
            proof fix x
               assume A2:"x \<in> a1 \<inter> a2" 
               have B3:"(\<exists>B1. B1 \<in> B \<and> x \<in> B1 \<and> B1 \<subseteq> a1)"
                 using A1 A2 T_def by auto
               have B4:"(\<exists>B2. B2 \<in> B \<and> x \<in> B2 \<and> B2 \<subseteq> a2)"
                 using A1 A2 T_def by auto
               have B5:"\<exists>B1 B2. B1 \<in> B \<and> B2 \<in> B \<and> x \<in> B1 \<inter> B2 \<and> B1 \<inter> B2 \<subseteq> a1 \<inter> a2"
                 by (meson B3 B4 IntI Int_mono)
            show "(\<exists>Bx. Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> a1 \<inter> a2)"
              by (meson A0 B5 dual_order.trans is_base3_for_topology_imp4b)
        qed
        show "a1 \<inter> a2 \<in> T"
        apply(simp add: B6 T_def)
          using A1 B6 T_def inf.absorb_iff2 by fastforce
       qed
      show ?thesis
        by (simp add: B0 top_i3_def)
  qed
    have B3:"T \<in> Dpow X"
      using T_def by blast
  show ?thesis
    using B3 T0 T1 T2 is_topology_on_def by auto
qed

lemma base2_top_then_base34:
  assumes A0:"is_base2_for_topology B T" and A1:"is_topology_on T X"
  shows "is_base3_for_topology B X"
  unfolding is_base3_for_topology_def
  proof
    show "is_base_3_covering B X"
    proof-
      have B0:"X \<in> T" 
        using A1 is_topology_on_def by blast
      have B1:"\<And>x. x \<in> X \<longrightarrow> (\<exists>Bx. Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> X)"
        by (meson A0 B0 is_base2_for_topology_imp2)
      have B2:"B \<subseteq> Pow X"
        by (meson A0 A1 in_dpow_iff is_base2_for_topology_def is_topology_on_def subsetD subsetI)
      have B3:" \<forall>x \<in>X. \<exists>U\<in>B. x \<in> U"
        using B1 by auto
      show ?thesis
        by (simp add: B2 B3 is_base_3_covering_if)
    qed
    show "is_base_3_intercont B X"
    proof- 
      have B8:"\<And>x U1  U2. x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)"
      proof
      fix x U1 U2 assume A2:"x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B"
        have B4:"U1 \<in> T \<and> U2 \<in> T"
          using A0 A2 is_base2_for_topology_imp0 by blast
        have B5:"U1 \<inter> U2 \<in> T"
          by (meson A1 B4 is_topology_on_def top_i3_def)
        obtain U3 where B6:"x \<in> U3 \<and> U3 \<in> B \<and> U3 \<subseteq> U1 \<inter> U2"
          by (meson A0 A2 B5 is_base2_for_topology_def)
        show "\<exists>U3 \<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
          using B6 by blast
      qed
      show ?thesis
        using B8 is_base_3_intercont_if2 by blast
    qed
qed

lemma open_iff_nhp:
  assumes A0:"is_topology_on T X" and A1:"V \<in> Pow X"
  shows "V \<in> T \<longleftrightarrow> (\<forall>x. x \<in> V \<longrightarrow> (\<exists>Ux. Ux \<in> T \<and>  x \<in> Ux \<and> Ux \<subseteq> V))" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    using L by blast
  next
  assume R:?R
  define f where B0:"f=(\<lambda>x. SOME Ux. Ux \<in> T \<and> x \<in> Ux \<and> Ux \<subseteq> V)"
  have B1:"\<forall>x. x \<in> V \<longrightarrow> f x \<in> T \<and> x \<in> f x \<and> f x \<subseteq> V"
    by (metis (mono_tags, lifting) R B0 someI)
  have B2:"\<Union>(f`V) \<subseteq> V"
    by (simp add: B1 un_all_pts)
  have B3:"V \<subseteq> (\<Union>(f`V))"
    using B1 by blast   
  show ?L
    by (metis A0 B1 B2 B3 image_subset_iff is_topology_on_def subset_antisym top_u1_def)
qed

  

lemma finite_inter_finite:
  fixes EF::"'a set set"
  assumes A0:"\<And>E. E \<in> EF \<Longrightarrow> finite E" and A1:"EF \<noteq> {}"
  shows "finite (\<Inter>EF)"
  using A0 A1 by blast


lemma in_cofinite_sets_in_imp1:
  "\<And>U. U \<in> cofinite_sets_in X \<Longrightarrow> U \<in> Pow X \<and> (finite (X - U) \<or> U={})"
  by (simp add: cofinite_sets_in_def)

lemma in_cocountable_sets_in_imp1:
  "\<And>U. U \<in> cocountable_sets_in X \<Longrightarrow> U \<in> Pow X \<and> (is_countable (X - U) \<or> U={})"
  by (simp add: cocountable_sets_in_def)

lemma in_cocountable_sets_in_imp2:
  "\<And>U. U \<in> cocountable_sets_in X \<Longrightarrow> U \<noteq> {} \<Longrightarrow> is_countable(X - U)"
  by (simp add: cocountable_sets_in_def)

lemma in_cofinite_iff1:
  assumes A0:"U \<in> Pow X"
  shows "U \<in> cofinite_sets_in X \<longleftrightarrow> (U \<noteq> {} \<longrightarrow> finite (X - U))"
  using A0 cofinite_sets_in_def by auto

lemma in_cocountable_iff1:
  assumes A0:"U \<in> Pow X"
  shows "U \<in> cocountable_sets_in X \<longleftrightarrow> (U \<noteq> {} \<longrightarrow> is_countable (X - U))"
  using assms cocountable_sets_in_def by auto

lemma in_cofinite_iff2:
  assumes A0:"U \<in> Pow X"
  shows "U \<in> cofinite_sets_in X \<longleftrightarrow> (U = {} \<or> finite (X - U))"
  using A0 cofinite_sets_in_def by auto

lemma imp_in_cofinite:
  "U \<in> Pow X \<Longrightarrow> U \<noteq> {} \<Longrightarrow>  finite (X - U) \<Longrightarrow> U \<in> cofinite_sets_in X"
  by (simp add: in_cofinite_iff1)

lemma cofinite_union_comp:
  assumes A0:"C \<subseteq> cofinite_sets_in X"
  shows "\<Union>C \<in> cofinite_sets_in X"
proof-
    let ?U="(\<Union>C)"
    have B0:"?U \<in> Pow X"
      using assms in_cofinite_sets_in_imp1 by fastforce
    have B1:"?U \<noteq> {} \<Longrightarrow> finite (X-?U)"
    proof-
      assume A1:"?U \<noteq> {}"
      have B2:"X-?U=(\<Inter>u \<in> C. (X-u))"
        using A1 by blast
      show "finite (X-?U)"
        by (metis A1 B2 assms empty_Union_conv finite_INT in_cofinite_sets_in_imp1 subset_iff)
    qed
  show ?thesis
    by (metis B0 B1 in_cofinite_iff1)
qed

lemma cocountable_un_closed:
  assumes A0:"C \<subseteq> cocountable_sets_in X"
  shows "\<Union>C \<in> cocountable_sets_in X"
proof-
    let ?U="(\<Union>C)"
    have B0:"?U \<in> Pow X"
      apply(auto simp add: assms cocountable_sets_in_def)
      by (smt (verit, ccfv_threshold) UnionI Union_Pow_eq assms cocountable_sets_in_def mem_Collect_eq subset_eq)
    have B1:"?U \<noteq> {} \<Longrightarrow> is_countable (X-?U)"
    proof-
      assume A1:"?U \<noteq> {}"
      have B2:"X-?U=(\<Inter>u \<in> C. (X-u))"
        using A1 by blast
      show "is_countable (X-?U)"
        by (metis A1 B2 Diff_Diff_Int Inter_lower Union_empty_conv assms image_eqI in_cocountable_sets_in_imp1 inf.absorb_iff2 inj_on_diff is_countable_def subset_eq)
    qed
  show ?thesis
    using B0 B1 cocountable_sets_in_def by blast
qed

lemma cofinite_binf_closed:
  assumes A0:"a1 \<in> cofinite_sets_in X \<and> a2 \<in> cofinite_sets_in X"
  shows "a1 \<inter> a2 \<in> cofinite_sets_in X"
proof-
  have B6:"a1 \<inter> a2 \<noteq> {} \<Longrightarrow> finite (X-(a1 \<inter> a2))"
  proof-
    assume A1:"a1 \<inter> a2 \<noteq> {}" 
     have B7:"finite (X-a1) \<and> (finite (X-a2))"
       using A1 assms in_cofinite_sets_in_imp1 by blast
    show "finite (X-(a1 \<inter> a2))"
      by (simp add: B7 Diff_Int)
  qed
  show "a1 \<inter> a2 \<in> cofinite_sets_in X"
    by (metis B6 PowD PowI assms in_cofinite_iff1 in_cofinite_sets_in_imp1 le_infI2)
qed
  

lemma countable_subset_is_countable1:
  "A \<subseteq> B \<and> is_countable B \<Longrightarrow> is_countable A"
  apply(auto simp: is_countable_def)
  using inj_on_subset by blast

lemma countable_subset_is_countable2:
  "A \<subseteq> X \<and> (is_countable X) \<Longrightarrow> is_countable (X - A)"
  apply(auto simp add: is_countable_def)
  using inj_on_diff by blast

lemma countable_then_cocountable_discrete:
  assumes "is_countable X"
  shows "cocountable_sets_in X = Pow X "
  apply(simp add: cocountable_sets_in_def)
  by (simp add: Collect_mono Pow_def assms countable_subset_is_countable2 subset_antisym)


lemma cofinite_top_is_top:
  "is_topology_on (cofinite_sets_in X) X"
proof-
  define T where "T= (cofinite_sets_in X)"
  have T0:"T \<in> Dpow X"
    by (simp add: Collect_mono Pow_def cofinite_sets_in_def T_def)
  have T1:" (top_u1 T)"
    by (simp add: T_def cofinite_union_comp top_u1_def)
  have T2:"top_i3 T"
    by (simp add: T_def cofinite_binf_closed top_i3_def)
  have T3:"X \<in> T"
    by (simp add: T_def cofinite_sets_in_def)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed

lemma cocountable_binf_closed:
  assumes A0:"a1 \<in> cocountable_sets_in X \<and> a2 \<in> cocountable_sets_in X"
  shows "a1 \<inter> a2 \<in> cocountable_sets_in X"
proof-
  have B6:"a1 \<inter> a2 \<noteq> {} \<Longrightarrow> is_countable (X-(a1 \<inter> a2))"
  proof-
    assume A1:"a1 \<inter> a2 \<noteq> {}" 
     have B7:"is_countable (X-a1) \<and> (is_countable (X-a2))"
       using A1 assms in_cocountable_sets_in_imp2 by auto
      have B8:"is_countable ((X - a1) \<union> (X - a2))"
        by (simp add: B7 is_countable_if_countable is_countable_imp_countable)
     show "is_countable (X-(a1 \<inter> a2))"
       by (simp add: B8 Diff_Int)
  qed
  show "a1 \<inter> a2 \<in> cocountable_sets_in X"
    by (metis B6 Pow_iff assms in_cocountable_iff1 in_cocountable_sets_in_imp1 le_infI2)
qed


lemma cocountable_top_is_top:
  " is_topology_on (cocountable_sets_in X) X"
proof-
  define T where "T= (cocountable_sets_in X)"
  have T0:"T \<in> Dpow X"
    using T_def in_cocountable_sets_in_imp1 by auto
  have T1:" (top_u1 T)"
    by (simp add: T_def cocountable_un_closed top_u1_def)
  have T2:"top_i3 T"
    by (simp add: T_def cocountable_binf_closed top_i3_def)
  have T3:"X \<in> T"
    by (simp add: T_def empty_countable in_cocountable_iff1)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed

lemma particular_point__top_is_top:
  assumes "X \<noteq> {} \<and> a \<in> X"
  shows "is_topology_on (particular_point_top a X) X"
proof-
  define T where "T= (particular_point_top a X)"
  have T0:"T \<in> Dpow X"
    apply(simp add:  particular_point_top_def T_def)
    by blast
  have T1:" (top_u1 T)"
    apply(simp add:top_u1_def T_def particular_point_top_def)
    by blast
  have T2:"top_i3 T"
    apply(simp add:top_i3_def T_def particular_point_top_def)
    by auto
  have T3:"X \<in> T"
    by (simp add: T_def assms particular_point_top_def)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed

lemma excluded_point_top_is_top:
   "is_topology_on (excluded_point_top a X) X"
proof-
  define T where "T= (excluded_point_top a X)"
  have T0:"T \<in> Dpow X"
    apply(simp add:  excluded_point_top_def T_def)
    by blast
  have T1:" (top_u1 T)"
    apply(simp add:top_u1_def T_def excluded_point_top_def)
    by blast
  have T2:"top_i3 T"
    apply(simp add:top_i3_def T_def excluded_point_top_def)
    by auto
  have T3:"X \<in> T"
    by (simp add: T_def excluded_point_top_def)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed

lemma ideal_contains_bot:
  assumes "is_ideal (I::'a set set)"
  shows "{} \<in> I"
  by (meson assms empty_subsetI is_downclosed_def is_ideal_def is_inhabited_imp)

lemma set_ideal_bsup_closed:
  assumes "is_ideal (I::'a set set)" and "I1 \<in> I \<and> I2 \<in> I"
  shows " I1 \<union> I2 \<in> I"
  using assms(1) assms(2) is_ideal_def updir_sup by auto

lemma ideal_complement_top:
  fixes T I::"'a set set" and  X::"'a set" 
  assumes A0:"I \<subseteq> Pow X" and A1:"is_ideal I" and A2:"is_topology_on T X"
  defines "B \<equiv> {x \<in> Pow X.   \<exists>u \<in> T. \<exists>i \<in> I. x = u - i }" 
  shows "is_base3_for_topology B X"
  proof-
    have B0:"is_base_3_covering B X"
    proof-
      have B01:"B \<subseteq> Pow X"
        apply(simp add: B_def)
        by blast
      have B02:"(\<And>(x::'a). x\<in>X \<longrightarrow> (\<exists>U::'a set\<in>B. x \<in> U))"
      proof
        fix x assume A3:"x \<in> X"
        have B020:"{} \<in> I \<and> X \<in> T"
          using A2 ideal_contains_bot is_topology_on_def local.A1 by blast
        have B030:"X \<in> B"
          using B020 B_def by blast
        show "\<exists>U::'a set\<in>B. x \<in> U" 
          using B030 A3 by blast
      qed
      show ?thesis
        by (simp add: B01 B02 is_base_3_covering_if)
    qed
    have B1:"is_base_3_intercont B X"
    proof-  
      have B14:"\<And>B1 B2 x. (B1 \<in> B \<and> B2 \<in> B \<and> x \<in> B1 \<inter> B2) \<longrightarrow> (\<exists>B3 \<in> B.  x \<in> B3 \<and> B3 \<subseteq> B1 \<and> B3 \<subseteq> B2)"
      proof
        fix B1 B2 x assume A4:"(B1 \<in> B \<and> B2 \<in> B \<and> x \<in> B1 \<inter> B2)"
        obtain U1 I1 U2 I2 where B10:"U1 \<in> T \<and> U2 \<in> T \<and> I1 \<in> I \<and> I2 \<in> I \<and> B1=U1-I1 \<and> B2=U2-I2"
          using A4 B_def by blast
        have B11:"B1 \<inter> B2 = (U1 \<inter> U2) - (I1 \<union> I2)"
          using B10 by fastforce
        have B12:" (U1 \<inter> U2)  \<in> T \<and> (I1 \<union> I2) \<in> I"
          by (meson A2 B10 is_topology_on_def local.A1 set_ideal_bsup_closed top_i3_def)
        have B13:"(B1 \<inter> B2 \<in> B)"
          by (metis (mono_tags, lifting) A2 B11 B12 B_def CollectI Diff_subset PowI Sup_upper2 carrier_is_top_un)
        show  "(\<exists>B3 \<in> B.  x \<in> B3 \<and> B3 \<subseteq> B1 \<and> B3 \<subseteq>B2)"
          by (meson A4 B13 inf.cobounded2 inf_sup_ord(1))
      qed
    show ?thesis
      by (simp add: B14 is_base_3_intercont_if)
  qed
  show ?thesis
    by (simp add: B0 B1 is_base3_for_topology_def)
qed
   

lemma arb_sup_cl_generates_top_if_base:
  assumes "is_base3_for_topology B X"
  shows "arb_sup_cl B = topology_generated_by_in B X" (is "?L=?R")
  proof-
    have B0:"is_topology_on ?L X"
      by (simp add: assms base34_generates_top)
    have B1:"B \<subseteq> ?L"
      by (simp add: arb_sup_cl_extensive)
    have B2:"?R \<le> ?L"
      by (meson B0 arb_sup_cl_extensive assms generated_topology_least1 is_base3_for_topology_imp2)
    have B3:"?L \<le> ?R"
    proof
      fix x assume A0:"x \<in> ?L"
      obtain E where B30:"E \<subseteq> B \<and> x = \<Union> E"
        by (metis A0 arb_sup_cl_imp1 sup_un_sets)
      have B31:"E \<subseteq> ?R"
        by (meson B30 assms dual_order.trans generated_topology_upper0 is_base3_for_topology_imp2)
      show "x \<in> ?R"
        using B30 B31 generated_topology2 top_u1_def by blast
  qed
  show ?thesis
    by (simp add: B2 B3 order_class.order_eq_iff)
qed


lemma finf_cl_yields_base:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  defines "B \<equiv> fin_inf_cl_in E (Pow X)"
  shows "is_base3_for_topology B X"
  apply(auto simp add:is_base3_for_topology_def)
  proof-
    show "is_base_3_covering B X"
    proof-
      have B0:"B \<le> Pow X"
        by (simp add: B_def fin_inf_cl_in_range)
       have B1:"X \<in> B"
         by (simp add: B_def fin_inf_cl_in_top)
       have B2:"\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U"
         using B1 by blast
        show ?thesis
          by (simp add: B0 B2 is_base_3_covering_def)
    qed
    show "is_base_3_intercont B X"
    proof-
      have B0:"\<And>B1 B2 x. (B1 \<in> B) \<and> (B2 \<in> B) \<and> (x \<in> B1 \<inter> B2) \<longrightarrow> (\<exists>B3 \<in> B. x \<in> B3 \<and> B3 \<subseteq> B1 \<inter> B2)"
      proof
        fix B1 B2 x assume A0:"(B1 \<in> B) \<and> (B2 \<in> B) \<and> (x \<in> B1 \<inter> B2)"
        obtain E1 where B3:"E1 \<in> Fpow E \<and> has_inf_in E1 (Pow X) \<and> InfIn E1 (Pow X) = B1"
          using A0 B_def fin_inf_cl_in_imp0 by blast
        obtain E2 where B4:"E2 \<in> Fpow E \<and> has_inf_in E2 (Pow X) \<and> InfIn E2 (Pow X) = B2"
          using A0 B_def fin_inf_cl_in_imp0 by blast
        have B5:"E1 \<union> E2 \<in> Fpow E"
          by (metis (mono_tags, lifting) B3 B4 Fpow_def Un_subset_iff finite_Un mem_Collect_eq)
        have B6:"is_inf_in (B1 \<inter> B2) (E1 \<union> E2) (Pow X)"
          by (smt (verit, del_insts) B3 B4 PowD PowI Un_iff inf_equiv1 infin_is_inf le_infI1 le_inf_iff)
        have B7:"has_inf_in (E1 \<union> E2) (Pow X)"
          by (meson B6 has_inf_in_def has_max_iff is_inf_in_imp1 is_max_iff)
        have B8:"InfIn (E1 \<union> E2) (Pow X) = (B1 \<inter> B2)"
          using B6 is_inf_in_inf_eq by blast
        have B9:"B1 \<inter> B2 \<in> B"
        apply(simp add:B_def)
          using B5 B7 B8 fin_inf_cl_in_if1 by blast
        show "(\<exists>B3 \<in> B. x \<in> B3 \<and> B3 \<subseteq> B1 \<inter> B2)"
          by (meson A0 B9 dual_order.eq_iff)
      qed
    show ?thesis
      by (meson B0 is_base_3_intercont_if)
   qed   
qed 


end