theory Top2
  imports Main "./PartialOrders" "./FiltersAgain14"
begin

definition fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set" where
  "fin_inf_cl A \<equiv> {x. \<exists>F \<in> Fpow_ne A. has_inf F \<and> x = InfUn F}"

definition arb_sup_cl::"'a::order set \<Rightarrow> 'a::order set" where
  "arb_sup_cl A \<equiv> {x. \<exists>F \<in> Pow A. has_sup F \<and> x = SupUn F}"

lemma fin_inf_cl_imp0:
  "\<And>A x. x \<in>  fin_inf_cl A \<Longrightarrow> (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F)"
  using fin_inf_cl_def by blast

lemma arb_sup_cl_imp0:
  "\<And>A x. x \<in>  arb_sup_cl A \<Longrightarrow> (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F)"
  using arb_sup_cl_def by blast

lemma fin_inf_cl_imp1:
  "\<And>A x. x \<in>  fin_inf_cl A \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> has_inf F \<and>  x = InfUn F)"
  by (metis fin_inf_cl_imp0 fpow_ne_imp)

lemma arb_sup_cl_imp1:
  "\<And>A x. x \<in>  arb_sup_cl A \<Longrightarrow> (\<exists>F. F \<subseteq> A  \<and> has_sup F \<and> x = SupUn F)"
  using arb_sup_cl_imp0 by auto

lemma fin_inf_cl_if1:
  "\<And>A x.  (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F) \<Longrightarrow> x \<in> fin_inf_cl A"
  by (simp add: fin_inf_cl_def)

lemma arb_sup_cl_if1:
  "\<And>A x.  (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F) \<Longrightarrow> x \<in> arb_sup_cl A"
  by (simp add: arb_sup_cl_def)

lemma fin_inf_cl_mem_iff:
  "x \<in> fin_inf_cl A \<longleftrightarrow> (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F)"
  by (simp add: fin_inf_cl_def)

lemma  arb_sup_cl_mem_iff:
  "x \<in> arb_sup_cl A \<longleftrightarrow> (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F)"
  by (simp add: arb_sup_cl_def)


lemma fpow_ne_iso:
  "A \<subseteq> B \<Longrightarrow> Fpow_ne A \<subseteq> Fpow_ne B"
  by (simp add: Diff_mono Fpow_mono)

lemma fpow_ne_finite_union:
  assumes A0:"EF \<in> Fpow_ne (Fpow_ne A)"
  shows "(\<Union>EF) \<in> Fpow_ne A"
  by (metis DiffD2 Pow_empty Pow_iff assms fpow_ne_equiv fpow_ne_union subset_eq)


lemma arb_sup_cl_extensive:
  "A \<subseteq> arb_sup_cl A"
proof
  fix a assume A0:"a \<in> A"
  have B0:"{a} \<in> Pow A \<and> has_sup {a} \<and> a = SupUn {a}"
    by (simp add: A0 has_sup_singleton sup_singleton)
  show "a \<in> arb_sup_cl A"
    using B0 arb_sup_cl_def by blast
qed

lemma fin_inf_cl_extensive:
  "A \<subseteq> fin_inf_cl A"
proof
  fix a assume A0:"a \<in> A"
  have B0:"{a} \<in> Fpow_ne A \<and> has_inf {a} \<and> a = InfUn {a}"
    by (metis A0 fpow_ne_singleton has_inf_singleton inf_singleton)
  show "a \<in> fin_inf_cl A"
    using B0 fin_inf_cl_def by blast
qed


lemma arb_sup_cl_iso:
  assumes "A \<subseteq> B"
  shows "arb_sup_cl A  \<subseteq> arb_sup_cl B"
proof
  fix a assume A0:"a \<in> arb_sup_cl A"
  obtain F where A1:"F \<in> Pow A \<and> has_sup F \<and> a = SupUn F"
    using A0 arb_sup_cl_imp0 by auto
  have B0:"F \<in> Pow B \<and> has_sup F \<and>  a = SupUn F"
    using A1 assms fpow_ne_iso by blast
  show "a \<in> arb_sup_cl B"
    using B0 arb_sup_cl_def by blast
qed

lemma fin_inf_cl_iso:
  assumes "A \<subseteq> B"
  shows "fin_inf_cl A  \<subseteq> fin_inf_cl B"
proof
  fix a assume A0:"a \<in> fin_inf_cl A"
  obtain F where A1:"F \<in> Fpow_ne A \<and> has_inf F \<and> a = InfUn F"
    using A0 fin_inf_cl_def by auto
  have B0:"F \<in> Fpow_ne B \<and> has_inf F \<and>  a = InfUn F"
    using A1 assms fpow_ne_iso by blast
  show "a \<in> fin_inf_cl B"
    using B0 fin_inf_cl_def by blast
qed



lemma fin_inf_cl_idemp:
    "fin_inf_cl A = fin_inf_cl (fin_inf_cl A)"
proof-
  define C where "C=(fin_inf_cl A)"
  have L:"C \<subseteq> fin_inf_cl C"
    by (simp add: fin_inf_cl_extensive)
  have R:"fin_inf_cl C \<subseteq> C"
  proof
    fix x assume A0:"x \<in> fin_inf_cl C"
    obtain Fx where A1:"Fx \<in> Fpow_ne C \<and> has_inf Fx \<and> x = InfUn Fx"
      using A0 C_def fin_inf_cl_def by blast
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Fpow_ne A. has_inf Fy \<and>  y = InfUn Fy)"
      using A1 C_def fin_inf_cl_def fpow_ne_imp by blast
    (*define Fxy where "Fxy={Fy \<in> Fpow_ne A. has_inf Fy \<and> (\<exists>y \<in> Fx. y = InfUn Fy)}" something something injection*)
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Fpow_ne A \<and> has_inf Fy \<and>  y= InfUn Fy)"
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_inf (F y)" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Fpow_ne A \<and> has_inf Fy \<and>  y= InfUn Fy"
        by (meson A2 B0)
      show "has_inf (F y)"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    have B2:"Fx = (InfUn`FFx)"
    proof-
      have B3:"Fx \<subseteq> InfUn`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(InfUn (F y) = y)"
          by (metis (mono_tags, lifting) A4 B0 F_def someI_ex)
        show "y \<in> (InfUn`FFx)"
          by (metis A4 B4 FFx_def imageI)
      qed
      have B4:"InfUn`FFx \<subseteq> Fx"
        by (metis A1 B3 FFx_def card_seteq dual_order.eq_iff finite_imageI fpow_ne_imp surj_card_le)
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_inf (InfUn`FFx)"
      using A1 B2 by blast
    have B7:"InfUn Fx = InfUn(InfUn`FFx)"
      using B2 by blast
    have B8:"... = InfUn(G)"
      by (metis A1 B1 B6 FFx_def fpow_ne_equiv inf_comp_un_ind G_def)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Fpow_ne A"
      by (metis (mono_tags, lifting) B0 F_def someI)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Fpow_ne A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Fpow_ne (Fpow_ne A)"
      by (metis A1 B10 FFx_def finite_imageI fpow_ne_equiv fpow_ne_if image_is_empty subsetI)
    define G where "G=\<Union>FFx"
    have B12:"G \<in> Fpow_ne A"
      using B11 G_def fpow_ne_finite_union by auto
    have B13:"has_inf G \<and> x = InfUn G"
      by (metis A1 B1 B6 B7 FFx_def G_def fpow_ne_equiv inf_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def fin_inf_cl_if1 by blast
    qed
  show ?thesis
    using C_def L R by force
qed

lemma arb_sup_cl_idemp:
    "arb_sup_cl A = arb_sup_cl (arb_sup_cl A)"
proof-
  define C where "C=(arb_sup_cl A)"
  have L:"C \<subseteq> arb_sup_cl C"
    by (simp add: arb_sup_cl_extensive)
  have R:"arb_sup_cl C \<subseteq> C"
  proof
    fix x assume A0:"x \<in> arb_sup_cl C"
    obtain Fx where A1:"Fx \<in> Pow C \<and> has_sup Fx \<and> x = SupUn Fx"
      using A0 arb_sup_cl_imp0 by auto
    show "x \<in> C"

lemma f_inf_cl_idemp2:
  "\<forall>A. fin_inf_cl A = fin_inf_cl (fin_inf_cl A)"
  using fin_inf_cl_idemp by blast

lemma fin_inf_cl_is_cl:
  "is_closure fin_inf_cl"
  unfolding is_closure_def
  apply(simp add: is_extensive_def fin_inf_cl_extensive is_isotone_def fin_inf_cl_iso)
  apply(simp add:is_idempotent_def)
  using f_inf_cl_idemp2 by blast



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


definition is_nhood_system_in::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_nhood_system_in N X \<equiv> (\<forall>x. is_pfilter_in (N x) X \<and>
                             (\<forall>V \<in> N x. x \<in> V \<and> 
                               (\<exists>W \<in> N x. (\<forall>y \<in> W. V \<in> N y))))"

definition is_topology_on::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "is_topology_on T X \<equiv> (T \<in> Dpow X) \<and> (top_u1 T) \<and> (top_i3 T) \<and> (X \<in> T)"

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


definition topologies_on::"'a set \<Rightarrow> 'a set set set" where
  "topologies_on X \<equiv> {T. is_topology_on T X}"

definition topology_generated_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_in E X = (SupIn {E} (topologies_on X))"

definition nhoods_from_top::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set set)" where
  "nhoods_from_top T X \<equiv> (\<lambda>x. if x \<in> X then {V \<in> Pow X. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V} else undefined)"

definition top_from_nhoods::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "top_from_nhoods N X \<equiv> {V \<in> Pow X. (\<forall>x \<in> V. V \<in> N x)}"

definition nhoods_of::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "nhoods_of x T X \<equiv> {V.  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V)}"

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
  shows  "(\<Inter>ET) \<in> topologies_on X"
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
  show ?thesis
    by (metis I_def T0 T1 T2 T3 is_topology_on_def mem_Collect_eq topologies_on_def)
qed

lemma topologies_sup_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows "(topology_generated_in (\<Union>ET) X) \<in> topologies_on X"
proof-
  have B0:"\<forall>T \<in> ET. is_topology_on T X"
    using A1 topologies_on_def by fastforce
  have B1:"\<forall>T \<in> ET. top_u1 T \<and> top_i3 T \<and> X \<in> T \<and> T \<in> Dpow X"
    using B0 is_topology_on_def by blast
  define E where "E =\<Union>ET"
  define S where "S=filter_closure_in E X"
  have B2:"E \<in> Dpow X"
    by (simp add: A1 E_def Sup_le_iff discrete_greater)
  have B2:""

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


lemma example_top1_is_top:
  fixes X::"'a set" 
  assumes "X \<noteq> {}"
  defines "T \<equiv> (Pow X)"
  shows "is_topology_on T X"
proof-
  have T0:"(T \<in> Pow(Pow X)) \<and> (X \<in> T) \<and> ({} \<in>  T)"
    using T_def by auto
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
  proof-
    have T20:"(\<And>E. E \<in> Fpow_ne T \<longrightarrow> (\<Inter>E) \<in> T)"
    proof
      fix E assume A0:"E \<in> Fpow_ne T"
      show "(\<Inter>E) \<in> T"
        by (metis A0 T_def discrete_top is_topology_on_def top_i3_finite_ne)
    qed
    show ?thesis
      using T_def discrete_top is_topology_on_def by blast
  qed
  show ?thesis
    using T0 T1 T2 is_topology_on_def by auto
qed


lemma example_top2_is_top:
  fixes X::"'a set" 
  assumes "X \<noteq> {}"
  defines "T \<equiv> {{}, X}"
  shows "is_topology_on T X"
proof-
 have T0:"(T \<in> Pow(Pow X)) \<and> (X \<in> T) \<and> ({} \<in>  T)"
    using T_def by auto
  have T1:"(top_u1 T)"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
  proof-
    have T20:"(\<And>E. E \<in> Fpow_ne T \<longrightarrow> (\<Inter>E) \<in> T)"
    proof
      fix E assume A0:"E \<in> Fpow_ne T"
      show "(\<Inter>E) \<in> T"
        by (metis A0 T_def is_topology_on_def top_i3_finite_ne trivial_top)
    qed
    show ?thesis
      using T_def is_topology_on_def trivial_top by auto
  qed
  show ?thesis
    using T0 T1 T2 is_topology_on_def by auto
qed






                                             
end