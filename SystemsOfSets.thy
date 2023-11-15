theory SystemsOfSets
  imports Main "./Posets"
begin

section Definitions

subsection PropertiesOfSystems

definition UpClosed::"'X set set \<Rightarrow> bool" where
  "UpClosed \<A>  \<equiv> (\<forall>B. (\<exists>A \<in>\<A>. B \<supseteq> A) \<longrightarrow> B \<in> \<A> )"

definition UpClosed_In::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "UpClosed_In \<A> X  \<equiv> (\<forall>B \<in> Pow X. (\<exists>A \<in>\<A>. B \<supseteq> A) \<longrightarrow> B \<in> \<A> )"


definition is_upclosed_by_inclusion::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "is_upclosed_by_inclusion \<A> X  \<equiv> is_up_closed \<A> (Pow X)"

definition Centered::"'X set set \<Rightarrow> bool" where
  "Centered \<A> \<equiv> (\<forall>A \<in> \<A>. \<forall>B \<in> \<A>. (A \<inter> B \<noteq> {}))"

definition FIP::"'X set set \<Rightarrow> bool" where
  "FIP \<A> \<equiv> (\<forall>B  \<in> (Pow  \<A>). finite B \<longrightarrow> (\<Inter>B \<noteq> {}))"


definition DownDirected::"'X set set \<Rightarrow> bool" where
  "DownDirected \<A> \<equiv> (\<forall>A \<in> \<A>. \<forall>B \<in> \<A>. (\<exists>C \<in>\<A>. A \<inter> B \<supseteq> C))"

definition PiSystem::"'X set set \<Rightarrow> bool" where
  "PiSystem \<A> \<equiv> (\<forall>A \<in> \<A>. \<forall>B \<in> \<A>. A \<inter> B \<in>\<A> )"

definition Proper::"'X set set \<Rightarrow> bool" where
  "Proper \<A> \<equiv> {} \<notin> \<A>"

definition ProperNE::"'X set set \<Rightarrow> bool" where
  "ProperNE A \<equiv> (Proper A) \<and> (A \<noteq> {})"



subsection TypesOfSystems

definition FilterSubbase::"'X set set \<Rightarrow> bool" where
  "FilterSubbase \<A> \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (FIP \<A>) "

definition FilterBase::"'X set set \<Rightarrow> bool" where
  "FilterBase \<A> \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (DownDirected \<A>) "

definition FilterOfSets::"'X set set \<Rightarrow> bool" where
  "FilterOfSets \<A> \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (PiSystem \<A>) \<and> (UpClosed \<A>) "


definition FilterSubbaseIn::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterSubbaseIn \<A> X  \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (FIP \<A>) "

definition FilterBaseIn::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterBaseIn \<A> X \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (DownDirected \<A>) "

definition FilterOfSetsIn::"'X set set\<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterOfSetsIn \<A> X \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (PiSystem \<A>) \<and> (UpClosed_In \<A> X) "

definition FilSpace::"'X set \<Rightarrow> 'X set set set" where
  "FilSpace X = {\<F> \<in> Pow (Pow X). FilterOfSetsIn \<F> X} "

definition FilterOfSetsIn2::"'X set set\<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterOfSetsIn2 \<A> X \<equiv> (\<A> \<noteq> {})  \<and> (PiSystem \<A>) \<and> (UpClosed_In \<A> X) "

definition DPow::"'X set \<Rightarrow> 'X set set set" where "DPow X = (Pow (Pow X))"

definition FilSpace2::"'X set \<Rightarrow> 'X set set set" where
  "FilSpace2 X = {\<F> \<in> (DPow X). FilterOfSetsIn2 \<F> X} "



subsection RelationsAndOperations

definition preceq:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "\<A> \<preceq> \<B>  \<longleftrightarrow> (\<forall>A\<in>\<A>. (\<exists>B\<in>\<B>. (A \<supseteq> B)))"

definition fequiv:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" (infix "~" 50) where
  "\<A> ~ \<B>  \<longleftrightarrow> ((\<A> \<preceq> \<B>) \<and> ( \<B> \<preceq>  \<A>))"

definition upclosure:: "'X set set \<Rightarrow> 'X set set" where
  "upclosure \<A>  = {E. (\<exists>A \<in>\<A>.( A \<subseteq> E)) }"

definition upclosure_in:: "'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set set" where
  "upclosure_in \<A> X  = {E \<in> Pow X. (\<exists>A \<in>\<A>. ( A \<subseteq> E)) }"

definition fmeetclosure:: "'X set set \<Rightarrow> 'X set set" where
  "fmeetclosure \<A> = {A. (\<exists>\<B>\<in>(Pow \<A>). (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))}"

definition fmeetclosure_in:: "'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set set" where
  "fmeetclosure_in \<A> X = {A \<in> Pow X. (\<exists>\<B>\<in>(Pow \<A>). (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))}"

definition fmeet_in::"'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "fmeet_in \<A> X A \<equiv> ((A \<in> Pow X) \<and> (\<exists>\<B>\<in>(Pow \<A>).  (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {})))"

(*finite_inter_of_idemp*)
definition FilUpSets::"'X set set \<Rightarrow>  'X set \<Rightarrow> 'X set set set" where
  "FilUpSets A X = {F \<in> Pow (Pow X). (FilterOfSetsIn F X) \<and> (A \<preceq> F)}"

definition meshes:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" where
  "meshes \<A> \<B> \<equiv> \<forall>A \<in> \<A>. \<forall>B \<in>\<B>. (A \<inter> B \<noteq> {})"

definition grill_of::"'X set set \<Rightarrow> 'X set  \<Rightarrow> 'X set set" where
  "grill_of \<A> X =  {E \<in> Pow X. meshes {E} \<A> } "

definition filter_generated_by:: "'X set set \<Rightarrow> 'X set set" where
  "filter_generated_by \<C> =  upclosure (fmeetclosure \<C>) "

definition filter_generated_by_in:: "'X set set\<Rightarrow> 'X set  \<Rightarrow> 'X set set" where
  "filter_generated_by_in \<C> X =  upclosure_in (fmeetclosure_in \<C> X) X "

subsection SyntaxForFC

definition is_f_many::"'X set \<Rightarrow>'X set \<Rightarrow> bool" where
  "is_f_many \<B> \<A> \<equiv>  (\<B> \<subseteq> \<A>) \<and> (finite \<B>) \<and> (\<B> \<noteq> {}) "

definition f_many::"'X set \<Rightarrow> 'X set set" where
  "f_many \<A> = {\<B>. is_f_many \<B> \<A> }"



section Lemmas

subsection PropertiesOfRelations

(*1.70.1*)
lemma preceq_transitive:
   "\<forall>\<A> \<B> \<C>. (\<A> \<preceq> \<B> \<and>  \<B> \<preceq> \<C>) \<longrightarrow> (\<A> \<preceq> \<C>)"
  by (meson dual_order.trans preceq_def)

lemma preceq_reflexive:
  "\<forall>\<A>. \<A> \<preceq> \<A>"
  using preceq_def by auto

(*1.70.2*)
lemma subseteq_imp_preceq:
  " \<forall>\<A> \<B>. \<A> \<subseteq> \<B>\<longrightarrow>\<A> \<preceq> \<B>"
  by (meson dual_order.refl in_mono preceq_def)

lemma preceq_trns2:
  "\<forall>\<A> \<B> \<C>. \<A> \<subseteq> \<B> \<and> \<B> \<preceq> \<C> \<longrightarrow> \<A> \<preceq> \<C>  "
  using preceq_transitive subseteq_imp_preceq by blast

(*1.70.3*)
lemma upclosed_then_preceq_imp_subseteq:
  assumes A0: "(Proper \<A>) \<and> (\<A> \<noteq> {})" and
          A1: "(Proper \<B>) \<and> (\<B> \<noteq> {})" and
          A2: "UpClosed \<B>" and
          A3: "\<A> \<preceq> \<B>" 
  shows "\<A> \<subseteq> \<B>"
proof-
  have B0:"\<forall>A. (\<exists>B \<in> \<B>. B \<subseteq> A) \<longrightarrow> A \<in> \<B>"
    using A2 UpClosed_def by blast
  have B1:"\<forall>A \<in> \<A>. (\<exists>B \<in> \<B>. B \<subseteq> A)"
    using A3 preceq_def by blast
  with B0 B1 show ?thesis
    by (meson subsetI)
qed

lemma upclosed_then_preceq_imp_subseteq2:
  assumes A0:"X \<noteq> {}" and A1:"A \<noteq> {}" and A2:"B \<noteq> {}" and A3:"A \<in> (DPow X)" and  A4:"B \<in> (DPow X)" and
          A5: "UpClosed_In B X" and  A6: "A \<preceq> B" 
  shows "A \<subseteq> B"
proof-
  have B0:"\<forall>a \<in> (Pow X). (\<exists>b \<in> B. b \<subseteq> a) \<longrightarrow> a \<in> B"
  proof
    fix a assume "a \<in> Pow X"
    show " (\<exists>b \<in> B. b \<subseteq> a) \<longrightarrow> a \<in> B"  using A5 UpClosed_In_def \<open>a \<in> Pow X\<close> by blast
  qed   
  have B1:"\<forall>a \<in> A. (\<exists>b \<in> B. b \<subseteq> a)" using A6 preceq_def by auto
  with B0 B1 show ?thesis
    by (metis A3 DPow_def PowD in_mono subsetI)
qed

(*1.70.4*)
lemma upclosed_equiv_then_equal:
  assumes A0:"UpClosed  \<A> \<and> UpClosed \<B> " and  A1:"\<A> ~ \<B>"
 shows  "\<A>=\<B>"
  by (meson A0 A1 UpClosed_def fequiv_def preceq_def subsetI subset_antisym)

lemma upclosed_then_upclosed_in:
  "\<forall>X. \<forall>\<A>. UpClosed \<A> \<longrightarrow> UpClosed_In \<A> X"
  by (simp add: UpClosed_In_def UpClosed_def)

lemma upclosed_in_equiv_then_equal:
  assumes A0: "\<A> \<in> Pow (Pow X) \<and> \<B> \<in> Pow (Pow X)" and
          A1:"UpClosed_In \<A> X  \<and> UpClosed_In \<B> X " and
          A2:"\<A> ~ \<B>"
 shows  "\<A>=\<B>"
proof-
  have B0:"\<forall>A \<in> \<A>. \<exists>B \<in> \<B>. A \<supseteq> B"
    by (meson A2 fequiv_def preceq_def)
  have B1:"\<forall>A \<in> \<A>. \<exists>B \<in> \<B>. A \<supseteq> B \<longrightarrow> A \<in> \<B>"
    by (metis A0 A1 B0 UnionI Union_Pow_eq UpClosed_In_def)
  have B2:"\<forall>B \<in> \<B>. \<exists>A \<in> \<A>. A \<subseteq>  B"
    by (meson A2 fequiv_def preceq_def)
  have B3:"\<forall>B \<in> \<B>. \<exists>A \<in> \<A>. A \<subseteq>  B \<longrightarrow> B \<in> \<A>"
    by (meson A0 A1 B2 PowD UpClosed_In_def in_mono)
  have B4:"\<B> \<subseteq> \<A>  \<and> \<A> \<subseteq> \<B>"
    by (meson A0 A1 B0 B2 PowD UpClosed_In_def in_mono subsetI)
  have B5:"\<A> =\<B>"  by (simp add: B4 subset_antisym)
  with B5 show ?thesis by simp
qed

lemma upclosure_is_upclosed1:
  assumes "\<A>=upclosure \<B>"
  shows "UpClosed \<A>"
  by (smt (verit, ccfv_SIG) CollectD CollectI UpClosed_def assms dual_order.trans upclosure_def)

(*1.70.5*)
lemma upclosure_in_is_upclosed_in1:
  assumes "\<A>=upclosure_in \<B> X"
  shows "UpClosed_In \<A> X"
  by (smt (verit, ccfv_SIG) CollectD CollectI UpClosed_In_def assms subset_eq upclosure_in_def)

(*1.70.5*)
lemma upclosure_is_upclosed2:
  assumes "\<A>=upclosure \<B>"
  shows "\<A> ~ \<B>"
  by (smt (verit, ccfv_threshold) assms dual_order.refl fequiv_def mem_Collect_eq preceq_def upclosure_def)

(*1.70.7*)
lemma upclosure_in_is_upclosed_in2:
  assumes A0: "\<B> \<in> Pow (Pow X)" and
          A1: "ProperNE \<B>" and
          A2:"\<A>=(upclosure_in \<B> X)"
  shows "\<A> ~ \<B>"
proof-
  have B0: "\<forall>A \<in> \<A>. \<exists>B \<in> \<B>. A \<supseteq> B"
    by (simp add: A2 upclosure_in_def)
  have B1:"\<A> \<preceq> \<B>"
    by (simp add: B0 preceq_def)
  have B2:"(\<forall>B \<in> \<B>. B \<in>\<A>) \<longrightarrow> (\<forall>B \<in> \<B>. (\<exists>A \<in> \<A>. A \<supseteq> B))"
    by auto
  have B3:"(\<forall>B \<in> \<B>. (\<exists>A \<in> \<A>. A \<supseteq> B)) "
    by (metis (no_types, lifting) A0 A2 UnionI Union_Pow_eq dual_order.refl mem_Collect_eq upclosure_in_def)
  have B4:"\<B> \<preceq> \<A>"
    by (metis (no_types, lifting) A0 A2 PowD in_mono mem_Collect_eq subsetI subseteq_imp_preceq upclosure_in_def)
  have B5:"\<A> ~ \<B>"
    by (simp add: B1 B4 fequiv_def)
  with B5 show ?thesis
    by simp
qed

lemma upclosure_preserves_properness:
  assumes A0:"Proper \<A>"
  shows "Proper( upclosure \<A>)"
  by (smt (verit, best) Proper_def assms mem_Collect_eq subset_empty upclosure_def)


lemma fequiv_iff_upclosure_equal:
  "\<A> ~ \<B> \<longleftrightarrow> (upclosure \<A>) = (upclosure \<B>) "
  by (smt (verit) fequiv_def preceq_transitive upclosed_equiv_then_equal upclosure_is_upclosed1 upclosure_is_upclosed2)



lemma lem_meshing1:
  "\<forall>\<A>. \<forall>\<B>. meshes \<A> \<B> \<longleftrightarrow> {} \<notin> {E. ( \<exists>A \<in>\<A>. \<exists>B \<in>\<B>. E=(A \<inter> B))}"
  using meshes_def by fastforce


lemma lem_meshing2:
 "\<forall>A \<F>.  (meshes {A} \<F>) \<longleftrightarrow> (\<forall>F \<in> \<F>. ((A \<inter> F) \<noteq> {}))"
  by (simp add: meshes_def)

lemma lem_meshing3:
  "\<forall>\<F> B A. ((meshes {A} \<F>) \<and> (A \<subseteq> B) \<longrightarrow> (meshes {B} \<F>))"
proof-
  have B0:"\<forall>\<F> B A. ((meshes {A} \<F>) \<and> (A \<subseteq> B))  \<longleftrightarrow> ((\<forall>F \<in> \<F>. F \<inter> A \<noteq> {}) \<and> (A \<subseteq> B))"
    by (simp add: inf_commute lem_meshing2)
  have B1: "\<forall>F B A. ( F \<inter> A \<noteq> {}) \<and> (A \<subseteq> B) \<longrightarrow> (F \<inter> B \<noteq> {})"
    by auto
  have B2: "\<forall>\<F> B A. ((\<forall>F \<in> \<F>. F \<inter> A \<noteq> {}) \<and> (A \<subseteq> B)) \<longrightarrow>  ((\<forall>F \<in> \<F>. F \<inter> B \<noteq> {})) "
    by (meson B1)
  have B3: "\<forall>\<F> B A. (meshes {A} \<F>) \<and> (A \<subseteq> B) \<longrightarrow> meshes {B} \<F> "
    by (metis B1 Int_commute lem_meshing2)
  with B3 show ?thesis
    by blast
qed


lemma lem_meshing3p2:
  assumes A0: "\<F> \<in> Pow( Pow X) \<and> A \<in> (Pow X)" and
          A1: "FilterOfSets \<F> "
  shows "\<not>(A \<in> \<F> \<and> meshes {X-A} \<F>) "
  by (metis Diff_disjoint Int_commute lem_meshing2)


lemma lem_meshing4:
  assumes A0: "\<F> \<in> Pow( Pow X) \<and> \<G> \<in> Pow (Pow X)" and
          A1: "\<F> \<preceq> \<G> " and
          A2: "FilterOfSets \<F>  \<and> FilterOfSets \<G>"
  shows "meshes \<F> \<G> "
proof-
  have B0: "\<forall>F \<in> \<F>. \<exists> G \<in>\<G>. (F \<supseteq> G)" using A1 preceq_def by auto
  have B1: "\<forall>F \<in> \<F>. \<forall>G \<in>\<G>. F \<inter> G \<noteq> {}"
    by (metis A2 B0 FilterOfSets_def PiSystem_def Proper_def UpClosed_def)
  have B2: "meshes \<F> \<G>"
    by (simp add: B1 meshes_def)
  with B2 show ?thesis by simp
qed

lemma lem_meshing5:
  fixes X::"'X set"
  assumes A0: "UpClosed_In  \<A> X" and
          A1: "\<Union>\<A> \<subseteq> X" and
          A2: "E \<subseteq> X"
  shows "(meshes {X-E} \<A>) \<longrightarrow> (E \<notin> \<A>)"
  by (metis Diff_disjoint Int_commute lem_meshing2)

subsection PropertiesOfTypes

lemma filt_ne:
  assumes A0:"X \<noteq> {}" and
          A1:"F \<in> (FilSpace2 X)"
  shows "F \<noteq> {}"
  using A1 FilSpace2_def FilterOfSetsIn2_def by blast

lemma filt_ne1:
  assumes A0:"X \<noteq> {}" and
          A1:"F \<in> (FilSpace X)"
  shows "F \<noteq> {}"
  using A1 FilSpace_def FilterOfSetsIn_def by fastforce 



lemma filt_univ:
  assumes A0:"X \<noteq> {}" and A1:"F \<in> (FilSpace2 X)" shows "X \<in> F"
  by (smt (verit, best) A1 CollectD DPow_def FilSpace2_def FilterOfSetsIn2_def PowD PowI UpClosed_In_def subset_eq subset_nonempty)

lemma filt_univ2:
  assumes A0:"X \<noteq> {}" and  A1:"F \<in> (FilSpace X)" shows "X \<in> F"
  by (metis (no_types, lifting) A0 A1 DPow_def FilSpace2_def FilSpace_def FilterOfSetsIn2_def FilterOfSetsIn_def filt_univ mem_Collect_eq)


lemma filt_pws1:
   assumes A0:"F \<in> (FilSpace2 X)" shows "F \<in> DPow X" using A0 FilSpace2_def by fastforce

lemma filt_pws12:
   assumes A0:"F \<in> (FilSpace X)" shows "F \<in> DPow X" by (metis (no_types, lifting) CollectD DPow_def FilSpace_def assms)

lemma dpow_lem:
  assumes A0:"A \<in> DPow X" and A1:"a \<in> A"
  shows "a \<in> Pow X"
  using A0 A1 DPow_def by auto

lemma filt_pws2:
   assumes A0:"F \<in> (FilSpace2 X)" and A1:"a \<in> F" shows "a \<in> Pow X"
   using A0 A1 dpow_lem filt_pws1 by blast

lemma filt_pws22:
   assumes A0:"F \<in> (FilSpace X)" and A1:"a \<in> F" shows "a \<in> Pow X"
   using A0 A1 dpow_lem filt_pws12 by blast

lemma filt_upc:
  assumes A0:"F \<in> (FilSpace2 X)" and A1:"b \<in> Pow X" and A2:"a \<in> F"   and A3:"a \<subseteq> b"
  shows "b \<in> F"
proof -
  have "FilterOfSetsIn2 F X"
    using A0 FilSpace2_def by fastforce
  then show ?thesis
    by (metis (no_types) A1 A2 A3 FilterOfSetsIn2_def UpClosed_In_def)
qed

lemma filt_upc2:
  assumes A0:"F \<in> (FilSpace X)" and A1:"b \<in> Pow X" and A2:"a \<in> F" and A3:"a \<subseteq> b"
  shows "b \<in> F"  by (metis (no_types, lifting) A0 A1 A2 A3 CollectD FilSpace_def FilterOfSetsIn_def UpClosed_In_def)

lemma lfil1:
  assumes A0:"F \<in> FilSpace2 X" and A1:"a \<in>F  \<and>  b \<in>F"
  shows "a \<inter> b \<in> F"
  by (metis (no_types, lifting) A0 A1 CollectD FilSpace2_def FilterOfSetsIn2_def PiSystem_def)


lemma lfil12:
  assumes A0:"F \<in> FilSpace X" and A1:"a \<in>F  \<and>  b \<in>F"  shows "a \<inter> b \<in> F"
  by (smt (verit) A0 A1 CollectD FilSpace_def FilterOfSetsIn_def PiSystem_def)

lemma lfil2:
  assumes A0:"F \<in> FilSpace2 X"  shows "a \<in>F  \<and>  b \<in>F \<longrightarrow>a \<inter> b \<in> F" using assms lfil1 by auto

lemma lfil22:
  assumes A0:"F \<in> FilSpace X"  shows "a \<in>F  \<and>  b \<in>F \<longrightarrow>a \<inter> b \<in> F" using assms lfil12 by auto

lemma lfil3:
  assumes "F \<in> FilSpace2 X"  shows  "\<And>a b. a \<in> F \<Longrightarrow> b \<in> F \<Longrightarrow> a \<inter> b \<in> F" using assms lfil2 by blast

lemma lfil32:
  assumes "F \<in> FilSpace X"  shows  "\<And>a b. a \<in> F \<Longrightarrow> b \<in> F \<Longrightarrow> a \<inter> b \<in> F" using assms lfil22 by blast

lemma lfil4:
  assumes A0:"F \<in> FilSpace2 X" and A1:"a \<in> Pow X" and A2:"b \<in> Pow X" shows "(a \<inter> b \<in> F) \<longrightarrow>  (a \<in> F)" using A0 A1 filt_upc by blast

lemma lfil42:
  assumes A0:"F \<in> FilSpace X" and A1:"a \<in> Pow X" and A2:"b \<in> Pow X" shows "(a \<inter> b \<in> F) \<longrightarrow>  (a \<in> F)" using A0 A1 filt_upc2 by blast

lemma lfil5:
   assumes A0:"F \<in> FilSpace2 X" and A1:"a \<in> Pow X" and A2:"b \<in> Pow X" shows "((a \<inter> b) \<in> F) \<longleftrightarrow> ((a \<in> F) \<and> (b \<in> F))"
   by (meson A0 A1 A2 filt_upc inf_le2 lfil1 lfil4)

lemma lfil52:
   assumes A0:"F \<in> FilSpace X" and A1:"a \<in> Pow X" and A2:"b \<in> Pow X" shows "((a \<inter> b) \<in> F) \<longleftrightarrow> ((a \<in> F) \<and> (b \<in> F))"
   by (meson A0 A1 A2 filt_upc2 inf_le2 lfil12 lfil42)

(*1.70.8*)
lemma equiv_fbase_imp_fbase:
  assumes A0:"FilterBase \<B> "and  A1: "\<A> ~\<B> " shows "FilterBase \<A>"
proof-
  have B0: "\<forall>A \<in> \<A>. (\<exists>B \<in> \<B>. B \<subseteq> A)"
    by (meson A1 fequiv_def preceq_def)
  have B1: "\<forall>B \<in> \<B>. B \<noteq> {} "
    using A0 FilterBase_def Proper_def by auto
  have B2: "\<forall>A \<in> \<A>.  A \<noteq> {}"
    using B0 B1 by blast
  have B3:"\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>.( \<exists>B1 \<in> \<B>. B1 \<subseteq> A1)\<and>( \<exists>B2 \<in> \<B>. B2 \<subseteq> A2)"
    by (simp add: B0)
  have B4:"\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>.( \<exists>B1 \<in> \<B>. B1 \<subseteq> A1)\<and>( \<exists>B2 \<in> \<B>. B2 \<subseteq> A2)"
    by (simp add: B0)
 have B5:"\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. (\<exists>B1 \<in> \<B>. (\<exists>B2 \<in> \<B>. ( (B1 \<inter> B2)\<subseteq> (A1 \<inter> A2))))"
   by (meson B4 Int_mono)
  have B6: "\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. (\<exists>B1 \<in> \<B>. (\<exists>B2 \<in> \<B>.(\<exists>B3 \<in> \<B>. (B3 \<subseteq> (B1 \<inter> B2)) \<and> ((B1 \<inter> B2)\<subseteq> (A1 \<inter> A2))) ))"
    by (metis A0 B5 DownDirected_def FilterBase_def)
  have B7: "\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. (\<exists>B1 \<in> \<B>. (\<exists>B2 \<in> \<B>.(\<exists>B3 \<in> \<B>. \<exists>A3 \<in> \<A>. ((A3 \<subseteq> B3) \<and> (B3 \<subseteq> (B1 \<inter> B2))) \<and> ((B1 \<inter> B2)\<subseteq> (A1 \<inter> A2))) ))"
    by (smt (verit) A1 B6 fequiv_def preceq_def)
  have B8: "\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. \<exists>A3 \<in> \<A>. A3 \<subseteq> A1 \<inter> A2"
    by (metis B7 subset_trans)
  have B9:"DownDirected \<A>"
    using B8 DownDirected_def by blast
  have B10:"Proper \<A>"
    using B2 Proper_def by blast
  have B11:"\<A> \<noteq> {}"
    by (metis A0 A1 FilterBase_def UpClosed_def empty_iff fequiv_def preceq_def upclosed_equiv_then_equal)
  with B9 B10 B11 show ?thesis
    by (simp add: FilterBase_def)
qed

lemma equiv_fbase_imp_fbase2:
  assumes A0:"FilterBaseIn B X "and  A1: "A ~B " shows "FilterBaseIn A X"
  by (metis A0 A1 FilterBaseIn_def FilterBase_def equiv_fbase_imp_fbase)

(*1.70.9*)
lemma fbase_gen_filter:
  assumes A0: "FilterBase A"  shows "FilterOfSets (upclosure A)"
proof-
  let ?F="upclosure A"
  have B0: "f \<in> ?F \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f)"
    by (simp add: upclosure_def)
  have B1:"Proper A"
    using FilterBase_def assms by blast
  from B0 B1 have  B2:"{} \<notin> ?F"
    by (metis FilterBase_def Proper_def assms equiv_fbase_imp_fbase upclosure_is_upclosed2)
  have B3:"Proper ?F"
    by (simp add: B2 Proper_def)
  have B4: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B1\<in>A. \<exists>B2\<in> A. \<exists>B3 \<in> A. (B1 \<subseteq>F1) \<and> (B2 \<subseteq> F2) \<and> (B3 \<subseteq> (B1 \<inter> B2))"
    by (smt (verit, ccfv_threshold) CollectD DownDirected_def FilterBase_def assms upclosure_def)
  have B5: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B3 \<in> A. (B3 \<subseteq> (F1 \<inter> F2)) "
    by (metis B4 DownDirected_def FilterBase_def UpClosed_def assms equiv_fbase_imp_fbase upclosure_is_upclosed1 upclosure_is_upclosed2)
  have B6: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. ((F1 \<inter> F2) \<in> ?F)"
    by (metis (mono_tags, lifting) B5 mem_Collect_eq upclosure_def)
  have B7: "PiSystem ?F"
    using B6 PiSystem_def by blast
  have B8: "UpClosed ?F"
    by (simp add: upclosure_is_upclosed1)
  from B3 B7 B8 have B9: "FilterOfSets ?F"
    by (metis FilterBase_def FilterOfSets_def assms equiv_fbase_imp_fbase upclosure_is_upclosed2)
  with B9 show ?thesis by simp
qed


lemma fbase_gen_filter2:
  assumes A0:"FilterBaseIn A X" and A1:"A \<in> DPow X" shows "FilterOfSetsIn (upclosure_in A X) X"
proof-
   let ?F="upclosure_in A X"
   have B0: "\<forall>f \<in> Pow X. (f \<in> ?F \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f))"  by (simp add: upclosure_in_def)
   have B1:"Proper A" using A0 FilterBaseIn_def by blast
   have B3:"Proper ?F"  by (metis A0 A1 DPow_def FilterBaseIn_def ProperNE_def equiv_fbase_imp_fbase2 upclosure_in_is_upclosed_in2)
   have B4: "\<forall>f1 \<in> ?F. \<forall>f2 \<in> ?F. (\<exists>b1\<in>A. \<exists>b2\<in> A. \<exists>b3 \<in> A. (b1 \<subseteq>f1) \<and> (b2 \<subseteq> f2) \<and> (b3 \<subseteq> (b1 \<inter> b2)))"
   proof
    fix f1 assume B4A0:"f1 \<in> ?F"
    obtain b1 where B4A1:"b1 \<in> A \<and> b1 \<subseteq> f1" by (smt (verit) B4A0 CollectD upclosure_in_def)
    show "\<forall>f2 \<in> ?F. (\<exists>b1\<in>A. \<exists>b2\<in> A. \<exists>b3 \<in> A. (b1 \<subseteq>f1) \<and> (b2 \<subseteq> f2) \<and> (b3 \<subseteq> (b1 \<inter> b2)))"
    proof
      fix f2 assume B4A2:"f2 \<in> ?F"
      obtain b2 where B4A3:"b2 \<in> A \<and> b2 \<subseteq> f2" by (smt (verit) B4A2 CollectD upclosure_in_def)
      obtain b3 where B4A4:"b3 \<in> A \<and> b3 \<subseteq> (b1 \<inter> b2)" by (metis A0 B4A1 B4A3 DownDirected_def FilterBaseIn_def)
      show "(\<exists>b1\<in>A. \<exists>b2\<in> A. \<exists>b3 \<in> A. (b1 \<subseteq>f1) \<and> (b2 \<subseteq> f2) \<and> (b3 \<subseteq> (b1 \<inter> b2)))" using B4A1 B4A3 B4A4 by blast
    qed
   qed
   have B6: "\<forall>f1 \<in> ?F. \<forall>f2 \<in> ?F. ((f1 \<inter> f2) \<in> ?F)" by (smt (verit) B0 B4 CollectD Pow_iff inf.absorb_iff2 inf.bounded_iff inf_le2 upclosure_in_def)
   have B7: "PiSystem ?F" using B6 PiSystem_def by blast
   have B8: "UpClosed_In ?F X" by (simp add: upclosure_in_is_upclosed_in1)
   from B3 B7 B8 have B9: "FilterOfSetsIn ?F X" by (metis A0 A1 DPow_def FilterBaseIn_def FilterOfSetsIn_def ProperNE_def equiv_fbase_imp_fbase2 upclosure_in_is_upclosed_in2)
   with B9 show ?thesis by simp
qed
  
(*1.70.10*)
lemma upclosure_iff:
  assumes A0:"X \<noteq> {}" and A1:"A \<in> Pow (Pow X)"
  shows "\<forall>f \<in> Pow X. ((f \<in> (upclosure_in A X) \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f)))"
proof-
  let ?L="\<lambda>f. f \<in> (upclosure_in A X)" and ?R="\<lambda>f. (\<exists>a \<in> A. a \<subseteq> f)"
  have LR:"\<forall>f \<in> Pow X. (?L f \<longrightarrow>?R f)"
    by (simp add: upclosure_in_def)
  have RL:"\<forall>f \<in> Pow X. (?R f \<longrightarrow>?L f)"
    by (simp add: upclosure_in_def)
  with LR RL show ?thesis by blast
qed

(*1.70.9*)
lemma fbase_gen_filterb:
  assumes A0: "FilterBaseIn A X" and A1:"X \<noteq> {}" and A2:"A \<in> Pow(Pow X)"
  shows "FilterOfSetsIn (upclosure_in A X) X"
proof-
  let ?F="upclosure_in A X"
  have B0: "\<forall>f \<in> Pow X. (f \<in> ?F \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f))"
    by (simp add: upclosure_in_def)
  have B1:"Proper A"
    using A0 FilterBaseIn_def by blast
  from B0 B1 have  B2:"{} \<notin> ?F"
    by (simp add: Proper_def)
  have B3:"Proper ?F"
    by (simp add: B2 Proper_def)
  have B4: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B1\<in>A. \<exists>B2\<in> A. \<exists>B3 \<in> A. (B1 \<subseteq>F1) \<and> (B2 \<subseteq> F2) \<and> (B3 \<subseteq> (B1 \<inter> B2))"
    by (smt (verit, best) A0 CollectD DownDirected_def FilterBaseIn_def upclosure_in_def)
  have B5: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B3 \<in> A. (B3 \<subseteq> (F1 \<inter> F2)) "
    by (smt (verit, ccfv_SIG) B4 inf.absorb_iff2 inf.cobounded2 inf_assoc)
  have B6: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. ((F1 \<inter> F2) \<in> ?F)"
    by (metis (mono_tags, lifting) B5 Pow_iff inf.absorb_iff2 inf_assoc mem_Collect_eq upclosure_in_def)
  have B7: "PiSystem ?F"
    using B6 PiSystem_def by blast
  have B8: "UpClosed_In ?F X"
    by (simp add: upclosure_in_is_upclosed_in1)
  from B3 B7 B8 have B9: "FilterOfSetsIn ?F X"
    by (metis (no_types, lifting) A0 A2 B0 FilterBaseIn_def FilterOfSetsIn_def Pow_iff bot.extremum_uniqueI in_mono subsetI)
  with B9 show ?thesis by simp
qed
(*1.70.10*)
lemma fbase_condition:
  assumes A0: "(Proper B)" and
          A1: "FilterOfSets F"
  shows "(F=upclosure B) \<longleftrightarrow> (F \<preceq> B) \<and> (B \<subseteq> F)"
  by (metis A0 A1 FilterOfSets_def UpClosed_def empty_iff fequiv_def fequiv_iff_upclosure_equal subseteq_imp_preceq upclosed_equiv_then_equal upclosed_then_preceq_imp_subseteq upclosure_is_upclosed1 upclosure_is_upclosed2)

(*1.70.11*)
lemma upprop_fip:
  assumes A0:"Centered B" and
          A1: "A \<preceq> B"
  shows"Centered A"
  by (metis (no_types, lifting) A0 A1 Centered_def inf_mono preceq_def subset_empty)




lemma union_inter_c:
  "\<Inter>(\<A> \<union> \<B>) = (\<Inter>\<A>)\<inter>(\<Inter>\<B> )"
  by blast

lemma union_inter_c2:
  assumes  "I \<noteq> {}" and
           "B \<in> Pow X" and
           "\<forall>i \<in> I. A(i) \<in> Pow X" and
           "X \<noteq> {}"
  shows "B \<inter> (\<Union>i \<in> I. A(i)) = (\<Union>i \<in> I. (B \<inter> A(i)))"
  by simp

lemma union_inter_c3:
  assumes "\<forall>j \<in> J. I(j) \<noteq> {}" and "J \<noteq> {}" and
          "\<forall>j \<in> J. \<forall>i \<in> I(j). A(i) \<in> Pow X" and "X \<noteq> {}"
  shows "(\<Union>i\<in>(\<Union>j \<in> J. I(j)). A(i)) =(\<Union>j\<in>J. (\<Union>i\<in>I(j). A(i)))"
  by blast


lemma union_inter_c4:
  assumes "I \<noteq> {}" and "finite I" and "\<forall>i \<in> I. (A i) \<in> Pow X" and 
          "\<forall>i \<in> I. (finite (A i))"
  shows "finite (\<Union>i\<in>I. A (i))"
  using assms(2) assms(4) by blast

lemma sup_subbase0:
  assumes A0:"FilterSubbase \<C>"
  shows "Proper (fmeetclosure \<C>)"
  by (smt (verit, ccfv_threshold) FIP_def FilterSubbase_def Proper_def assms fmeetclosure_def mem_Collect_eq)

lemma misc1:
  assumes A0:"A \<noteq> {} \<and> B \<noteq> {}" and
          A1:"{} \<notin> A \<and> {} \<notin> B" and
          A2: "\<forall>a \<in> A. (\<exists> b \<in> B. b \<subseteq>  a)"
  shows "(\<Inter>B)\<subseteq> (\<Inter>A)"
  by (simp add: A2 Inf_mono)



lemma upprop_fip2:
  assumes A0:"FIP \<B>" and
          A1: "\<A> \<preceq> \<B>"
   shows"FIP \<A>"
proof-
  have B0: "\<forall>\<E> \<in> Pow \<A>. (\<forall>E \<in> \<E>. (\<exists>F \<in>\<B>. F \<subseteq> E)) "
    by (metis A1 Pow_iff preceq_def preceq_trns2)
  let ?f="\<lambda>E. (SOME F. ((F \<subseteq> E) \<and> (F \<in> \<B>)))"
  have B0:"\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> finite (?f`(\<E>))"
    by simp
  have B1:"\<forall>\<E> \<in> Pow \<A>.  (?f`(\<E>))\<subseteq> \<B>"
  proof -
    { fix AA :: "'a set set"
      have ff1: "\<And>A. \<not> A \<subseteq> \<A> \<or> A \<preceq> \<B>"
        using A1 preceq_transitive subseteq_imp_preceq by blast
      have "\<forall>A f Aa. \<exists>Ab. (f ` A \<subseteq> Aa \<or> (Ab::'a set) \<in> A) \<and> ((f Ab::'a set) \<notin> Aa \<or> f ` A \<subseteq> Aa)"
        by (metis image_subset_iff)
      then have "AA \<notin> Pow \<A> \<or> (\<lambda>A. SOME Aa. Aa \<subseteq> A \<and> Aa \<in> \<B>) ` AA \<subseteq> \<B>"
        using ff1 by (smt (z3) Pow_iff preceq_def someI_ex) }
    then show ?thesis
      by simp
  qed
  have B3:"\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> (finite (?f`(\<E>))) \<and> ((?f`(\<E>)) \<in> Pow \<B>)"
    by (simp add: B1)
  have B4:"\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> \<Inter>(?f`(\<E>)) \<noteq> {}"
    by (metis (mono_tags, lifting) A0 B3 FIP_def)
  have B5:"\<forall>\<E> \<in> Pow \<A>. ( \<forall>E \<in> \<E>. ((?f E) \<subseteq> E))"
    by (metis (no_types, lifting) A1 PowD preceq_def preceq_transitive someI_ex subseteq_imp_preceq)
  have B6:"\<forall>\<E> \<in> Pow \<A>.  \<Inter>(?f`(\<E>)) \<subseteq> (\<Inter>\<E>)"
    using B5 by blast
  have B7:"\<forall>\<E> \<in> Pow \<A>. finite \<E>\<longrightarrow> ( \<Inter>(?f`(\<E>)) \<noteq> {}) \<and> ( \<Inter>(?f`(\<E>)) \<subseteq> (\<Inter>\<E>))"
    using B4 B6 by force
  have B8: "\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> (\<Inter>\<E>) \<noteq> {}"
    by (metis (no_types, lifting) B4 B6 subset_empty)
  with B8 show ?thesis by (simp add: FIP_def)
qed


lemma union_fiter0:
  assumes A0:"FilterSubbase \<C>" 
  shows "B \<in> (fmeetclosure \<C>) \<longleftrightarrow> (\<exists>\<E>\<in>(f_many \<C>). B=\<Inter>\<E> )"
proof-
  have B0:"B \<in>(fmeetclosure \<C>) \<longleftrightarrow> (\<exists>\<B>\<in>Pow \<C>. (finite \<B>) \<and> ( B=\<Inter>\<B>) \<and> (\<B> \<noteq> {})) "
    by (simp add: fmeetclosure_def)
  have B1:"\<forall>\<E>. (\<E>\<in>(f_many \<C>) \<longleftrightarrow>  is_f_many \<E> \<C>)"
    by (simp add: f_many_def)
  have B2:"\<forall>\<E>. ( is_f_many \<E> \<C>) \<longleftrightarrow> ((\<E> \<subseteq>\<C>) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: is_f_many_def)
  have B3:"\<forall>\<E>. (\<E>\<in>(f_many \<C>)) \<longleftrightarrow> ((\<E>  \<in> Pow \<C>) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: B1 B2)
  have B4:"B\<in>(fmeetclosure \<C>) \<longrightarrow> (\<exists>\<E>. ((\<E>  \<in> Pow \<C>) \<and> (finite \<E>) \<and> (\<E> \<noteq> {})) \<and>( B=\<Inter>\<E>) )"
    using B0 by blast
  have B5:"B\<in>(fmeetclosure \<C>) \<longrightarrow>  (\<exists>\<E>\<in>(f_many \<C>). B=\<Inter>\<E> )"
    using B0 B3 by blast
  have B6:"\<forall>B. ((\<exists>\<E>\<in>(f_many \<C>). B=\<Inter>\<E> ) \<longrightarrow> B\<in>(fmeetclosure \<C>))"
    by (smt (verit, del_insts) B3 CollectI fmeetclosure_def is_f_many_def)
  with B5 B6 show ?thesis by blast
qed



lemma union_fiter0b:
  assumes A0:"FilterSubbaseIn C X" 
  shows "\<forall>B \<in> Pow X. (B \<in> (fmeetclosure_in C X) \<longleftrightarrow> (\<exists>\<E>\<in>(f_many C). B=\<Inter>\<E> ))"
proof-
  have B0:"B \<in>(fmeetclosure_in C X) \<longleftrightarrow> (B \<in> Pow X \<and> (\<exists>\<B>\<in>Pow C. (finite \<B>) \<and> ( B=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))) "
    by (simp add: fmeetclosure_in_def)
  have B1:"\<forall>\<E>. (\<E>\<in>(f_many C) \<longleftrightarrow>  is_f_many \<E> C)"
    by (simp add: f_many_def)
  have B2:"\<forall>\<E>. ( is_f_many \<E> C) \<longleftrightarrow> ((\<E> \<subseteq>C) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: is_f_many_def)
  have B3:"\<forall>\<E>. (\<E>\<in>(f_many C)) \<longleftrightarrow> ((\<E>  \<in> Pow C) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: B1 B2)
  have B4:"B\<in>(fmeetclosure_in C X) \<longrightarrow> (\<exists>\<E>. ((\<E>  \<in> Pow C) \<and> (finite \<E>) \<and> (\<E> \<noteq> {})) \<and>( B=\<Inter>\<E>) )"
    using B0 by blast
  have B5:"B\<in>(fmeetclosure_in C X) \<longrightarrow>  (\<exists>\<E>\<in>(f_many C). B=\<Inter>\<E> )"
    using B0 B3 by blast
  have B6:"\<forall>B \<in> Pow X. (((\<exists>\<E>\<in>(f_many C). B=\<Inter>\<E> ) \<longrightarrow> B\<in>(fmeetclosure_in C X)))"
    by (metis (mono_tags, lifting) B3 CollectI fmeetclosure_in_def)
  with B5 B6 show ?thesis
    by (smt (verit, best) B3 fmeetclosure_in_def mem_Collect_eq)
qed

subsection Subbases

lemma sup_subbase1:
  assumes A0:"FilterSubbase \<C>" and
          A1:"(A1\<in>(fmeetclosure \<C>)) \<and> (A2 \<in>(fmeetclosure \<C>))"
  shows "(A1 \<inter> A2) \<in> (fmeetclosure \<C>)"
  by (smt 
      (verit, ccfv_threshold)
         A1 CollectD CollectI Pow_iff Un_empty
         finite_Un fmeetclosure_def le_sup_iff
         union_inter_c)


lemma sup_subbase1b:
  assumes A0:"FilterSubbaseIn C X" and
          A1:"(A1\<in>(fmeetclosure_in C X)) \<and> (A2 \<in>(fmeetclosure_in C X))"
  shows "(A1 \<inter> A2) \<in> (fmeetclosure_in C X)"
  by (smt (verit) A1 CollectD CollectI IntD2 Pow_iff Un_empty finite_Un fmeetclosure_in_def le_sup_iff subset_eq union_inter_c)





lemma sup_subbase2:
  assumes A0:"FilterSubbase \<C>"
  shows "PiSystem (fmeetclosure \<C>)"
  by (simp add: PiSystem_def assms sup_subbase1)


lemma sup_subbase2b:
  assumes A0:"FilterSubbaseIn C X"
  shows "PiSystem (fmeetclosure_in C X)"
  by (simp add: PiSystem_def assms sup_subbase1b)


lemma sup_subbase3:
  assumes A0: "PiSystem \<A>"
  shows "DownDirected \<A>"
  by (meson DownDirected_def PiSystem_def assms subsetI)


lemma sup_subbase5:
  assumes A0:"FilterSubbase \<C>"
  shows "( fmeetclosure \<C>) \<noteq> {}"
  by (metis CollectI FilterSubbase_def assms bot.extremum ex_in_conv f_many_def finite.emptyI finite.insertI insert_subset is_f_many_def union_fiter0)


lemma sup_subbase5b:
  assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
  shows "(fmeetclosure_in C X) \<noteq> {}"
proof -
  obtain bb :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
    f1: "\<forall>X0 X1. bb X0 X1 = is_f_many X1 X0"
    by moura
  then have "\<forall>A. f_many A = Collect (bb A)"
    using f_many_def by blast
  then show ?thesis
    using f1 by (metis (no_types) A1 A2 FilterSubbaseIn_def Pow_iff cInf_singleton ex_in_conv finite.emptyI finite_insert insert_not_empty insert_subset is_f_many_def mem_Collect_eq subset_eq union_fiter0b)
qed


lemma sup_subbase4:
  assumes A0:"FilterSubbase \<C>"
  shows "FilterBase (fmeetclosure \<C> )"
  by (simp add: FilterBase_def assms sup_subbase0 sup_subbase2 sup_subbase3 sup_subbase5)

lemma sup_subbase4b:
  assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
  shows "FilterBaseIn (fmeetclosure_in C X) X"
  by (smt (verit) A0 A1 A2 CollectD FIP_def FilterBaseIn_def FilterSubbaseIn_def Proper_def fmeetclosure_in_def sup_subbase2b sup_subbase3 sup_subbase5b)


subsection Bases

lemma sup_base5:
  assumes A0:"FilterBase \<B>"
  shows "(upclosure \<B>) \<noteq> {}"
  using FilterOfSets_def assms fbase_gen_filter by auto

lemma sup_base5b:
  assumes A0: "X \<noteq> {}" and A1:"B \<in> Pow(Pow X)" and A2:"FilterBaseIn B X"
  shows "(upclosure_in B X) \<noteq> {}"
  by (metis A0 A1 A2 FilterOfSetsIn_def fbase_gen_filterb)


lemma sup_base6:
  assumes A0: "FilterBase \<B>"
  shows "Proper ( upclosure( \<B> ))"
  using FilterBase_def assms upclosure_preserves_properness by auto

lemma sup_base6b:
  assumes A0:"X \<noteq> {}" and A1:"B \<in> Pow(Pow X)" and A2:"FilterBaseIn B X"
  shows "Proper ( upclosure_in B  X)"
  by (meson A0 A1 A2 FilterOfSetsIn_def fbase_gen_filterb)


lemma sup_base7:
  assumes A0: "FilterBase \<B>"
  shows "PiSystem (upclosure \<B>)"
  using FilterOfSets_def assms fbase_gen_filter by auto



lemma sup_base7b:
  assumes A0: "FilterBaseIn B X"
  shows "PiSystem (upclosure_in B X)"
  by (smt (verit, ccfv_threshold) A0 CollectD CollectI DownDirected_def FilterBaseIn_def PiSystem_def Pow_iff inf.absorb_iff2 inf.bounded_iff inf_aci(2) upclosure_in_def)

lemma sup_base8:
   assumes A0: "FilterBase \<B>"
   shows "UpClosed (upclosure \<B>)"
  by (simp add: upclosure_is_upclosed1)


lemma sup_base8b:
   assumes A0: "FilterBaseIn B X"
   shows "UpClosed_In (upclosure_in B X) X"
  by (simp add: upclosure_in_is_upclosed_in1)

lemma sup_base9:
  assumes A0: "FilterBase \<B>"
  shows "FilterOfSets (upclosure \<B>)"
  by (simp add: assms fbase_gen_filter)

(*1.70.9*)
lemma sup_base9b:
  assumes A0:"X \<noteq> {}" and A1:"B \<in> Pow (Pow X)" and A2: "FilterBaseIn B X"
  shows "FilterOfSetsIn (upclosure_in B X) X"
  using A0 A1 A2 fbase_gen_filterb by blast

lemma generated_filter:
  assumes A0:"FilterSubbase \<C>"
  shows "FilterOfSets( upclosure (fmeetclosure \<C>))"
  by (simp add: assms sup_base9 sup_subbase4) 

lemma generated_filter_in:
   assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
   shows "FilterOfSetsIn (filter_generated_by_in C X) X"
  by (metis (no_types, lifting) A0 A1 A2 CollectD PowI fbase_gen_filterb filter_generated_by_in_def fmeetclosure_in_def subsetI sup_subbase4b)



lemma fmc_monotone:
  assumes A0:"C \<in> Pow (Pow X)" and A1:"C \<noteq> {}"
  shows "C \<subseteq> (fmeetclosure_in C X)"
proof-
  have B00:"\<forall>c \<in> C. finite({c})" by simp
  have B01:"\<forall>c \<in> C. {c} \<noteq> {}" by simp 
  have B02:"\<forall>c \<in> C. ({c} \<in> (Pow C))" by auto
  have B03:"\<forall>c \<in> C. \<Inter>{c}=c" by simp
  have B04:"\<forall>c \<in> C. c \<in> (fmeetclosure_in C X)"
        by (smt (verit, ccfv_SIG) A0 B00 B01 B02 B03 CollectI PowD fmeetclosure_in_def subset_eq)
  with B04 show ?thesis
    by (simp add: subsetI)
qed


lemma finite_intersections_in_set:
  fixes X::"'X set"
  assumes A1:"C \<in> Pow(Pow (X))" and
          A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> a1 \<inter> a2 \<in> C"and 
          A3:"finite E" and
          A4:"E \<noteq> {}"  and
          A5:"E \<subseteq> C"
  shows "(\<Inter>E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    with assms show ?case
      by simp
    next
    case (insert x F)
    then have "(\<Inter>(insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C"
        using insert.prems by auto
      have P1: "F \<subseteq> C"
        using insert.prems by auto
      with A2 have P2:"x \<inter> (\<Inter>F) \<in> C"
        by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(\<Inter>F) \<in> C"
        using P1 by blast
      have  P4:"\<Inter>(insert x F) = x \<inter> (\<Inter>F)" by simp
      then show "(\<Inter>(insert x F)) \<in> C"
        by (simp add: P2)
    qed
    show ?case
      using \<open>\<Inter> (insert (x::'X set) (F::'X set set)) \<in> (C::'X set set)\<close> by auto
  qed
qed


lemma finite_union_in_set:
  fixes X::"'X set"
  assumes A1:"C \<in> Pow(Pow (X))" and
          A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> a1 \<union>  a2 \<in> C"and 
          A3:"finite E" and
          A4:"E \<noteq> {}"  and
          A5:"E \<subseteq> C"
  shows "(\<Union>E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    with assms show ?case
      by simp
    next
    case (insert x F)
    then have "(\<Union>(insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C"
        using insert.prems by auto
      have P1: "F \<subseteq> C"
        using insert.prems by auto
      with A2 have P2:"x \<union> (\<Union>F) \<in> C"
        by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(\<Union>F) \<in> C"
        using P1 by blast
      have  P4:"\<Union>(insert x F) = x \<union> (\<Union>F)" by simp
      then show "(\<Union>(insert x F)) \<in> C"
        by (simp add: P2)
    qed
    show ?case
      using \<open>\<Union> (insert (x::'X set) (F::'X set set)) \<in> (C::'X set set)\<close> by auto
  qed
qed


lemma lfil6:
  assumes A0:"(X \<noteq> {}) \<and> (F \<in> FilSpace2 X) \<and> (F \<noteq> {})" and A1:"(finite I) \<and> (I \<noteq> {})" 
  and A2:"\<forall>i \<in> I. (f i) \<in> F"
  shows "(\<Inter>(f`I)) \<in> F"
  proof-
    let ?E="(f`I)"
    have B0:"F \<in> DPow X"  by (simp add: A0 filt_pws1)
    have B1:"... =  Pow (Pow X)" by (simp add: DPow_def)
    have B2:"finite ?E" by (simp add: A1)
    have B3:"?E \<subseteq> F" by (simp add: A2 image_subsetI)
    have B4:"\<And>a1 a2. a1 \<in> F \<Longrightarrow> a2 \<in> F \<Longrightarrow> a1 \<inter> a2 \<in> F" using A0 lfil1 by blast
    have B5:"?E \<noteq> {}" by (simp add: A1)
    have B6:"(\<Inter>?E) \<in> F"  by (metis B0 B1 B2 B3 B4 B5 finite_intersections_in_set)
    with B6 show ?thesis by simp
qed

lemma lfil7:
  assumes A0:"(X \<noteq> {}) \<and> (F \<in> FilSpace2 X) \<and> (F \<noteq> {})" and A1:"(finite I) \<and> (I \<noteq> {})" 
  and A2:"((\<Inter>(f`I)) \<in> F) \<and> ((f`I) \<in> DPow X)"
  shows "\<forall>i \<in> I. (f i) \<in> F"
proof-
    let ?fI="(\<Inter>(f`I))"
    have B0:"\<forall>i \<in> I. ?fI \<subseteq> (f i)" by blast
    have B1:"?fI \<in> F" by (simp add: A2)
    have B2:"\<forall>i \<in> I.  ((f i) \<in> F)" by (meson A0 A2 INF_lower dpow_lem filt_upc rev_image_eqI)
    with B2 show ?thesis by simp
qed
  
lemma lfil8:
  assumes A0:"(X \<noteq> {}) \<and> (F \<in> FilSpace2 X) \<and> (F \<noteq> {})" and
          A1:"(finite I) \<and> (I \<noteq> {})" and
          A2:"f`I \<in> DPow X"
  shows "(\<Inter>(f`I)) \<in> F \<longleftrightarrow>  (\<forall>i \<in> I. (f i) \<in> F)"
  by (meson A0 A1 A2 lfil6 lfil7)

lemma lfil9:
   assumes A0:"(F \<in> FilSpace2 X)"
   shows "\<And>a. a \<in> Pow X \<Longrightarrow> ((\<exists>b \<in> F. b \<subseteq> a) \<longleftrightarrow> (a \<in> F))"
  using assms filt_upc by blast

lemma fmeet_idemp:
  assumes A0:"C \<in> Pow (Pow X)" and A1:"C \<noteq> {}"
  shows "(fmeetclosure_in C X) = fmeetclosure_in (fmeetclosure_in C X) X"
proof-
  let ?C1= "(fmeetclosure_in C X)"
  let ?C2= "(fmeetclosure_in ?C1 X)"
  have B0: "C \<subseteq> ?C1"
    by (metis A0 A1 fmc_monotone)
  have B1:"?C1 \<subseteq> ?C2"
    by (metis (no_types, lifting) Pow_iff empty_iff fmc_monotone fmeetclosure_in_def mem_Collect_eq subsetI)
  have B2:"?C2 \<subseteq> ?C1"
  proof
    fix a assume "a \<in> ?C2"    
    have "a \<in> Pow X"
      by (metis (no_types, lifting) CollectD \<open>(a::'a set) \<in> fmeetclosure_in (fmeetclosure_in (C::'a set set) (X::'a set)) X\<close> fmeetclosure_in_def)
    let ?r="\<lambda>a. \<lambda>C.  (\<exists>B\<in>(Pow C). (finite B) \<and> (a=\<Inter>B) \<and> (B \<noteq> {}))"
    have B20:"a \<in> ?C2 \<longleftrightarrow> (\<exists>B\<in>(Pow ?C1). (finite B) \<and> (a=\<Inter>B) \<and> (B \<noteq> {}))"
      by (smt (verit, ccfv_SIG) \<open>a \<in> Pow X\<close> fmeetclosure_in_def mem_Collect_eq)
    have B30:"a \<in> ?C1 \<longleftrightarrow> (\<exists>b\<in>(Pow C). (finite b) \<and> (a=\<Inter>b) \<and> (b \<noteq> {}))"
      by (smt (verit, ccfv_SIG) \<open>a \<in> Pow X\<close> fmeetclosure_in_def mem_Collect_eq)
    have B40:"a \<in> ?C2 \<longleftrightarrow> ?r a ?C1"
      using B20 by blast
    have B50:"d \<in> ?C1 \<longleftrightarrow> ?r d C"
      by (smt (verit, ccfv_threshold) A0 Inf_lower2 Pow_iff Set.set_insert finite_has_minimal fmeetclosure_in_def insert_subset mem_Collect_eq)
   obtain B where "(B \<in> (Pow ?C1)) \<and> finite B \<and> (a=(\<Inter>B)) \<and> (B \<noteq> {})"
     by (smt (verit, best) CollectD \<open>(a::'a set) \<in> fmeetclosure_in (fmeetclosure_in (C::'a set set) (X::'a set)) X\<close> fmeetclosure_in_def)
   have B60:"B \<in> Pow ?C1"
        using \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close> by blast
   obtain f where "f=(\<lambda>x.  SOME t. ( (is_f_many t C) \<and> (x=\<Inter>t)))"
      by simp
   have B70: "\<forall>b \<in> B. (?r b C)"
        by (smt (verit, best) CollectD PowD Set.set_insert \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close> fmeetclosure_in_def insert_subset)
   have B80:"\<forall>b \<in> B. (\<exists>t. ((is_f_many t C) \<and> (b=\<Inter>t)))"
        by (meson PowD \<open>\<forall>b::'a set\<in>B::'a set set. \<exists>B::'a set set\<in>Pow (C::'a set set). finite B \<and> b = \<Inter> B \<and> B \<noteq> {}\<close> is_f_many_def)   
   have B90:"\<forall>b \<in> B. (b=\<Inter>(f b))"
        by (metis (mono_tags, lifting) \<open>(f::'a set \<Rightarrow> 'a set set) = (\<lambda>x::'a set. SOME t::'a set set. is_f_many t (C::'a set set) \<and> x = \<Inter> t)\<close> \<open>\<forall>b::'a set\<in>B::'a set set. \<exists>t::'a set set. is_f_many t (C::'a set set) \<and> b = \<Inter> t\<close> someI)
   have B90:"\<forall>b \<in> B. (is_f_many (f b) C)"
     by (metis (mono_tags, lifting) B80 \<open>(f::'a set \<Rightarrow> 'a set set) = (\<lambda>x::'a set. SOME t::'a set set. is_f_many t (C::'a set set) \<and> x = \<Inter> t)\<close> someI)
   have B100:"\<forall>b \<in> B. (finite (f b))"
     using B90 is_f_many_def by blast
   have B110:"finite B"
     by (simp add: \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close>)    
   let ?D="\<Union>b \<in> B. (f b)"
   have B120:"finite ?D"
     using B100 B110 by blast
   have B130:"?D \<in> Pow C"
     by (meson B90 PowI UN_least is_f_many_def)
   have B140:"?D \<noteq> {}"
     using B90 \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close> is_f_many_def by fastforce
   have B150:"a=\<Inter>B"
     by (simp add: \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close>)
   have B160:"a=(\<Inter>b\<in>B. b)"
     by (simp add: B150)
   have B170:"\<forall>b \<in> B. (b=(\<Inter>(f b)))"
     by (metis (mono_tags, lifting) B80 \<open>(f::'a set \<Rightarrow> 'a set set) = (\<lambda>x::'a set. SOME t::'a set set. is_f_many t (C::'a set set) \<and> x = \<Inter> t)\<close> someI_ex)
   have B180:"a=(\<Inter>b\<in>B. (\<Inter>(f b)))"
     using B160 B170 by auto
  have B190:"a=\<Inter>?D"
    using B180 by blast
  with B120 B130 B140 B190 have B200:"a \<in> ?C1"
    using B30 by blast
  show "a \<in> ?C1"
    by (simp add: B200)
  qed
  have B3:"?C1 = ?C2"
    by (simp add: B1 B2 subset_antisym)
  with B3 show ?thesis
    by simp
qed

lemma bozowatch1:
  assumes A0:"PiSystem A" and A1:"A \<noteq> {}" and A2:"A \<in> Pow(Pow(X))"
  shows "\<forall>E \<in> Pow A. E \<noteq> {} \<longrightarrow> finite E \<longrightarrow> \<Inter>E \<in> A"
  by (metis A0 A2 PiSystem_def PowD finite_intersections_in_set)

lemma bozowatch2:
  assumes A0:"PiSystem A" and A1:"A \<noteq> {}" and A2:"A \<in> Pow(Pow(X))"
  shows "A = fmeetclosure_in A X"
proof-
  have L:"A \<subseteq> fmeetclosure_in A X"
    by (meson A1 A2 fmc_monotone)
  have R:"fmeetclosure_in A X \<subseteq> A"
  proof
    fix a assume "a \<in> fmeetclosure_in A X"
    have R0:"(a \<in> Pow X)"
      by (metis (no_types, lifting) CollectD \<open>a \<in> fmeetclosure_in A X\<close> fmeetclosure_in_def)
    have R1:"\<exists>B\<in>(Pow A). (finite B) \<and> (a=\<Inter>B) \<and> (B \<noteq> {})"
      using \<open>a \<in> fmeetclosure_in A X\<close> fmeetclosure_in_def by auto
    show "a \<in> A"
      by (metis A0 A1 A2 R1 bozowatch1)
  qed
  with L R show ?thesis by simp
qed

lemma bozowatch3:
  assumes A0:"FilterOfSetsIn F X" and A1:"F \<in> Pow (Pow X)"
  shows "F = fmeetclosure_in F X"
  by (metis A0 A1 FilterOfSetsIn_def bozowatch2)

lemma fsubbase1712:
  assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
  shows "F \<in> (FilUpSets C X) \<longrightarrow>  (filter_generated_by_in C X) \<preceq> F "
proof-
  let ?BF="(fmeetclosure_in C X)" 
  let ?EF="upclosure_in ?BF X "
  have B0:"C \<preceq> ?BF"
    by (metis A1 empty_subsetI fmc_monotone subseteq_imp_preceq)
  have B1:"?BF \<preceq> ?EF"
    by (smt (verit, del_insts) CollectD CollectI fmeetclosure_in_def preceq_def preceq_reflexive upclosure_in_def)
  have B2:"F \<in> FilUpSets C X \<longrightarrow> C \<preceq> F"
    by (simp add: FilUpSets_def)
  have B3:"F \<in> FilUpSets C X \<longrightarrow> C \<subseteq> F "
  proof
    fix Fp assume "Fp \<in> FilUpSets C X"
    have B30:"Proper Fp"
      using FilUpSets_def FilterOfSetsIn_def \<open>Fp \<in> FilUpSets C X\<close> by fastforce
    have B31:"Fp \<noteq> {}"
      using FilUpSets_def FilterOfSetsIn_def \<open>Fp \<in> FilUpSets C X\<close> by fastforce
    from A2 have B32:"Proper C"
      using FilterSubbaseIn_def by blast
    from A2 have B33:"C \<noteq> {}"
      by (simp add: FilterSubbaseIn_def)
    from B2 have B34:"C \<preceq> Fp"
      using FilUpSets_def \<open>Fp \<in> FilUpSets C X\<close> by auto
    show "C \<subseteq> Fp"
      by (smt (verit, del_insts) A1 CollectD FilUpSets_def FilterOfSetsIn_def PowD UpClosed_In_def \<open>Fp \<in> FilUpSets C X\<close> in_mono preceq_def subsetI)
  qed
  have B4:"F \<in> FilUpSets C X \<longrightarrow> ?BF \<preceq> F"
    by (smt (verit, del_insts) B3 CollectD FilUpSets_def FilterOfSetsIn_def Pow_mono bozowatch1 fmeetclosure_in_def preceq_def subset_eq)
  have B5:"F \<in> (FilUpSets C X) \<longrightarrow> ?EF \<preceq> F"
    by (smt (verit, ccfv_threshold) B4 CollectD FilUpSets_def FilterOfSetsIn_def UpClosed_In_def fmeetclosure_in_def preceq_def upclosure_in_def)
  have B6:"?EF = (filter_generated_by_in C X)"
    by (simp add: filter_generated_by_in_def)
  with B5 B6 show ?thesis
    by simp
qed


definition ewunion::"'X set set \<Rightarrow> 'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set set" where
  "(ewunion \<A> \<B> X) = {E \<in> Pow(X). \<exists>A \<in> \<A>. \<exists>B \<in> \<B>. E=A\<union>B}"


definition ewinter::"'X set set \<Rightarrow> 'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set set" where
  "(ewinter \<A> \<B> X) = {E \<in> Pow(X). \<exists>A \<in> \<A>. \<exists>B \<in> \<B>. E=A\<inter>B}"

(*1.71.1a*)
lemma ewi1:
  assumes "\<A> \<in> Pow(Pow X)" and "\<B> \<in> Pow(Pow X)" and "\<A> \<noteq> {}" and " \<B> \<noteq> {}" and "(ewinter \<A> \<B> X) \<noteq> {}"
  shows "(ewinter \<A> \<B> X) = (ewinter \<B> \<A> X)"
proof-
  have L:"(ewinter \<A> \<B> X) \<subseteq> (ewinter \<B> \<A> X)" by (smt (verit) CollectD CollectI Int_commute ewinter_def subsetI)
  have R:"(ewinter \<B> \<A> X) \<subseteq> (ewinter \<A> \<B> X)" by (smt (verit) CollectD CollectI Int_commute ewinter_def subsetI)
  with L R show ?thesis by simp 
qed
    
(*1.71.1a*)
lemma ewu1:
  assumes "\<A> \<in> Pow(Pow X)" and "\<B> \<in> Pow(Pow X)" and "\<A> \<noteq> {}" and " \<B> \<noteq> {}" and "(ewunion \<A> \<B> X) \<noteq> {}"
  shows "(ewunion \<A> \<B> X) = (ewunion \<B> \<A> X)"
proof-
  let ?L="(ewunion \<A> \<B> X)"
  let ?R="(ewunion \<B> \<A> X)"
  have LsR:"?L \<subseteq>?R"
  proof
    fix E assume A00:"E \<in> ?L"
    have A01:"\<exists>A \<in> \<A>. \<exists>B \<in> \<B>. E=A\<union>B"
      by (smt (verit) A00 CollectD ewunion_def) 
    have A02:"\<exists>B\<in>\<B>. \<exists>A\<in>\<A>. E=B\<union>A" using A01 by blast
    show "E \<in> ?R"
      by (smt (verit, ccfv_threshold) A00 A02 ewunion_def mem_Collect_eq)
  qed
  have RsL:"?R \<subseteq> ?L"
    by (smt (verit, del_insts) CollectD CollectI ewunion_def subsetI sup_commute)
  with LsR RsL show ?thesis by simp 
qed

(*1.71.1b*)
lemma ewi2:
  assumes A0:"\<A> \<in> Pow(Pow X)" and A1:"\<B> \<in> Pow(Pow X)" and A2:"\<C> \<in> Pow(Pow X)"
  and A3:"\<A> \<noteq> {}" and A4:"\<B> \<noteq> {}" and A5:"\<C> \<noteq> {}" and A6:"(ewinter \<A> (ewinter \<B> \<C>  X) X) \<noteq> {}"
  shows "(ewinter \<A> (ewinter \<B> \<C>  X) X) = (ewinter (ewinter \<A> \<B> X) \<C> X)"
proof-
  let ?BC="ewinter \<B> \<C> X" let ?AB="(ewinter \<A> \<B> X)"
  have LtR:"(ewinter (?AB) \<C> X) \<subseteq> (ewinter \<A> (?BC) X)"
  proof
    fix E assume LtR0:"E \<in> (ewinter (?AB) \<C> X)"
    obtain AB C where "AB \<in> (?AB) \<and> C \<in> \<C> \<and> (E= AB \<inter> C)" by (smt (verit) CollectD LtR0 ewinter_def)
    obtain A B where "A \<in> \<A> \<and> B \<in> \<B> \<and> (AB = A \<inter> B)" by (smt (verit) CollectD \<open>AB \<in> ewinter \<A> \<B> X \<and> C \<in> \<C> \<and> E = AB \<inter> C\<close> ewinter_def)
    have "E= (A \<inter> B \<inter> C)"
      by (simp add: \<open>A \<in> \<A> \<and> B \<in> \<B> \<and> AB = A \<inter> B\<close> \<open>AB \<in> ewinter \<A> \<B> X \<and> C \<in> \<C> \<and> E = AB \<inter> C\<close>)
    have "B \<inter> C \<in> ?BC"
      using A2 \<open>A \<in> \<A> \<and> B \<in> \<B> \<and> AB = A \<inter> B\<close> \<open>AB \<in> ewinter \<A> \<B> X \<and> C \<in> \<C> \<and> E = AB \<inter> C\<close> ewinter_def by fastforce
    show "E \<in> (ewinter \<A> (?BC) X) "
      by (metis (mono_tags, lifting) CollectD CollectI LtR0 \<open>A \<in> \<A> \<and> B \<in> \<B> \<and> AB = A \<inter> B\<close> \<open>B \<inter> C \<in> ewinter \<B> \<C> X\<close> \<open>E = A \<inter> B \<inter> C\<close> ewinter_def inf_aci(2))
  qed
  have RtL:" (ewinter \<A> (?BC) X) \<subseteq> (ewinter (?AB) \<C> X)"
  proof
    fix E assume RtL0: "E \<in> (ewinter \<A> (?BC) X)"
    then obtain A BC where "A \<in> \<A> \<and> BC \<in> ?BC \<and> E = A \<inter> BC" by (smt (verit) CollectD RtL0 ewinter_def)
    then obtain B C where "B \<in> \<B> \<and> C \<in> \<C> \<and> BC = B \<inter> C" by (smt (verit) CollectD ewinter_def)
    then have "E = A \<inter> (B \<inter> C)"
      by (simp add: \<open>A \<in> \<A> \<and> BC \<in> ewinter \<B> \<C> X \<and> E = A \<inter> BC\<close>)
    then have "E = (A \<inter> B) \<inter> C"
      by (simp add: inf_assoc)
    then have "A \<inter> B \<in> ?AB"
      by (smt (verit, best) A1 Pow_iff \<open>A \<in> \<A> \<and> BC \<in> ewinter \<B> \<C> X \<and> E = A \<inter> BC\<close> \<open>B \<in> \<B> \<and> C \<in> \<C> \<and> BC = B \<inter> C\<close> ewinter_def le_infI2 mem_Collect_eq subset_eq)
    then show "E \<in> (ewinter (?AB) \<C> X)"
      by (metis (mono_tags, lifting) CollectD CollectI RtL0 \<open>B \<in> \<B> \<and> C \<in> \<C> \<and> BC = B \<inter> C\<close> \<open>E = A \<inter> B \<inter> C\<close> ewinter_def)
  qed
  thus "(ewinter \<A> (ewinter \<B> \<C> X) X) = (ewinter (ewinter \<A> \<B> X) \<C> X)"
    by (simp add: LtR dual_order.eq_iff)
qed

(*1.71.1b*)
lemma ewu2:
  assumes A0:"\<A> \<in> Pow(Pow X)" and A1:"\<B> \<in> Pow(Pow X)" and A2:"\<C> \<in> Pow(Pow X)"
  and A3:"\<A> \<noteq> {}" and A4:"\<B> \<noteq> {}" and A5:"\<C> \<noteq> {}" and A6:"(ewunion \<A> (ewunion \<B> \<C>  X) X) \<noteq> {}"
  shows "(ewunion \<A> (ewunion \<B> \<C>  X) X) = (ewunion (ewunion \<A> \<B> X) \<C> X)"
proof-
  let ?BC="ewunion \<B> \<C> X" let ?AB="(ewunion \<A> \<B> X)"
  have LtR:"(ewunion (?AB) \<C> X) \<subseteq> (ewunion \<A> (?BC) X)"
  proof
    fix E assume LtR0:"E \<in> (ewunion (?AB) \<C> X)"
    obtain AB C where "AB \<in> (?AB) \<and> C \<in> \<C> \<and> (E= AB \<union> C)" by (smt (verit) CollectD LtR0 ewunion_def)
    obtain A B where "A \<in> \<A> \<and> B \<in> \<B> \<and> (AB = A \<union> B)" by (smt (verit) CollectD \<open>AB \<in> ewunion \<A> \<B> X \<and> C \<in> \<C> \<and> E = AB \<union> C\<close> ewunion_def)
    have "E= (A \<union> B \<union> C)"
      by (simp add: \<open>A \<in> \<A> \<and> B \<in> \<B> \<and> AB = A \<union> B\<close> \<open>AB \<in> ewunion \<A> \<B> X \<and> C \<in> \<C> \<and> E = AB \<union> C\<close>)
    have "B \<union> C \<in> ?BC"
      by (smt (verit) A1 A2 CollectI Pow_iff Un_iff \<open>A \<in> \<A> \<and> B \<in> \<B> \<and> AB = A \<union> B\<close> \<open>AB \<in> ewunion \<A> \<B> X \<and> C \<in> \<C> \<and> E = AB \<union> C\<close> ewunion_def subset_eq)
    show "E \<in> (ewunion \<A> (?BC) X) "
      by (metis (mono_tags, lifting) CollectD CollectI LtR0 \<open>A \<in> \<A> \<and> B \<in> \<B> \<and> AB = A \<union>  B\<close> \<open>B \<union> C \<in> ewunion \<B> \<C> X\<close> \<open>E = A \<union> B \<union> C\<close> ewunion_def sup_aci(2))
  qed
  have RtL:" (ewunion \<A> (?BC) X) \<subseteq> (ewunion (?AB) \<C> X)"
  proof
    fix E assume RtL0: "E \<in> (ewunion \<A> (?BC) X)"
    then obtain A BC where "A \<in> \<A> \<and> BC \<in> ?BC \<and> E = A \<union> BC" by (smt (verit) CollectD RtL0 ewunion_def)
    then obtain B C where "B \<in> \<B> \<and> C \<in> \<C> \<and> BC = B \<union> C" by (smt (verit) CollectD ewunion_def)
    then have "E = A \<union> (B \<union> C)"
      by (simp add: \<open>A \<in> \<A> \<and> BC \<in> ewunion \<B> \<C> X \<and> E = A \<union> BC\<close>)
    then have "E = (A \<union> B) \<union> C"
      by (simp add: sup_assoc)
    then have "A \<union>  B \<in> ?AB"
      by (smt (verit, ccfv_SIG) A0 A1 CollectI Pow_iff Un_subset_iff \<open>A \<in> \<A> \<and> BC \<in> ewunion \<B> \<C> X \<and> E = A \<union> BC\<close> \<open>B \<in> \<B> \<and> C \<in> \<C> \<and> BC = B \<union> C\<close> ewunion_def subsetD)
    then show "E \<in> (ewunion (?AB) \<C> X)"
      by (metis (mono_tags, lifting) CollectD CollectI RtL0 \<open>B \<in> \<B> \<and> C \<in> \<C> \<and> BC = B \<union> C\<close> \<open>E = A \<union> B \<union> C\<close> ewunion_def)
  qed
  thus "(ewunion \<A> (ewunion \<B> \<C> X) X) = (ewunion (ewunion \<A> \<B> X) \<C> X)"
    by (simp add: LtR subset_antisym)
qed

lemma lem1712a1:
  assumes A0:"A1 \<in> Pow (Pow X)" and A1:"A2 \<in> Pow (Pow X)" and
          A2:"B1 \<in> Pow (Pow X)" and A2:"B2 \<in> Pow (Pow X)" and
          A4:"A1 \<subseteq> A2" and A5:"B1 \<subseteq> B2" 
          shows "ewinter A1 B1 X \<subseteq> ewinter A2 B2 X"
  by (smt (verit, ccfv_SIG) A4 A5 CollectD CollectI ewinter_def subsetD subsetI)
      
lemma lem1712a2:
  assumes A0:"A1 \<in> Pow (Pow X)" and A1:"A2 \<in> Pow (Pow X)" and
          A2:"B1 \<in> Pow (Pow X)" and A2:"B2 \<in> Pow (Pow X)" and
          A4:"A1 \<subseteq> A2" and A5:"B1 \<subseteq> B2" 
          shows "ewunion A1 B1 X \<subseteq> ewunion A2 B2 X"
  by (smt (verit, ccfv_threshold) A4 A5 CollectD CollectI ewunion_def subsetD subsetI)
  
lemma lem1712b1:
  assumes A0:"A1 \<in> Pow (Pow X)" and A1:"A2 \<in> Pow (Pow X)" and
          A2:"B1 \<in> Pow (Pow X)" and A2:"B2 \<in> Pow (Pow X)" and
          A4:"A1 \<preceq> A2" and A5:"B1 \<preceq> B2" 
          shows "ewinter A1 B1 X \<preceq>  ewinter A2 B2 X"
proof-
  let ?A1B1="ewinter A1 B1 X" let ?A2B2="ewinter A2 B2 X"
  have P0:"\<forall>E \<in> ?A1B1. \<exists>C \<in> ?A2B2. C \<subseteq>E"
  proof
  fix E assume "E \<in> ?A1B1"
  obtain a1 b1 where "a1 \<in> A1 \<and> b1 \<in> B1 \<and> E=a1 \<inter> b1" by (smt (verit, ccfv_SIG) CollectD \<open>E \<in> ewinter A1 B1 X\<close> ewinter_def)
  from A4 obtain a2 where "a2 \<in> A2 \<and> a2 \<subseteq> a1"  by (meson \<open>a1 \<in> A1 \<and> b1 \<in> B1 \<and> E = a1 \<inter> b1\<close> preceq_def)
  from A5 obtain b2 where "b2 \<in> B2 \<and> b2 \<subseteq> b1"  by (meson \<open>a1 \<in> A1 \<and> b1 \<in> B1 \<and> E = a1 \<inter> b1\<close> preceq_def)
  have "a2 \<inter> b2 \<in> ?A2B2"
    using A2 Pow_iff \<open>a2 \<in> A2 \<and> a2 \<subseteq> a1\<close> \<open>b2 \<in> B2 \<and> b2 \<subseteq> b1\<close> ewinter_def by fastforce
  have "a2 \<inter> b2 \<subseteq> a1 \<inter> b1"
    using \<open>a2 \<in> A2 \<and> a2 \<subseteq> a1\<close> \<open>b2 \<in> B2 \<and> b2 \<subseteq> b1\<close> by blast
  have "\<exists>c \<in> ?A2B2.( c \<subseteq> (E))"
    using \<open>a1 \<in> A1 \<and> b1 \<in> B1 \<and> E = a1 \<inter> b1\<close> \<open>a2 \<inter> b2 \<in> ewinter A2 B2 X\<close> \<open>a2 \<inter> b2 \<subseteq> a1 \<inter> b1\<close> by blast
  show "\<exists>C \<in> ?A2B2. C \<subseteq>E"
    by (simp add: \<open>\<exists>c\<in>ewinter A2 B2 X. c \<subseteq> E\<close>)
  qed
  with P0 show ?thesis
    using preceq_def by blast
qed

lemma lem1712b2:
  assumes A0:"A1 \<in> Pow (Pow X)" and A1:"A2 \<in> Pow (Pow X)" and
          A2:"B1 \<in> Pow (Pow X)" and A2:"B2 \<in> Pow (Pow X)" and
          A4:"A1 \<preceq> A2" and A5:"B1 \<preceq> B2" 
          shows "ewunion A1 B1 X \<preceq>  ewunion A2 B2 X"
proof-
  let ?A1B1="ewunion A1 B1 X" let ?A2B2="ewunion A2 B2 X"
  have P0:"\<forall>E \<in> ?A1B1. \<exists>C \<in> ?A2B2. C \<subseteq>E"
  proof
  fix E assume "E \<in> ?A1B1"
  obtain a1 b1 where "a1 \<in> A1 \<and> b1 \<in> B1 \<and> E=a1 \<union> b1" by (smt (verit, ccfv_SIG) CollectD \<open>E \<in> ewunion A1 B1 X\<close> ewunion_def)
  from A4 obtain a2 where "a2 \<in> A2 \<and> a2 \<subseteq> a1"  by (meson \<open>a1 \<in> A1 \<and> b1 \<in> B1 \<and> E = a1 \<union> b1\<close> preceq_def)
  from A5 obtain b2 where "b2 \<in> B2 \<and> b2 \<subseteq> b1"  by (meson \<open>a1 \<in> A1 \<and> b1 \<in> B1 \<and> E = a1 \<union> b1\<close> preceq_def)
  have "a2 \<union> b2 \<in> ?A2B2"
    using A1 A2 \<open>a2 \<in> A2 \<and> a2 \<subseteq> a1\<close> \<open>b2 \<in> B2 \<and> b2 \<subseteq> b1\<close> ewunion_def by fastforce
  have "a2 \<union> b2 \<subseteq> a1 \<union> b1"
    using \<open>a2 \<in> A2 \<and> a2 \<subseteq> a1\<close> \<open>b2 \<in> B2 \<and> b2 \<subseteq> b1\<close> by blast
  have "\<exists>c \<in> ?A2B2.( c \<subseteq> (E))"
    using \<open>a1 \<in> A1 \<and> b1 \<in> B1 \<and> E = a1 \<union> b1\<close> \<open>a2 \<union> b2 \<in> ewunion A2 B2 X\<close> \<open>a2 \<union> b2 \<subseteq> a1 \<union> b1\<close> by blast
  show "\<exists>C \<in> ?A2B2. C \<subseteq>E"
    by (simp add: \<open>\<exists>c\<in>ewunion A2 B2 X. c \<subseteq> E\<close>)
  qed
  with P0 show ?thesis
    using preceq_def by blast
qed  

lemma lem1712c1:
  assumes A0:"A1 \<in> Pow (Pow X)" and A1:"A2 \<in> Pow (Pow X)" and
          A2:"B1 \<in> Pow (Pow X)" and A2:"B2 \<in> Pow (Pow X)" and
          A4:"A1 ~ A2" and A5:"B1 ~ B2" 
          shows "ewinter A1 B1 X ~  ewinter A2 B2 X"
  by (meson A0 A1 A2 A4 A5 assms(3) fequiv_def lem1712b1)


lemma lem1712c2:
  assumes A0:"A1 \<in> Pow (Pow X)" and A1:"A2 \<in> Pow (Pow X)" and
          A2:"B1 \<in> Pow (Pow X)" and A2:"B2 \<in> Pow (Pow X)" and
          A4:"A1 ~ A2" and A5:"B1 ~ B2" 
          shows "ewunion A1 B1 X ~  ewunion A2 B2 X"
  by (meson A0 A1 A2 A4 A5 assms(3) fequiv_def lem1712b2)

lemma lem171311:
  assumes A0:"A \<in> Pow (Pow X)" and A1:"B \<in> Pow (Pow X)" 
  shows "ewunion A B X \<preceq> A"
  by (smt (verit) CollectD Un_subset_iff dual_order.refl ewunion_def preceq_def)

lemma lem171311b:
  assumes A0:"A \<in> Pow (Pow X)" and A1:"B \<in> Pow (Pow X)" 
  shows "ewunion A B X \<preceq> B"
  by (smt (verit) CollectD PowD Pow_top Un_subset_iff ewunion_def preceq_def)



lemma lem171312:
  assumes A0:"A \<in> Pow (Pow X)" and A1:"B \<in> Pow (Pow X)" and "ewinter A B X \<noteq> {}" and "B \<noteq> {}" and "A \<noteq> {}"
  and "\<forall>a \<in> A. \<exists>b \<in>B. a \<inter>b \<noteq> {}" 
  shows "A \<preceq> ewinter A B X"
proof-
  let ?AB="ewinter A B X"
  have P:"\<forall>a\<in>A. \<exists>ab\<in>?AB. (a \<supseteq> ab)"
  proof
    fix a assume "a \<in> A"
    obtain b where "b \<in> B \<and> (a \<inter> b \<noteq> {})" by (meson \<open>a \<in> A\<close> assms(6))
    have "a \<inter> b \<in> ?AB"  using A0 \<open>a \<in> A\<close> \<open>b \<in> B \<and> a \<inter> b \<noteq> {}\<close> ewinter_def by fastforce
    have "a \<supseteq> (a \<inter> b)"  by simp
    show "\<exists>ab\<in>?AB. (a \<supseteq> ab)"  using \<open>a \<inter> b \<in> ewinter A B X\<close> \<open>a \<inter> b \<subseteq> a\<close> by blast
  qed
  with P show ?thesis by (simp add: preceq_def)
qed


lemma filter_inter:
  fixes X::"'X set" fixes FFam::"'X set set set"
  assumes A0:"X \<noteq> {}" and  A1:"FFam \<in> Pow( FilSpace X)"
  and A2:"Proper (\<Inter>FFam)"
  shows "\<Inter>FFam \<in> FilSpace X"
proof-
  let ?EF="\<Inter>FFam"
  have F00:"\<forall>Fi \<in> FFam. FilterOfSetsIn Fi X"  using A1 FilSpace_def by fastforce
  have F01:"\<forall>Fi \<in> FFam. Fi \<noteq> {}" using F00 FilterOfSetsIn_def by blast
  have F02:"\<forall>Fi \<in> FFam. X \<in> Fi" by (smt (verit) A1 CollectD FilSpace_def FilterOfSetsIn_def PowD PowI UpClosed_In_def subset_eq subset_nonempty)
  have F03:"X \<in> ?EF" by (simp add: F02)
  have F0:"?EF \<noteq> {}" using F03 by blast
  have F1:"Proper ?EF" by (simp add: A2)
  have F2:"PiSystem ?EF" by (meson F00 FilterOfSetsIn_def Inter_iff PiSystem_def)
  have F3:"UpClosed_In ?EF X" by (meson F00 FilterOfSetsIn_def Inter_iff UpClosed_In_def)
  have T1:"FilterOfSetsIn ?EF X" by (simp add: F0 F1 F2 F3 FilterOfSetsIn_def)
  have T2:"?EF \<in> Pow (Pow X)" by (smt (verit, ccfv_SIG) A1 CollectD F1 FilSpace_def Inter_iff PowD PowI Proper_def subset_eq)
  have T3:"?EF \<in> FilSpace X" using FilSpace_def T1 T2 by auto
  with T3 show ?thesis by simp
qed

declare [[show_types]]

lemma mega_bozo:
  "\<A> \<in> DPow X \<longleftrightarrow> \<A> \<in> (Pow (Pow X))"
  by (simp add: DPow_def)

lemma filter_inter2:
  fixes X::"'X set" fixes FFam::"'X set set set"
  assumes A0:"X \<noteq> {}" and  A1:"FFam \<in> Pow (FilSpace2 X)" and A2:"FFam \<noteq> {}"
  shows "\<Inter>FFam \<in> FilSpace2 X"
proof-
  let ?EF="\<Inter>FFam"
  have F00:"\<forall>Fi \<in> FFam. FilterOfSetsIn2 Fi X"  using A1 FilSpace2_def by fastforce
  have F01:"\<forall>Fi \<in> FFam. Fi \<noteq> {}" using F00 FilterOfSetsIn2_def by blast
  have F02:"\<forall>Fi \<in> FFam. X \<in> Fi" by (smt (verit) A1 CollectD FilSpace2_def DPow_def mega_bozo FilterOfSetsIn2_def PowD PowI UpClosed_In_def subset_eq subset_nonempty)
  have F03:"X \<in> ?EF" by (simp add: F02)
  have F0:"?EF \<noteq> {}" using F03 by blast
  have F2:"PiSystem ?EF" by (meson F00 FilterOfSetsIn2_def Inter_iff PiSystem_def)
  have F3:"UpClosed_In ?EF X" by (meson F00 FilterOfSetsIn2_def Inter_iff UpClosed_In_def)
  have T1:"FilterOfSetsIn2 ?EF X" by (simp add: F0 F2 F3 FilterOfSetsIn2_def)
  have T2:"FFam \<in> Pow (DPow X)" using A1 FilSpace2_def by blast
  have T3:"?EF \<in> DPow X" using A2 T2
    by (metis DPow_def Inf_lower2 IntD2 Pow_iff equals0I inf.order_iff) 
  have T4:"?EF \<in>(FilSpace2 X)" using FilSpace2_def T1 T3 by auto
  with T4 show ?thesis by simp
qed

(*(\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le>  a)\<longrightarrow> (z \<le>  m) )) *)

lemma bozowatch6:
  assumes A0:"X \<noteq> {}" and 
          A1:"FFam \<in> Pow (Pow (Pow X))" and
          A2:"F \<in> Pow (Pow X)" and
          A3:"\<forall>Fi \<in> FFam. F \<subseteq> Fi"
  shows "F \<subseteq> (\<Inter>FFam)"
  by (simp add: A3 Inter_greatest)

lemma bozowatch7:
  "FilSpace2 X \<subseteq> DPow X"
  by (simp add: FilSpace2_def)

lemma lem1761:
  assumes A0:"X \<noteq> {}" and A1:"FFam \<in> Pow( FilSpace X)" and A2:"Proper (\<Inter>FFam)"
  shows "IsInf2 (\<Inter>FFam) FFam (FilSpace X)"
proof-
  let ?EF="\<Inter>FFam"
  have B0:"?EF\<in> (FilSpace X)" by (meson A0 A1 A2 filter_inter)
  have B1:"\<forall>Fi \<in> FFam. ?EF \<subseteq> Fi" by (simp add: Inter_lower)
  have B2:"\<forall>F\<in>(FilSpace X). (\<forall>Fi \<in> FFam. (F \<subseteq> Fi)) \<longrightarrow> (F \<subseteq> ?EF)"
  proof
    fix F assume "F \<in> (FilSpace X) "
    have "IsInf2 (?EF) FFam (Pow (Pow X))" by (metis (no_types, lifting) B0 B1 CollectD FilSpace_def Inter_greatest IsInf2_def lower_bounds_are_lower_bounds2)
    have "FilSpace X \<subseteq> Pow (Pow X)" using FilSpace_def by auto
    show "(\<forall>Fi \<in> FFam. (F \<subseteq> Fi)) \<longrightarrow> (F \<subseteq> ?EF)" by (simp add: Inter_greatest)
  qed
  show ?thesis by (simp add: B0 B1 B2 IsInf2_def lower_bounds_are_lower_bounds2)
qed

lemma lem1762:
  assumes A0:"X \<noteq> {}" and A1:"FFam \<in> Pow( FilSpace2 X)" and A2:"FFam \<noteq> {}"
  shows "IsInf2 (\<Inter>FFam) FFam (FilSpace2 X)"
proof-
  let ?EF="\<Inter>FFam"
  have B0:"?EF\<in> (FilSpace2 X)" by (meson A0 A1 A2 filter_inter2)
  have B1:"\<forall>Fi \<in> FFam. ?EF \<subseteq> Fi" by (simp add: Inter_lower)
  have B2:"\<forall>F\<in>(FilSpace X). (\<forall>Fi \<in> FFam. (F \<subseteq> Fi)) \<longrightarrow> (F \<subseteq> ?EF)"
  proof
    fix F assume "F \<in> (FilSpace X) "
    have "IsInf2 (?EF) FFam (Pow (Pow X))"
      by (metis (no_types, lifting) B0 B1 CollectD DPow_def FilSpace2_def Inter_greatest IsInf2_def lower_bounds_are_lower_bounds2)
    have "FilSpace2 X \<subseteq> Pow (Pow X)" using DPow_def bozowatch7 by blast 
    show "(\<forall>Fi \<in> FFam. (F \<subseteq> Fi)) \<longrightarrow> (F \<subseteq> ?EF)" by (simp add: Inter_greatest)
  qed
  show ?thesis by (simp add: B0 B1 Inter_greatest IsInf2_def lower_bounds_are_lower_bounds2)
qed

lemma lem1763:
  assumes A0:"X \<noteq> {}" and A1:"FFam \<in> Pow( FilSpace2 X)" and A2:"FFam \<noteq> {}"
  shows "HasLowerBound1 FFam (FilSpace2 X)"
  by (metis A0 A1 A2 HasLowerBound1_def Inf_lower IsLowerBound_def emptyE filter_inter2 lower_bounds_are_lower_bounds)

lemma lem1764:
  assumes A0:"X \<noteq> {}" and A1:"FFam \<in> Pow( FilSpace2 X)" and A2:"FFam \<noteq> {}"
  shows "HasUpperBound1 FFam (FilSpace2 X)"
proof-
  let ?P="Pow X"
  have B0:"?P \<in> FilSpace2 X"
  proof-
    have B00:"(UpClosed_In ?P X) " by (simp add: UpClosed_In_def)
    have B01:"PiSystem ?P" using PiSystem_def by blast
    have B02:"?P \<noteq> {}" by (simp add: Pow_not_empty)
    show ?thesis by (simp add: B00 B01 B02 DPow_def FilSpace2_def FilterOfSetsIn2_def)
  qed
  have B1:"?P \<in> UpperBoundsIn FFam (FilSpace2 X)" by (metis A1 A2 B0 DPow_def PowD bozowatch7 in_mono ub_in_ub_set)
  show ?thesis using B1 HasUpperBound1_def by blast
qed

lemma lem1765:
  assumes A0:"X \<noteq> {}" and A1:"FFam \<in> Pow( FilSpace2 X)" and A2:"FFam \<noteq> {}"
  shows "HasAnInf1 FFam (FilSpace2 X)"
  by (metis A0 A1 A2 HasAnInf2_def has_inf1_iff_has_inf2 lem1762 subset_nonempty)

lemma lem1766:
  assumes A0:"X \<noteq> {}" and A1:"FFam \<in> Pow( FilSpace2 X)" and A2:"FFam \<noteq> {}"
  shows "HasASup1 FFam (FilSpace2 X)"
  by (metis A0 A1 A2 Pow_top bounded_above_infs_then_sups lem1764 lem1765 subset_nonempty)

lemma lem1767:
   assumes A0:"X \<noteq> {}" and A1:"I \<noteq> {}" and A2:"\<forall>i \<in> I. ((F i) \<in> (FilSpace2 X))" 
   shows "HasAnInf1 (F`(I)) (FilSpace2 X)"
  by (simp add: A0 A1 A2 image_subset_iff lem1765)

lemma lem1768:
   assumes A0:"X \<noteq> {}" and A1:"I \<noteq> {}" and A2:"\<forall>i \<in> I. ((F i) \<in> (FilSpace2 X))" 
   shows "HasASup1 (F`(I)) (FilSpace2 X)"
  by (simp add: A0 A1 A2 image_subset_iff lem1766)


lemma lem1769b:
  assumes A00:"X \<noteq> {}" and A01:"Y \<noteq> {}" and A10:"A \<in> (DPow X)" and A11:"(B \<in> DPow Y)" and A21:"UpClosed_In A X" and A22:"UpClosed_In B Y"
  shows "UpClosed_In (ewunion A B (X \<union> Y)) (X \<union> Y)"
proof-
  let ?XY="X \<union> Y"
  let ?AB="ewunion A B ?XY"
  have B0:"\<forall>c \<in> (Pow ?XY). (\<exists>ab \<in>?AB. c \<supseteq> ab) \<longrightarrow> c \<in> ?AB"
  proof
    fix c assume A3:"c \<in> (Pow ?XY)"
    show "(\<exists>ab \<in>?AB. c \<supseteq> ab) \<longrightarrow> c \<in> ?AB"
    proof
      assume A4:"(\<exists>ab \<in>?AB. c \<supseteq> ab)"
      obtain ab where A4:"ab \<subseteq> c \<and> ab \<in> ?AB"  using A4 by blast
      obtain a b where A5:"a \<in> A \<and> b \<in> B \<and> ab=a \<union> b" by (smt (verit, ccfv_SIG) A4 CollectD ewunion_def)
      have B011:"a \<subseteq> (c \<inter> X)" using A10 A4 A5 mega_bozo by auto  
      have B012:"b \<subseteq> (c \<inter> Y)" using A11 A4 A5 mega_bozo by auto
      have B021:"(ab \<inter> X) \<subseteq> X" by simp
      have B022:"(ab \<inter> Y) \<subseteq> Y" by simp
      let ?cX="c \<inter> X"
      let ?cY="c \<inter> Y"
      have B031:"?cX \<in> A" by (meson A21 A5 B011 PowI UpClosed_In_def inf_le2)
      have B032:"?cY \<in> B" by (meson A22 A5 B012 PowI UpClosed_In_def inf_le2) 
      have B04:"?cX  \<union> ?cY = c \<inter> (X \<union> Y)" by (simp add: Int_Un_distrib)
      have B05:" ... = c" using A3 by blast
      have B06:"(?cX \<union> ?cY) \<in> ?AB"by (metis (mono_tags, lifting) A3 B031 B032 B04 B05 CollectI ewunion_def) 
      show "c \<in> ?AB" using B04 B05 B06 by presburger
    qed
  qed
  with B0 show ?thesis by (simp add: UpClosed_In_def)
qed

lemma lem1769c:
  assumes A0:"X \<noteq> {}" and A10:"A \<in> (DPow X)" and A11:"(B \<in> DPow X)" and A20:"UpClosed_In A X" and A21:"UpClosed_In B X"
  shows "UpClosed_In (ewunion A B X) X"
  by (metis A0 A10 A11 A20 A21 lem1769b sup.idem)


lemma lem1769d:
  assumes A00:"X \<noteq> {}" and
          A01:"Y \<noteq> {}" and
          A10:"A \<in> (DPow X)" and 
          A11:"(B \<in> DPow Y)" and 
          A21:"UpClosed_In A X" and
          A22:"UpClosed_In B Y" and
          A3:"X \<inter> Y \<noteq> {}"
  shows "UpClosed_In (ewinter A B (X \<inter> Y)) (X \<inter> Y)"
proof-
  let ?XY="X \<inter> Y"
  let ?AB="ewinter A B ?XY"
  have B0:"\<forall>c \<in> (Pow ?XY). (\<exists>ab \<in>?AB. c \<supseteq> ab) \<longrightarrow> c \<in> ?AB"
  proof
    fix c assume A3:"c \<in> (Pow ?XY)"
    show "(\<exists>ab \<in>?AB. c \<supseteq> ab) \<longrightarrow> c \<in> ?AB"
    proof
      assume A4:"(\<exists>ab \<in>?AB. c \<supseteq> ab)"
      obtain ab where A4:"(ab \<subseteq> c) \<and> (ab \<in> ?AB)"  using A4 by blast
      obtain a b where A5:"a \<in> A \<and> b \<in> B \<and> (ab=a \<inter> b)" by (smt (verit, best) A4 CollectD ewinter_def)
      have B011:"a \<subseteq> (a \<union> c)" using A10 A4 A5 mega_bozo by auto  
      have B012:"... \<subseteq> X \<union> (X \<inter> Y)"  using A10 A3 A5 mega_bozo by auto
      have B013:"... = X" by simp
      have B014:"b \<subseteq> (b \<union> c)" using A11 A4 A5 mega_bozo by auto
      have B015:"... \<subseteq> Y \<union> (Y \<inter> X)"  using A11 A3 A5 DPow_def by auto 
      have B016:"... = Y" by simp
      have B017:"a \<union> c \<in> A"  by (metis A21 A5 B011 B012 B013 PowI UpClosed_In_def)
      have B018:"b \<union> c \<in> B" by (metis A22 A5 B014 B015 B016 PowI UpClosed_In_def) 
      have B019:"(a \<union> c) \<inter> (b \<union> c) = (a \<inter> b) \<union> (a \<inter> c) \<union> (c \<inter> b) \<union> c" by blast
      have B020:"... = c" using A4 A5 by blast
      have B021:"c \<subseteq> (X \<inter> Y)" using A3 by auto
      have B022:"\<exists>a1 \<in> A. \<exists>b1 \<in>B. c=a1 \<inter> b1" by (metis B017 B018 B019 B020)
      have B023:"c \<in> ?AB"  using A3 B022 ewinter_def by fastforce
      show "c \<in> ?AB" by (simp add: B023)
    qed
  qed
  with B0 show ?thesis by (simp add: UpClosed_In_def)
qed

lemma lem1769e:
  assumes A0:"X \<noteq> {}" and
          A10:"A \<in> (DPow X)" and 
          A11:"(B \<in> DPow X)" and 
          A20:"UpClosed_In A X" and
          A21:"UpClosed_In B X"
  shows "UpClosed_In (ewinter A B X) X"
  by (metis A0 A10 A11 A20 A21 Int_absorb lem1769d)


lemma mega_bozowatch_thesqueakuel:
  assumes A0:"X \<noteq> {}" and A1:"F1 \<in> (FilSpace2 X)" and A2:"F2 \<in>( FilSpace2 X)" and A01:"F1 \<noteq> {}" and A02:"F2 \<noteq> {}"
  shows "(Inf1 {F1, F2} (FilSpace2 X)) = {f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<union> f2}"
proof-
  let ?INF="{f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<union> f2}"
  have B0:"?INF = (ewunion F1 F2 X)" by (simp add: ewunion_def)
  have B1:"?INF \<preceq> F1" using preceq_def by fastforce
  have B2:"?INF \<preceq> F2" using preceq_def by fastforce (* by (metis A1 A2 B0 DPow_def preceq_def bozowatch7 lem171311 subsetD)*)
  have B3:"UpClosed_In ?INF X" by (metis (no_types, lifting) A0 A1 A2 B0 FilSpace2_def FilterOfSetsIn2_def lem1769c mem_Collect_eq)
  have B4:"?INF \<subseteq> F1" by (smt (verit) A1 B1 FilSpace2_def FilterOfSetsIn2_def UpClosed_In_def mem_Collect_eq preceq_def subsetI) 
  have B5:"?INF \<subseteq> F2" by (smt (verit) A2 B2 FilSpace2_def FilterOfSetsIn2_def UpClosed_In_def mem_Collect_eq preceq_def subsetI)
  have B6:"\<forall>F\<in>(FilSpace2 X). (\<forall>Fi \<in> {F1, F2}. (F \<subseteq> Fi)) \<longrightarrow> (F \<subseteq> ?INF)"
  proof
    fix F3 assume A3:"F3 \<in> (FilSpace2 X)"
    show "(\<forall>Fi \<in> {F1, F2}. (F3 \<subseteq> Fi)) \<longrightarrow> (F3 \<subseteq> ?INF)"
    proof
      assume A4:"(\<forall>Fi \<in> {F1, F2}. (F3 \<subseteq> Fi))"
      have B50:"(F3 \<subseteq> F1) \<and> (F3 \<subseteq> F2)" by (simp add: A4)
      show "F3 \<subseteq> ?INF"
      proof
        fix f3 assume A5:"f3 \<in> F3"
        obtain f1 where A6:"(f1 \<in> F1) \<and> (f1 \<subseteq> f3)" using A5 B50 by blast
        obtain f2 where A7:"(f2 \<in> F2) \<and> (f2 \<subseteq> f3)" using A5 B50 by blast 
        have B51:"f1 \<union> f2 \<subseteq> f3" by (simp add: A6 A7)
        have B52:"f1 \<union> f2 \<in> ?INF" using A1 A2 A6 A7 DPow_def bozowatch7 by auto
        show "f3 \<in> ?INF" using A3 A5 B50 DPow_def FilSpace2_def by blast
      qed
    qed
  qed
  have B7:"\<forall>Fi \<in> {F1, F2}. ?INF \<subseteq> Fi"  using B4 B5 by auto
  have B8:"\<forall>a \<in> ?INF. \<forall>b \<in> ?INF. a \<inter> b \<in>?INF "
  proof
    fix a assume B80:"a \<in> ?INF"
    obtain a1 a2 where B81:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> a=a1 \<union> a2" using B80 by blast
    show "\<forall>b \<in> ?INF. a \<inter> b \<in> ?INF"
    proof
      fix b assume B82:"b \<in> ?INF"
      obtain b1 b2 where B83:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> b=b1 \<union> b2" using B82 by blast
      have B84:"(a1 \<union> a2) \<inter> (b1 \<union> b2) = (a1 \<inter> b1) \<union> (a1 \<inter> b2) \<union> (a2 \<inter> b1) \<union> (a2 \<inter> b2)" by fastforce
      let ?a1b1="a1 \<inter> b1"  let ?a2b2="a2 \<inter> b2" let ?c="?a1b1 \<union> ?a2b2"
      have B85:"... \<supseteq> ?a1b1 \<union> ?a2b2" by auto 
      have B86:"\<forall>a1 \<in> F1. \<forall>b1 \<in> F1. a1 \<inter> b1 \<in> F1" by (smt (verit) A1 FilSpace2_def FilterOfSetsIn2_def PiSystem_def mem_Collect_eq)
      have B87:"\<forall>a2 \<in> F2. \<forall>b2 \<in> F2. a2 \<inter> b2 \<in> F2" by (smt (verit) A2 FilSpace2_def FilterOfSetsIn2_def PiSystem_def mem_Collect_eq)
      have B88:"?a1b1 \<in> F1" by (simp add: B81 B83 B86)
      have B89:"?a2b2 \<in> F2" by (simp add: B81 B83 B87) 
      have B810:"?c \<subseteq> a \<inter> b" using B81 B83 by blast
      show "a \<inter>b \<in> ?INF" by (smt (verit) B4 B5 B80 B82 B86 B87 CollectD CollectI Int_Un_eq(3) Pow_iff Un_Int_eq(4) Un_subset_iff subset_eq)
    qed
  qed
  have B9:"PiSystem ?INF" using B8 PiSystem_def by blast
  have B10:"?INF \<noteq> {}"
  proof-
    have B100:"\<exists>a \<in> Pow X. a \<in> F1" using A01 A1 DPow_def UnCI bozowatch7 by fastforce
    have B101:"\<exists>a \<in> Pow X. a \<in> F2" using A02 A2 DPow_def UnCI bozowatch7 by fastforce
    have B102:"X \<in> F1" by (metis (no_types, lifting) A1 B100 CollectD FilSpace2_def FilterOfSetsIn2_def PowD Pow_top UpClosed_In_def)
    have B103:"X \<in> F2" by (metis (no_types, lifting) A2 B101 CollectD FilSpace2_def FilterOfSetsIn2_def PowD Pow_top UpClosed_In_def)
    have B104:"X \<in> ?INF" using B102 B103 by blast
    show ?thesis using B104 by blast
  qed
  have B11:"?INF \<in> (FilSpace2 X)" by (metis (no_types, lifting) A1 B10 B3 B4 B9 CollectI DPow_def FilSpace2_def FilterOfSetsIn2_def Pow_iff bozowatch7 in_mono subset_trans)
  have B12:"IsInf2 ?INF {F1, F2} (FilSpace2 X)" by (smt (verit) B11 B6 B7 IsInf2_def lower_bounds_are_lower_bounds2)
  show ?thesis
    by (smt (verit) B12 Inf1_def IsInf2_def lower_bounds_are_lower_bounds2 maximum_is_greatest)
qed     
    

lemma mega_bozowatch_thechipwrecked1:
  assumes A0:"X \<noteq> {}" and A1:"F1 \<in> (FilSpace2 X)" and A2:"F2 \<in>( FilSpace2 X)" and A01:"F1 \<noteq> {}" and A02:"F2 \<noteq> {}"
  shows "PiSystem {f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<inter> f2}"
proof-
  let ?SUP="{f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<inter> f2}"    
  have B0:"\<forall>a \<in> ?SUP. \<forall>b \<in> ?SUP. a \<inter> b \<in>?SUP "
  proof
    fix a assume B01:"a \<in> ?SUP"
    obtain a1 a2 where B02:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> a=a1 \<inter> a2" using B01 by blast
    show "\<forall>b \<in> ?SUP. a \<inter> b \<in> ?SUP"
    proof
      fix b assume B03:"b \<in> ?SUP"
      obtain b1 b2 where B04:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> b=b1 \<inter> b2" using B03 by blast
      have B05:"(a1 \<inter> a2) \<inter> (b1 \<inter> b2) = (a1 \<inter> b1 ) \<inter> (a2 \<inter> b2)" by fastforce
      have B06:"(a1 \<inter> b1) \<in> F1" by (metis (no_types, lifting) A1 B02 B04 FilSpace2_def FilterOfSetsIn2_def PiSystem_def mem_Collect_eq)
      have B07:"(a2 \<inter> b2) \<in> F2" by (metis (no_types, lifting) A2 B02 B04 FilSpace2_def FilterOfSetsIn2_def PiSystem_def mem_Collect_eq)
      have B08:"(a1 \<inter> b1 ) \<inter> (a2 \<inter> b2) \<in> ?SUP" using B03 B04 B06 B07 by blast
      show B09:"a \<inter> b \<in> ?SUP" using B02 B04 B05 B08 by presburger
    qed
  qed
  with B0 show ?thesis by (meson PiSystem_def)
qed



lemma lem171311c:
  assumes A0:"A \<in> FilSpace2 X" and
          A1:"B \<in> FilSpace2 X" and 
          A2:"\<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b \<noteq> {}" and
          A3:"X \<noteq> {}"
  shows "A \<preceq> ewinter A B X"
proof-
  let ?C="ewinter A B X"
  have B0:"\<forall>a \<in> A. \<exists>c \<in> ?C. c \<subseteq> a"
  proof 
    fix a assume A4:"a \<in> A"
    show "\<exists>c \<in> ?C. c \<subseteq> a"
    proof-
      have B01:"X \<in> B" by (simp add: A1 A3 filt_univ) 
      have B02:"(a \<inter> X) \<in> ?C" using A4 B01 ewinter_def by fastforce
      have B03:"(a \<inter> X)\<subseteq>a" by simp
      show "\<exists>c \<in> ?C. c \<subseteq> a"  using B02 B03 by blast
    qed
  qed
  show ?thesis by (simp add: B0 preceq_def)
qed

lemma lem171311d:
  assumes A0:"A \<in> FilSpace2 X" and
          A1:"B \<in> FilSpace2 X" and 
          A2:"\<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b \<noteq> {}" and
          A3:"X \<noteq> {}"
  shows "B \<preceq> ewinter A B X"
  by (smt (verit) A0 A1 A2 A3 Int_commute bozowatch7 ewi1 filt_ne lem171311c mega_bozo subsetD)

lemma lem171311e:
  assumes A0:"X \<noteq> {}" and
          A1:"A \<in> FilSpace2 X" and
          A2:"B \<in> FilSpace2 X" and
          A3:"C \<in> DPow X" and
          A4:"PiSystem C" and
          A5:"\<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b \<noteq> {}" and
          A6:"A \<preceq> C \<and> B \<preceq> C"
  shows "(ewinter A B X) \<preceq> C"
proof-
  let ?AB="(ewinter A B X)"
  have B0:"\<forall>ab \<in> ?AB. \<exists>c \<in> C.  c \<subseteq> ab "
  proof
    fix ab assume A7:"ab \<in> ?AB"
    show "\<exists>c \<in> C. c \<subseteq> ab"
    proof-
      obtain a b  where A8:"a \<in> A \<and> b \<in> B \<and> a \<inter> b=ab" by (smt (verit, del_insts) A7 CollectD ewinter_def)
      obtain ca cb where A9:"ca \<in> C \<and> cb \<in> C \<and> ca \<subseteq> a \<and> cb \<subseteq> b" by (meson A6 A8 preceq_def)
      have B01:"ca \<inter> cb \<subseteq> a \<inter> b" using A9 by blast
      have B02:"... = ab" by (simp add: A8)
      have B03:"ca \<inter> cb \<in> C" by (meson A4 A9 PiSystem_def)
      have B04:"\<exists>c \<in> C. c \<subseteq> ab" using A8 B01 B03 by blast
      show ?thesis  by (simp add: B04)
    qed
  qed
  show ?thesis by (simp add: B0 preceq_def)
qed


lemma mega_bozowatch_thechipwrecked:
  assumes A0:"X \<noteq> {}" and A1:"F1 \<in> (FilSpace2 X)" and A2:"F2 \<in>( FilSpace2 X)" and
           A01:"F1 \<noteq> {}" and
           A02:"F2 \<noteq> {}" and
           A03:"\<forall>f1 \<in> F1. \<forall>f2 \<in> F2. f1 \<inter> f2 \<noteq> {}"
  shows "(Sup1 {F1, F2} (FilSpace2 X)) = {f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<inter> f2}"
proof-
  let ?SUP="{f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<inter> f2}"
  have P0:"?SUP=ewinter F1 F2 X" by (simp add: ewinter_def)
  have P1:"PiSystem {f \<in> Pow X. \<exists>f1 \<in> F1. \<exists>f2 \<in> F2. f=f1 \<inter> f2}"
  proof-
    have B0:"\<forall>a \<in> ?SUP. \<forall>b \<in> ?SUP. a \<inter> b \<in>?SUP "
    proof
      fix a assume B01:"a \<in> ?SUP"
      obtain a1 a2 where B02:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> a=a1 \<inter> a2" using B01 by blast
      show "\<forall>b \<in> ?SUP. a \<inter> b \<in> ?SUP"
      proof
        fix b assume B03:"b \<in> ?SUP"
        obtain b1 b2 where B04:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> b=b1 \<inter> b2" using B03 by blast
        have B05:"(a1 \<inter> a2) \<inter> (b1 \<inter> b2) = (a1 \<inter> b1 ) \<inter> (a2 \<inter> b2)" by fastforce
        have B06:"(a1 \<inter> b1) \<in> F1" by (metis (no_types, lifting) A1 B02 B04 FilSpace2_def FilterOfSetsIn2_def PiSystem_def mem_Collect_eq)
        have B07:"(a2 \<inter> b2) \<in> F2" by (metis (no_types, lifting) A2 B02 B04 FilSpace2_def FilterOfSetsIn2_def PiSystem_def mem_Collect_eq)
        have B08:"(a1 \<inter> b1 ) \<inter> (a2 \<inter> b2) \<in> ?SUP" using B03 B04 B06 B07 by blast
        show B09:"a \<inter> b \<in> ?SUP" using B02 B04 B05 B08 by presburger
      qed
    qed
    with B0 show ?thesis by (meson PiSystem_def)
  qed
  have P2:"UpClosed_In (ewinter F1 F2 X) X" by (metis (no_types, lifting) A0 A1 A2 CollectD FilSpace2_def FilterOfSetsIn2_def lem1769e)
  have P3:"UpClosed_In ?SUP X" using P0 P2 by auto
  have P4:"?SUP \<noteq> {}" by (metis (mono_tags, lifting) A0 A1 A2 CollectI PowD Pow_top bex_empty filt_univ inf.absorb_iff1)
  have P5:"PiSystem ?SUP"  using P1 by auto
  have P6:"FilterOfSetsIn2 ?SUP X" using FilterOfSetsIn2_def P3 P4 P5 by blast
  have P7:"?SUP \<in> DPow X" by (simp add: Collect_mono_iff Pow_def mega_bozo)
  have P8:"?SUP \<in> FilSpace2 X" using FilSpace2_def P6 P7 by blast
  have P9:"\<forall>F\<in>(FilSpace2 X). (\<forall>Fi \<in> {F1, F2}. (Fi \<subseteq> F)) \<longrightarrow> (?SUP \<subseteq> F)"
  proof
    fix F assume P9A0:"F\<in>(FilSpace2 X)"
    show "(\<forall>Fi \<in> {F1, F2}. (Fi \<subseteq> F)) \<longrightarrow> (?SUP \<subseteq> F)"
    proof
      assume P9A1:"(\<forall>Fi \<in> {F1, F2}. (Fi \<subseteq> F))"
      show "(?SUP \<subseteq> F)"
      proof-
        have P90:"F1 \<subseteq> F"  using P9A1 by blast
        have P91:"F2 \<subseteq> F" by (simp add: P9A1) 
        have P92:"F1 \<preceq> F" by (simp add: P90 subseteq_imp_preceq)
        have P93:"F2 \<preceq> F" by (simp add: P91 subseteq_imp_preceq)
        have P94:"(ewinter F1  F2 X) \<preceq> F"
          by (metis (no_types, lifting) A0 A03 A1 A2 FilSpace2_def FilterOfSetsIn2_def P92 P93 P9A0 lem171311e mem_Collect_eq)
        show ?thesis
          by (metis (no_types, lifting) A0 FilSpace2_def FilterOfSetsIn2_def P0 P4 P7 P94 P9A0 mem_Collect_eq upclosed_then_preceq_imp_subseteq2)
      qed
    qed
  qed
  have B7:"\<forall>Fi \<in> {F1, F2}. Fi \<subseteq> ?SUP"
    by (metis (no_types, lifting) A0 A01 A02 A03 A1 A2 P0 P3 P4 P7 bozowatch7 in_mono insertE lem171311c lem171311d singleton_iff upclosed_then_preceq_imp_subseteq2)
  have B8:"IsSup2 ?SUP {F1, F2} (FilSpace2 X)"
    by (smt (verit, ccfv_SIG) B7 IsSup2_def P8 P9 upper_bounds_are_upper_bounds2)
  show ?thesis
    by (smt (verit) B8 IsSup2_def Sup1_def element_lb_is_least_alt upper_bounds_are_upper_bounds2)
qed

definition fcl::"('X set set \<Rightarrow> 'X set set) \<Rightarrow> 'X set set set \<Rightarrow> bool" where
  "fcl = (\<lambda>E. \<lambda>X.  filter_generated_by_in E X)"

        
lemma fil_closure:
  "closure_on (\<lambda>E. filter_generated_by_in E X) (DPow X)"

end
