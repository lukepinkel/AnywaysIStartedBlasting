theory Posets2
  imports Main
begin

section Definitions
subsection MaxAndMin

definition IsMaximal:: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "IsMaximal m X \<equiv> (m \<in> X) \<and> (\<forall>x \<in> X. m\<le> x \<longrightarrow> m=x)"

definition IsMinimal:: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "IsMinimal m X \<equiv> (m \<in> X) \<and> (\<forall>x \<in> X. m\<le> x \<longrightarrow> m=x)"

definition IsUpperBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "IsUpperBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  a\<le>m)"

definition IsLowerBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "IsLowerBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  m\<le>a)"

definition IsMaximum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "IsMaximum m X \<equiv> IsUpperBound m X X"

definition IsMinimum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "IsMinimum m X \<equiv> IsLowerBound m X X"

definition HasMaximal::" 'X::order set  \<Rightarrow>  bool" where
  "HasMaximal A \<equiv> \<exists>m. IsMaximal m A"

definition HasMinimal::" 'X::order set  \<Rightarrow>  bool" where
  "HasMinimal A \<equiv> \<exists>m. IsMinimal m A"


definition HasUB::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "HasUB A X \<equiv> \<exists>u. IsUpperBound u A X"

definition HasLB::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "HasLB A X \<equiv> \<exists>l. IsLowerBound l A X"

definition HasMaximum::"'X::order set  \<Rightarrow>  bool" where
  "HasMaximum A \<equiv> \<exists>m \<in> A. \<forall>a \<in> A. a\<le>m"

definition HasMinimum::" 'X::order set  \<Rightarrow>  bool" where
  "HasMinimum A \<equiv> \<exists>m \<in> A. \<forall>a \<in> A. m\<le>a"

definition UpperBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "UpperBounds A X = {u \<in> X. IsUpperBound u A X }"

definition LowerBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "LowerBounds A X = {l \<in> X. IsLowerBound l A X }"

definition IsSup::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsSup s A X \<equiv> (s \<in> UpperBounds A X) \<and> (IsMinimum s ( UpperBounds A X))"

definition IsInf::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsInf i A X \<equiv> (i \<in> LowerBounds A X) \<and> (IsMaximum i ( LowerBounds A X))"

definition HasSup::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "HasSup A X \<equiv> \<exists>s. IsSup s A X"

definition HasInf::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where
  "HasInf A X \<equiv> \<exists>i. IsInf i A X"

definition IsBoundedPoset::"'X::order set \<Rightarrow> bool" where
  "IsBoundedPoset X \<equiv> (X \<noteq> {}) \<and> (HasMaximum X) \<and> (HasMinimum X)"

definition IsDownset::"'X::order set\<Rightarrow>'X::order set \<Rightarrow> bool" where
  "IsDownset D X \<equiv> (D \<in> Pow X) \<and> (\<forall>x \<in> X. \<forall>d \<in> D. x\<le>d \<longrightarrow> x \<in> D)"

definition IsUpset::"'X::order set\<Rightarrow>'X::order set \<Rightarrow> bool" where
  "IsUpset U X \<equiv> (U \<in> Pow X) \<and> (\<forall>x \<in> X. \<forall>u \<in> U. u\<le>x \<longrightarrow> x \<in> U)"

definition DownSets::"'X::order set \<Rightarrow>  'X::order set set" where
   "DownSets X = {D\<in>(Pow X). IsDownset D X }"

definition UpSets::"'X::order set \<Rightarrow>  'X::order set set" where
  "UpSets X = {U\<in>(Pow X). IsUpset U X }"
 

definition DownClosure::"'X::order set \<Rightarrow>  'X::order set\<Rightarrow>'X::order set" where
   "DownClosure A X = {x \<in> X. \<exists>a \<in> A. x \<le> a }"

definition UpClosure::"'X::order set \<Rightarrow>  'X::order set\<Rightarrow>'X::order set" where
   "UpClosure A X = {x \<in> X. \<exists>a \<in> A. a \<le> x }"
 
definition PrincipalDownClosure::"'X::order \<Rightarrow>'X::order set \<Rightarrow> 'X::order set" where
   "PrincipalDownClosure x X = (DownClosure {x} X)"

definition PrincipalUpClosure::"'X::order \<Rightarrow>'X::order set \<Rightarrow> 'X::order set" where
   "PrincipalUpClosure x X = (UpClosure {x} X)"





section Lemmas

lemma lem0:"IsMaximum X (Pow X)"
  by (metis IsMaximum_def IsUpperBound_def Pow_iff Pow_top)

lemma lem1:"X \<noteq> {} \<longrightarrow> (((D \<in> DownSets E)  \<and>( E \<in> DownSets X)) \<longrightarrow>( D \<in> DownSets X))"
  by (smt (verit) DownSets_def IsDownset_def Pow_iff in_mono mem_Collect_eq subsetI)

lemma lem2:"X \<noteq> {} \<longrightarrow> (((D \<in> UpSets E)  \<and>( E \<in> UpSets X)) \<longrightarrow>( D \<in> UpSets X))"
  by (smt (verit, del_insts) IsUpset_def Pow_iff UpSets_def in_mono mem_Collect_eq subsetI)

lemma lem3:"X \<noteq> {} \<longrightarrow> (\<forall>D \<in> Pow X. IsDownset D X \<longleftrightarrow> IsUpset (X-D) X)"
  by (smt (verit) Diff_iff Diff_subset IsDownset_def IsUpset_def Pow_iff in_mono)

lemma lem4:
  assumes A0:"X \<noteq> {}"  and
          A1:"\<D> \<in> Pow (DownSets X)"
  shows "\<Union>\<D> \<in> DownSets X"
proof-
  let ?D="\<Union>\<D>"
  have B0:"\<forall>d \<in> X. (d \<in> ?D \<longleftrightarrow> (\<exists>D \<in>\<D>. d \<in> D))" by simp
  have B1:"\<forall>x \<in> X. (\<forall>d \<in>?D. (x\<le> d) \<longrightarrow> (\<exists>D \<in>\<D>. x \<in> D))"
    by (smt (verit, best) A1 DownSets_def IsDownset_def Pow_iff UnionE in_mono mem_Collect_eq)
  have B2:"\<forall>x \<in> X. (\<forall>d \<in>?D. (x\<le> d) \<longrightarrow> x \<in> ?D)" using B1 by blast
  have B3:"\<forall>d \<in> ?D. d \<in> X"  using A1 DownSets_def by blast
  have B4:"?D \<in> Pow X"  using B3 by blast
  from B2 IsDownset_def B3 B4 have B5:"IsDownset ?D X" by metis
  have B6:"?D \<in> DownSets X"
    using B4 B5 DownSets_def by auto
  with B6 show ?thesis by simp
qed




lemma lem4_dual:
  assumes A0:"X \<noteq> {}"  and
          A1:"\<U> \<in> Pow (UpSets X)" and
          A2:"\<Inter>\<U> \<in> Pow X"
  shows "\<Inter>\<U> \<in> UpSets X"
proof-
  let ?U="\<Inter>\<U>"
  have B0:"\<forall>u \<in> X. (u \<in> ?U \<longleftrightarrow> (\<forall>U \<in>\<U>. u \<in> U))" by simp
  have B1:"\<forall>x \<in> X. (\<forall>u \<in>?U. (u \<le> x) \<longrightarrow> (\<forall>U \<in>\<U>. x \<in> U))"
    by (smt (verit, best) A1 UpSets_def IsUpset_def Pow_iff InterE in_mono mem_Collect_eq)
  have B2:"\<forall>x \<in> X. (\<forall>u \<in>?U. (u \<le> x) \<longrightarrow> x \<in> ?U)" using B1 by blast
  have B3:"\<forall>u \<in> ?U. u \<in> X"  using A1 A2 UpSets_def by blast
  have B4:"\<Inter>\<U> \<in> Pow X"  using B3 by blast
  from B2 IsUpset_def B3 B4 have B5:"IsUpset ?U X" by metis
  have B6:"?U \<in> UpSets X"
    using B4 B5 UpSets_def by auto
  with B6 show ?thesis by simp
qed


end