theory Top1
  imports Main
begin

definition ArbitraryUnionClosed::"'X set set \<Rightarrow> bool" where
  "ArbitraryUnionClosed \<A> \<equiv> (\<forall>\<E>. (\<forall>E \<in> \<E>. E \<in> \<A>) \<longrightarrow> (\<Union>\<E>) \<in> \<A>)"

definition FiniteIntersectionClosed::"'X set set \<Rightarrow> bool" where
  "FiniteIntersectionClosed \<A> \<equiv> (\<forall>\<E>. ((finite \<E>) \<and> (\<forall>E \<in> \<E>. E \<in> \<A>)) \<longrightarrow> (\<Inter>\<E>) \<in> \<A>)"

definition FiniteUnionClosed::"'X set set \<Rightarrow> bool" where
  "FiniteUnionClosed \<A> \<equiv> (\<forall>\<E>. ((finite \<E>) \<and> (\<forall>E \<in> \<E>. E \<in> \<A>)) \<longrightarrow> (\<Union>\<E>) \<in> \<A>)"



definition IsATopology::"'X set \<Rightarrow> 'X set set \<Rightarrow> bool" where
   "IsATopology X \<T> \<equiv> (X \<in> \<T>) \<and> ({} \<in>  \<T>) \<and> 
                      (ArbitraryUnionClosed \<T>) \<and>
                      (FiniteIntersectionClosed \<T>)"

lemma finint_app1:
  "FiniteIntersectionClosed A \<longrightarrow>( \<forall>a \<in>A. \<forall>b \<in>A. a \<inter> b \<in> A)"
proof-
  have B0:"FiniteIntersectionClosed A \<longrightarrow>( \<forall>a \<in>A. \<forall>b \<in>A. (\<forall>E \<in> {a, b}. E \<in> A))" by auto
  have B1:"FiniteIntersectionClosed A \<longrightarrow> ( \<forall>a \<in>A. \<forall>b \<in>A. (finite {a, b}))" by simp
  have B2:"FiniteIntersectionClosed A \<longrightarrow>  (\<forall>a \<in>A. \<forall>b \<in>A. (\<Inter>{a, b}) \<in> A)" using B1 FiniteIntersectionClosed_def by blast
  have B3:"FiniteIntersectionClosed A \<longrightarrow>( \<forall>a \<in>A. \<forall>b \<in>A. a \<inter> b \<in> A)" using B2 by force
  with B3 show ?thesis by simp
qed

lemma finun_app1:
  "FiniteUnionClosed A \<longrightarrow>( \<forall>a \<in>A. \<forall>b \<in>A. a \<union> b \<in> A)"
proof-
  have B0:"FiniteUnionClosed A \<longrightarrow>( \<forall>a \<in>A. \<forall>b \<in>A. (\<forall>E \<in> {a, b}. E \<in> A))" by auto
  have B1:"FiniteUnionClosed A \<longrightarrow> ( \<forall>a \<in>A. \<forall>b \<in>A. (finite {a, b}))" by simp
  have B2:"FiniteUnionClosed A \<longrightarrow>  (\<forall>a \<in>A. \<forall>b \<in>A. (\<Union>{a, b}) \<in> A)" using B1 FiniteUnionClosed_def by blast
  have B3:"FiniteUnionClosed A \<longrightarrow>( \<forall>a \<in>A. \<forall>b \<in>A. a \<union> b \<in> A)" using B2 by force
  with B3 show ?thesis by blast
qed

end