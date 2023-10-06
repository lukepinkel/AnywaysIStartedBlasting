theory Posets2
  imports Main
begin

section Definitions
subsection MaxAndMin

definition IsMaximal:: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where "IsMaximal m X \<equiv> (m \<in> X) \<and> (\<forall>x \<in> X. m\<le> x \<longrightarrow> m=x)"

definition IsMinimal:: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where"IsMinimal m X \<equiv> (m \<in> X) \<and> (\<forall>x \<in> X. m\<le> x \<longrightarrow> m=x)"

definition IsUpperBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsUpperBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  a\<le>m)"

definition IsLowerBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsLowerBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  m\<le>a)"

definition IsMaximum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsMaximum m X \<equiv> IsUpperBound m X X"

definition IsMinimum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsMinimum m X \<equiv> IsLowerBound m X X"

definition HasMaximal::" 'X::order set  \<Rightarrow>  bool" where "HasMaximal A \<equiv> \<exists>m. IsMaximal m A"

definition HasMinimal::" 'X::order set  \<Rightarrow>  bool" where "HasMinimal A \<equiv> \<exists>m. IsMinimal m A"

definition HasUB::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasUB A X \<equiv> \<exists>u. IsUpperBound u A X"

definition HasLB::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasLB A X \<equiv> \<exists>l. IsLowerBound l A X"

definition HasMaximum::"'X::order set  \<Rightarrow>  bool" where  "HasMaximum A \<equiv> \<exists>m \<in> A. \<forall>a \<in> A. a\<le>m"

definition HasMinimum::" 'X::order set  \<Rightarrow>  bool" where "HasMinimum A \<equiv> \<exists>m \<in> A. \<forall>a \<in> A. m\<le>a"

definition UpperBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where "UpperBounds A X = {u \<in> X. IsUpperBound u A X }"

definition LowerBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where "LowerBounds A X = {l \<in> X. IsLowerBound l A X }"

definition IsSup::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where "IsSup s A X \<equiv> (s \<in> UpperBounds A X) \<and> (IsMinimum s ( UpperBounds A X))"

definition IsInf::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where "IsInf i A X \<equiv> (i \<in> LowerBounds A X) \<and> (IsMaximum i ( LowerBounds A X))"

definition HasSup::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasSup A X \<equiv> \<exists>s. IsSup s A X"

definition HasInf::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasInf A X \<equiv> \<exists>i. IsInf i A X"

definition IsBoundedPoset::"'X::order set \<Rightarrow> bool" where "IsBoundedPoset X \<equiv> (X \<noteq> {}) \<and> (HasMaximum X) \<and> (HasMinimum X)"

definition IsDownset::"'X::order set\<Rightarrow>'X::order set \<Rightarrow> bool" where  "IsDownset D X \<equiv> (D \<in> Pow X) \<and> (\<forall>x \<in> X. \<forall>d \<in> D. x\<le>d \<longrightarrow> x \<in> D)"

definition IsUpset::"'X::order set\<Rightarrow>'X::order set \<Rightarrow> bool" where "IsUpset U X \<equiv> (U \<in> Pow X) \<and> (\<forall>x \<in> X. \<forall>u \<in> U. u\<le>x \<longrightarrow> x \<in> U)"

definition DownSets::"'X::order set \<Rightarrow>  'X::order set set" where "DownSets X = {D\<in>(Pow X). IsDownset D X }"

definition UpSets::"'X::order set \<Rightarrow>  'X::order set set" where "UpSets X = {U\<in>(Pow X). IsUpset U X }"
 
definition DownClosure::"'X::order set \<Rightarrow>  'X::order set\<Rightarrow>'X::order set" where "DownClosure A X = {x \<in> X. \<exists>a \<in> A. x \<le> a }"

definition UpClosure::"'X::order set \<Rightarrow>  'X::order set\<Rightarrow>'X::order set" where "UpClosure A X = {x \<in> X. \<exists>a \<in> A. a \<le> x }"
 
definition PrincipalDownClosure::"'X::order \<Rightarrow>'X::order set \<Rightarrow> 'X::order set" where "PrincipalDownClosure x X = (DownClosure {x} X)"

definition PrincipalUpClosure::"'X::order \<Rightarrow>'X::order set \<Rightarrow> 'X::order set" where "PrincipalUpClosure x X = (UpClosure {x} X)"

definition ftriple::"('X \<Rightarrow> 'Y) \<Rightarrow> 'X set \<Rightarrow> 'Y set \<Rightarrow> bool " where "ftriple f X Y \<equiv> (\<forall>x \<in>X. f x \<in> Y)"

definition antitone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow> bool " where "antitone f X Y \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x2 \<le> f x1))"

definition isotone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow> bool " where "isotone f X Y \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x1 \<le> f x2))"


section Lemmas

lemma lemf1: "ftriple f X Y \<longrightarrow> (\<forall>A \<in> Pow X. f`A \<in> Pow Y)" by (metis PowI UnionI Union_Pow_eq ftriple_def image_subsetI)

lemma lemf2: "ftriple f X Y \<longrightarrow> (\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y)" by (meson PowD PowI lemf1)

lemma lemf3: "(\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y) \<longrightarrow> ftriple f X Y " by (meson ftriple_def image_subset_iff order_refl)

lemma lemf4: " (\<forall>A \<in> Pow X. f`A \<in> Pow Y) \<longrightarrow>  ftriple f X Y" by (meson PowD PowI lemf3)

lemma upper_bounds_lem0:"UpperBounds A X \<subseteq> X" by (simp add: UpperBounds_def)
lemma upper_bounds_lem1:"UpperBounds A X \<in> Pow X" by (simp add: UpperBounds_def)
lemma upper_bounds_lem2:"\<forall>x \<in>X. (x \<in> UpperBounds A X \<longleftrightarrow> IsUpperBound x A X)"  by (simp add: UpperBounds_def)
lemma upper_bounds_lem3:"\<forall>x \<in>UpperBounds A X. \<forall>a \<in>A. a\<le>x" by (metis IsUpperBound_def subset_iff upper_bounds_lem0 upper_bounds_lem2) 
lemma upper_bounds_lem4:"x \<in>UpperBounds A X \<longrightarrow> ( \<forall>a \<in>A. a\<le>x)" by (simp add: upper_bounds_lem3) 

lemma upper_bounds_lem5:"IsUpset (UpperBounds A X) X"
proof-
  have B0:"\<forall>u \<in> UpperBounds A X. \<forall>a \<in> A. a\<le>u" by (simp add: upper_bounds_lem3)
  have B1:"\<forall>x \<in> X. ((\<exists>u \<in> UpperBounds A X. x \<ge> u) \<longrightarrow>(\<forall>a \<in> A. a \<le> x)) " by (meson B0 dual_order.trans)
  have B2:"\<forall>x \<in> X. ((\<exists>u \<in> UpperBounds A X. x \<ge> u) \<longrightarrow>(x \<in> UpperBounds A X))" by (meson B1 IsUpperBound_def upper_bounds_lem2)
  have B3:"IsUpset (UpperBounds A X) X" by (meson B2 IsUpset_def upper_bounds_lem1)
  with B3 show ?thesis by auto
qed

lemma upper_bounds_lem6:"\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> x \<in> UpperBounds A X"  by (simp add: IsUpperBound_def upper_bounds_lem2)


lemma lower_bounds_lem0:"LowerBounds A X \<subseteq> X" by (simp add: LowerBounds_def)
lemma lower_bounds_lem1:"LowerBounds A X \<in> Pow X" by (simp add: LowerBounds_def)
lemma lower_bounds_lem2:"\<forall>x \<in>X. (x \<in> LowerBounds A X \<longleftrightarrow> IsLowerBound x A X)"  by (simp add: LowerBounds_def)
lemma lower_bounds_lem3:"\<forall>x \<in>LowerBounds A X. \<forall>a \<in>A. x\<le>a" by (meson IsLowerBound_def lower_bounds_lem0 lower_bounds_lem2 subsetD)
lemma lower_bounds_lem4:"x \<in>LowerBounds A X \<longrightarrow> ( \<forall>a \<in>A. x\<le>a)"by (simp add: lower_bounds_lem3)
lemma lower_bounds_lem5:"IsDownset (LowerBounds A X) X"
proof-
  have B0:"\<forall>l \<in> LowerBounds A X. \<forall>a \<in> A. l \<le> a" by (simp add: lower_bounds_lem3)
  have B1:"\<forall>x \<in> X. ((\<exists>l \<in> LowerBounds A X. x \<le> l) \<longrightarrow> (\<forall>a \<in> A. x \<le> a))" by (meson B0 order_trans)
  have B2:"\<forall>x \<in> X. ((\<exists>l \<in> LowerBounds A X. x \<le> l) \<longrightarrow> (x \<in> LowerBounds A X))" by (meson B1 IsLowerBound_def lower_bounds_lem2)
  have B3:"IsDownset (LowerBounds A X) X" by (meson B2 IsDownset_def lower_bounds_lem1)
  with B3 show ?thesis by auto
qed

lemma lower_bounds_lem6:"\<forall>x \<in> X. (\<forall>a \<in>A. x \<le> a) \<longrightarrow> x \<in> LowerBounds  A X"  by (simp add: IsLowerBound_def lower_bounds_lem2)


lemma lem0:"IsMaximum X (Pow X)"  by (metis IsMaximum_def IsUpperBound_def Pow_iff Pow_top)

lemma lem01:"IsDownset D X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in>D. x\<le> d\<longrightarrow> x \<in> D)" by (simp add: IsDownset_def)

lemma lem01_dual: "IsUpset U X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in> U. d \<le> x\<longrightarrow> x \<in>U)" by (simp add: IsUpset_def)

lemma lem02:"(DownClosure A X) \<subseteq> X"
proof-
  have B0:"DownClosure A X = {x \<in> X. \<exists>a \<in> A. x \<le> a}" using DownClosure_def by auto
  have B1:"\<forall>x \<in> DownClosure A X.  x \<in> X" by (simp add: B0)
  have B2:"(DownClosure A X) \<subseteq> X" by (simp add: B1 subsetI)
  with B2 show ?thesis by simp
qed

lemma lem02_dual:"(UpClosure A X) \<subseteq> X"
proof-
  have B0:"UpClosure A X = {x \<in> X. \<exists>a \<in> A. x \<ge>  a}" using UpClosure_def  by auto
  have B1:"\<forall>x \<in> UpClosure A X.  x \<in> X" by (simp add: B0)
  have B2:"(UpClosure A X) \<subseteq> X" by (simp add: B1 subsetI)
  with B2 show ?thesis by simp
qed

lemma lem1:
  assumes A0: "X \<noteq> {}" and
          A1: "E \<in> DownSets X" and
          A2: "D \<in> DownSets E" 
        shows "D \<in> DownSets X"
proof-
  have B0:"IsDownset D E" using A2 DownSets_def by auto
  have B1:"IsDownset E X" using A1 DownSets_def by auto
  have B21: "(D \<in> Pow E)" using B0 IsDownset_def by auto 
  have B22:"(\<forall>y \<in> E. \<forall>d \<in> D. y\<le>d \<longrightarrow> y \<in> D)" by (meson B0 IsDownset_def)
  have B31:"(E \<in> Pow X)" using B1 IsDownset_def by auto 
  have B32:"(\<forall>x \<in> X. \<forall>y \<in> E. x\<le>y \<longrightarrow> x \<in> E)" by (meson B1 IsDownset_def)
  have B4:"D \<in> Pow X" using B21 B31 by blast
  have B5:"\<forall>x \<in> X. \<forall>d \<in> D. x \<le>d \<longrightarrow> x \<in> D" using B21 B22 B32 by blast
  have B6:"IsDownset D X" by (meson B4 B5 IsDownset_def)
  from B4 B6 have B7:"D \<in> DownSets X" by (simp add: DownSets_def)
  with B7 show ?thesis by simp
qed


lemma lem1_dual:
  assumes A0: "X \<noteq> {}" and
          A1: "E \<in> UpSets X" and
          A2: "U \<in> UpSets E" 
        shows "U \<in> UpSets X"
proof-
  have B0:"IsUpset U E" using A2 UpSets_def by auto
  have B1:"IsUpset E X" using A1 UpSets_def by auto
  have B21: "(U \<in> Pow E)" using B0 IsUpset_def by auto 
  have B22:"(\<forall>y \<in> E. \<forall>u \<in> U. y \<ge> u \<longrightarrow> y \<in> U)" by (meson B0 IsUpset_def)
  have B31:"(E \<in> Pow X)" using B1 IsUpset_def by auto 
  have B32:"(\<forall>x \<in> X. \<forall>y \<in> E. x \<ge> y \<longrightarrow> x \<in> E)" by (meson B1 IsUpset_def)
  have B4:"U \<in> Pow X" using B21 B31 by blast
  have B5:"\<forall>x \<in> X. \<forall>u \<in> U. x \<ge> u \<longrightarrow> x \<in> U" using B21 B22 B32 by blast
  have B6:"IsUpset U X" by (meson B4 B5 IsUpset_def)
  from B4 B6 have B7:"U \<in> UpSets X" by (simp add: UpSets_def)
  with B7 show ?thesis by simp
qed


lemma lem2:
  assumes A0: "X \<noteq> {}" and
          A1: "D \<in> Pow X"
  shows "IsDownset D X \<longleftrightarrow> IsUpset (X-D) X"
proof-
  have B0:"IsDownset D X \<longrightarrow> IsUpset (X-D) X"
  proof-
    have C0: "IsDownset D X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in>D. x\<le> d\<longrightarrow> x \<in> D)" by (simp add: IsDownset_def) 
    have C1: " (\<forall>x \<in> X. \<forall>d \<in>D. x\<le> d\<longrightarrow> x \<in> D) \<longrightarrow>  (\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<notin> D)" by auto
    have C2: "(\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<notin> D) \<longrightarrow>  (\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<in>(X-D))" by blast
    have C3:" (\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<in>(X-D)) \<longrightarrow> IsUpset (X-D) X" by (simp add: IsUpset_def)
    have C4:"IsDownset D X \<longrightarrow> IsUpset (X-D) X" using C0 C3 by blast
    with C4 show ?thesis by simp
  qed
  have B1:"IsUpset (X-D) X \<longrightarrow> IsDownset D X"
  proof-
    have D0: "IsUpset (X-D) X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in> (X-D). d \<le> x\<longrightarrow> x \<in>(X-D))" by (simp add: IsUpset_def) 
    have D1: "(\<forall>x \<in> X. \<forall>d \<in> (X-D). d \<le> x\<longrightarrow> x \<in>(X-D)) \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in> D. x \<le> d \<longrightarrow> x \<in> D) "  using A1 by blast
    have D2: " (\<forall>x \<in> X. \<forall>d \<in> D. x \<le> d \<longrightarrow> x \<in> D)  \<longrightarrow> IsDownset D X" using A1 IsDownset_def by auto
    have D3:"IsUpset (X-D) X \<longrightarrow> IsDownset D X" using D0 D1 D2 by blast
    with D3 show ?thesis by simp
  qed
  from B0 B1 have B2:"IsDownset D X \<longleftrightarrow> IsUpset (X-D) X" by blast
  with B2 show ?thesis by simp
qed



lemma lem3:
  "PrincipalDownClosure a X = {x \<in> X. x\<le> a }"
proof-
  have B0:"PrincipalDownClosure a X = {x \<in> X. \<exists>b \<in> {a}. x \<le> b }"
    by (simp add: DownClosure_def PrincipalDownClosure_def)
  have B1:"PrincipalDownClosure a X = {x \<in> X.  x \<le> a }" using B0 by auto
  with B1 show ?thesis by simp
qed

lemma lem3_dual:
  "PrincipalUpClosure a X = {x \<in> X. x\<ge> a }"
proof-
  have B0:"PrincipalUpClosure a X = {x \<in> X. \<exists>b \<in> {a}. x \<ge> b }"
    by (simp add: UpClosure_def PrincipalUpClosure_def)
  have B1:"PrincipalUpClosure a X = {x \<in> X. x \<ge> a }" using B0 by auto
  with B1 show ?thesis by simp
qed

lemma lem4:
  "PrincipalUpClosure a X \<subseteq> X"
proof-
  let ?U="PrincipalUpClosure a X"
  have B0:"?U = {x \<in> X. \<exists>b \<in> {a}. x \<ge> b }"
    by (simp add: UpClosure_def PrincipalUpClosure_def)
  have B1:"\<forall>x \<in>?U. x \<in> X"  by (simp add: B0)
  with B1 show ?thesis by auto
qed

lemma lem4_dual:"PrincipalDownClosure a X \<subseteq> X"
proof-
  let ?D="PrincipalDownClosure a X"
  have B0:"?D = {x \<in> X. \<exists>b \<in> {a}. x \<le>  b }"
    by (simp add: DownClosure_def PrincipalDownClosure_def)
  have B1:"\<forall>x \<in>?D. x \<in> X"  by (simp add: B0)
  with B1 show ?thesis by auto
qed

lemma lem5:
  assumes A0:"X \<noteq> {}" and A1: "x1 \<in> X" and A2:"x2 \<in> X"
  shows "PrincipalDownClosure x1 X \<subseteq> PrincipalDownClosure x2 X \<longleftrightarrow> x1 \<le> x2"
proof-
  let ?D1="PrincipalDownClosure x1 X"
  let ?D2="PrincipalDownClosure x2 X"
  have B01:"\<forall>x \<in> X. (x \<in> ?D1  \<longleftrightarrow> x \<le> x1)" using lem3 A0 A1 by auto
  have B02:"\<forall>x \<in> X. (x \<in> ?D2  \<longleftrightarrow> x \<le> x2)" using lem3 A0 A2 by auto
  have B03:"?D1 \<in> Pow X" by (simp add: lem4_dual)
  have B04:"?D2 \<in> Pow X" by (simp add: lem4_dual)
  have B1: "?D1 \<subseteq> ?D2  \<longrightarrow>  x1 \<le> x2"
  proof-
    have B11:"?D1 \<subseteq> ?D2 \<longrightarrow> (\<forall>x \<in> ?D1. x \<in> ?D2) " by (simp add: in_mono)
    have B12:"x1 \<in> ?D1"  by (simp add: A1 B01)
    have B13:"?D1 \<subseteq> ?D2 \<longrightarrow> x1 \<in> ?D2" by (simp add: B11 B12)
    have B14:"?D1 \<subseteq> ?D2 \<longrightarrow> x1 \<le> x2" using A1 B02 B13 by auto
    with B14 show ?thesis by simp
  qed
  have B2: "x1 \<le> x2  \<longrightarrow> ?D1 \<subseteq> ?D2 "
  proof-
    have B21:"x1\<le>x2 \<longrightarrow> (\<forall>x \<in> X. x\<le>x1 \<longrightarrow> x \<le> x2)"
      by auto
    have B22:"(\<forall>x \<in> X. x\<le>x1 \<longrightarrow> x \<le> x2) \<longrightarrow>(\<forall>x \<in> X. (x \<in> ?D1  \<longrightarrow>  x \<in> ?D2)) "
      by (simp add: B01 B02)
    have B23:"x1\<le>x2 \<longrightarrow>  ?D1 \<subseteq> ?D2" using B03 B21 B22 by blast 
    with B23 show ?thesis by simp
  qed
  have B3: "?D1 \<subseteq> ?D2 \<longleftrightarrow> x1 \<le> x2" using B1 B2 by blast
  with B3 show ?thesis by auto
qed





lemma lem6:
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

lemma lem6_dual:
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


lemma lem_lub1:
  assumes A0:"HasSup A X" and
          A1: "A \<noteq> {}" and
          A2: "A \<in> Pow X" and
          A3: "s \<in> X"
  shows "(IsSup s A X) \<longleftrightarrow> (\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longleftrightarrow> (s \<le> x))"
proof-
  let ?U="UpperBounds A X"
  let ?R="\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longleftrightarrow> (s \<le> x)"
  let ?RL="\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> (s \<le> x)"
  let ?RR="\<forall>x \<in> X. (s \<le> x) \<longrightarrow> (\<forall>a \<in>A. a \<le> x)"
  have B00:"IsSup s A X \<longrightarrow> (s \<in> ?U)" by (simp add: IsSup_def)
  have B01:"IsSup s A X \<longrightarrow> (IsMinimum s ?U)" by (simp add: IsSup_def)
  have B02:"?R \<longleftrightarrow> (?RL \<and> ?RR)" by auto
  have LtR:"IsSup s A X \<longrightarrow> ?R"
  proof-
    have B0:"IsSup s A X \<longrightarrow> (\<forall>u \<in> ?U. s \<le> u)" by (meson B01 IsLowerBound_def IsMinimum_def)
    have B1:"IsSup s A X \<longrightarrow> (\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> x \<in> ?U)" by (simp add: IsUpperBound_def upper_bounds_lem2)
    have B2:"IsSup s A X \<longrightarrow> ?RL"  by (simp add: B0 B1) 
    have B3:"IsSup s A X \<longrightarrow> (\<forall>x \<in> X. (s \<le> x) \<longrightarrow> x \<in> ?U)" using B00 lem01_dual upper_bounds_lem5 by auto
    have B4:"IsSup s A X \<longrightarrow> ?RR" using B3 upper_bounds_lem4 by blast
    have B5:"IsSup s A X \<longrightarrow> ?R" using B2 B4 by blast
    with B5 show ?thesis by simp
  qed
  have RtL:"?R \<longrightarrow> IsSup s A X"
  proof-
    have C0:"\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> x \<in> ?U" by (simp add: upper_bounds_lem6)
    have C1:"?RL \<longrightarrow> (\<forall>x \<in>X. x \<in> ?U \<longrightarrow> s\<le> x)" by (simp add: upper_bounds_lem3)
    have C2:"s \<le> s" by simp
    have C3:"?RR \<longrightarrow> s \<in> ?U" by (simp add: A3 C0)
    have C4:"?R\<longrightarrow> (?RL \<and> ?RR) \<longrightarrow> ((\<forall>x \<in>X. x \<in> ?U \<longrightarrow> s\<le> x) \<and> ( s \<in> ?U))" using C1 C3 by blast
    have C5:"?R \<longrightarrow> IsLowerBound s ?U ?U" by (smt (verit) C1 C3 IsLowerBound_def subset_eq upper_bounds_lem0)
    have C6:"?R \<longrightarrow> IsMinimum s ?U" by (simp add: C5 IsMinimum_def)
    have C7:"?R \<longrightarrow> IsSup s A X" by (simp add: C3 C6 IsSup_def)
    with C7 show ?thesis by simp
  qed
  from RtL LtR have RtLtR:"IsSup s A X \<longleftrightarrow> ?R" by auto
  with RtLtR show ?thesis by simp
qed

(*"IsSup s A X \<equiv> (s \<in> UpperBounds A X) \<and> (IsMinimum s ( UpperBounds A X))"*)
(*definition IsLowerBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" 
  where "IsLowerBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  m\<le>a)"

definition IsMaximum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsMaximum m X \<equiv> IsUpperBound m X X"

definition IsMinimum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsMinimum m X \<equiv> IsLowerBound m X X"
*)
end