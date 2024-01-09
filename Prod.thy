theory Prod
  imports Main
begin

declare [[show_types]]

definition CartesianProduct::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "CartesianProduct I X = {f::('I \<Rightarrow> 'X). \<forall>i \<in> I. (f i) \<in> (X i)}"

abbreviation Prod::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "Prod I X \<equiv> CartesianProduct I X"

lemma prod_mem:
  "f \<in> Prod I X \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (X i))"
  by (simp add: CartesianProduct_def)


lemma axiom_of_choice_lol:
  fixes I::"'I set"
  fixes X::"'I \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. X i \<noteq> {}"
  shows "Prod I X \<noteq> {}"
proof-
  define f where "f=(\<lambda>i. SOME x. (x \<in> (X i)))"
  have "f \<in> Prod I X"
    by (metis A1 equals0I f_def prod_mem verit_sko_ex')
  show ?thesis
    using \<open>(f::'I \<Rightarrow> 'X) \<in> Prod.Prod (I::'I set) (X::'I \<Rightarrow> 'X set)\<close> by auto
qed

lemma projection_is_surjective:
  fixes I::"'I set"
  fixes X::"'I \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. X i \<noteq> {}" 
  shows "\<forall>i \<in> I. \<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
proof-
  have B0:"Prod I X \<noteq> {}"
    by (simp add: A0 A1 axiom_of_choice_lol)
  have "\<forall>i \<in> I. \<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
  proof
    fix i assume "i \<in> I"
    show "\<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
    proof
      fix x assume "x \<in> (X i)"
      obtain f0 where "f0 \<in> Prod I X"
        using B0 by blast
      define f where "f=(\<lambda>j. if j=i then x else (f0 j))"
      have "f \<in> Prod I X"
        by (metis \<open>(f0::'I \<Rightarrow> 'X) \<in> Prod.Prod (I::'I set) (X::'I \<Rightarrow> 'X set)\<close> \<open>(x::'X) \<in> (X::'I \<Rightarrow> 'X set) (i::'I)\<close> f_def prod_mem)
      have "f i = x"
        by (simp add: f_def)
      show "\<exists>f \<in> (Prod I X). (f i) = x"
        using \<open>(f::'I \<Rightarrow> 'X) (i::'I) = (x::'X)\<close> \<open>(f::'I \<Rightarrow> 'X) \<in> Prod.Prod (I::'I set) (X::'I \<Rightarrow> 'X set)\<close> by auto
      qed
    qed
  show ?thesis
    by (simp add: \<open>\<forall>i::'I\<in>I::'I set. \<forall>x::'X\<in>(X::'I \<Rightarrow> 'X set) i. \<exists>f::'I \<Rightarrow> 'X\<in>Prod.Prod I X. f i = x\<close>)
qed

lemma comp_inverse:
  "UNIV-(UNIV-X) = X"
  by (simp add: Diff_Diff_Int)

lemma union_of_intersections:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" 
  shows "(\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) = (\<Inter>f\<in>(Prod I J). (\<Union>i \<in> I. (X i (f i))))"
proof-
  let ?S="\<Union>i \<in> I. J i"
  let ?P="Prod I J"
  have B0:"\<forall>f. f \<in> ?P \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (J i))"
    by (simp add: prod_mem)
  have B1:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longleftrightarrow> (\<exists>i \<in>I. x \<in>  (\<Inter>j\<in>(J i). (X i j)))"
    by blast
  have B2:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longleftrightarrow> (\<exists>i \<in> I. \<forall>j \<in> (J i). x \<in> (X i j))"
    by simp
  have B3:"\<forall>x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))). (\<exists>i \<in> I. \<forall>f \<in> ?P. x \<in> (X i (f i)))"
  proof
    fix x assume B3A0:"x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    obtain i where "i \<in>I \<and>  x \<in>  (\<Inter>j\<in>(J i). (X i j))"
      using B3A0 by blast
    have B30:"\<forall>f \<in> ?P. \<forall>i \<in> I. ((f i) \<in> (J i))"
      by (simp add: prod_mem)  
    show "(\<exists>i \<in> I. \<forall>f \<in> ?P. x \<in> (X i (f i) ))"
      using B30 B3A0 by auto
  qed
  have B4:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow>  ( \<forall>f \<in> ?P. \<exists>i \<in> I.  x \<in> (X i (f i)))"
    using B0 by blast
  have B5:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> (\<forall>f \<in> ?P. x \<in> (\<Union>i \<in> I. (X i (f i))))"
    by (simp add: B4)
  have B6:" (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<subseteq> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
    using B5 by blast
  have B7:"\<And>x. x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
  proof
    fix x assume B7A0:"x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    have B70:"\<forall>i \<in> I. x \<notin>(\<Inter>j\<in>(J i). (X i j))"
      using B7A0 by blast
    have B71:"\<forall>i \<in> I. {j. j\<in> (J i) \<and> (x \<notin> (X i j))} \<noteq> {}"
      using B70 by fastforce
    define K where "K=(\<lambda>(i::('I)).  {j. j\<in> (J i) \<and> (x \<notin> (X i j))})"
    define f where "f=( \<lambda>(i::('I)). SOME j. j \<in> (K i))"
    have B72:"f \<in> ?P"
      by (metis (mono_tags, lifting) B0 B71 Collect_empty_eq K_def f_def mem_Collect_eq verit_sko_ex')
    have B73:"\<forall>i \<in> I. x \<notin> (X i (f i))"
      by (metis (mono_tags, lifting) B71 Collect_empty_eq K_def f_def mem_Collect_eq someI_ex)
    have B74:"x \<notin>  (\<Union>i \<in> I. (X i (f i)))"
      using B73 by blast
    show "x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
      using B72 B74 by blast
  qed
  have B8:"\<forall>x. x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
    using B7 by blast
  have B9:"(\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i)))) \<subseteq>  (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    using B8 by blast
  with B6 B9 show ?thesis
    by blast
qed
   


lemma intersection_of_unions:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" 
  shows "(\<Inter>i \<in> I. (\<Union>j \<in> (J i). (X i j))) = (\<Union>f\<in>(Prod I J). (\<Inter>i\<in> I. (X i (f i))))"
proof-
  define Z where "Z= (\<lambda>(i::('I)) (j::('J)). (UNIV-(X i j)))"
  have B0:"(\<Union>i \<in> I. (\<Inter>j \<in> (J i). (Z i j))) = (\<Inter>f \<in> (Prod I J). (\<Union>i \<in> I. (Z i (f i))))"
    by (simp add: assms union_of_intersections)
  have B1:"UNIV-(\<Union>i \<in> I. (\<Inter>j \<in> (J i). (Z i j))) = UNIV-(\<Inter>f \<in> (Prod I J). (\<Union>i \<in> I. (Z i (f i))))"
    using B0 by presburger
  have B2:"(\<Inter>i \<in> I. (UNIV -  (\<Inter>j \<in> (J i). (Z i j)))) = (\<Union>f \<in> (Prod I J). UNIV-(\<Union>i \<in> I. (Z i (f i))))"
    using B1 by force
  have B3:"(\<Inter>i \<in> I. (\<Union>j \<in> (J i). (UNIV-(Z i j)))) =  (\<Union>f \<in> (Prod I J). (\<Inter>i \<in> I. UNIV-(Z i (f i))))"
    using B1 by auto
  have B4:"(\<Inter>i \<in> I. (\<Union>j \<in> (J i). UNIV-(UNIV-(X i j)))) = (\<Union>f\<in>(Prod I J). (\<Inter>i\<in> I. UNIV-(UNIV-(X i (f i)))))"
    using B3 Z_def by blast
  have B5:"(\<Inter>i \<in> I. (\<Union>j \<in> (J i). (X i j))) = (\<Union>f\<in>(Prod I J). (\<Inter>i\<in> I. (X i (f i))))"
    proof -
      have "\<forall>X. (UNIV::'X set) - (UNIV - X) = X"
        by (simp add: comp_inverse)
      then show ?thesis
        using B4 by presburger
    qed
   with B5 show ?thesis
     by simp
qed

lemma cartesian_product_union_intersection:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. J i \<noteq> {}"
  shows "Prod I (\<lambda>i. (\<Union>j \<in> (J i). (X i j))) = (\<Union>f \<in> (Prod I J). (Prod I (\<lambda>i. (X i (f i)))))"
proof-
  define G where A2:"G=(\<lambda>i. (\<Union>j \<in> (J i). (X i j)))"
  define F where A3:"F=(\<lambda>f i. (X i (f i)))"
  let ?PIJ="Prod I J"
  let ?L="Prod I G"
  let ?R="(\<Union>f \<in>?PIJ. (Prod I (F f)))"
  have LR:"?L \<subseteq> ?R"
    proof-
      have LR0:"\<And>g. g \<in> ?L \<longrightarrow> g \<in> ?R"
        proof
          fix g assume LR0A0:"g \<in> ?L"
          have B0:"\<forall>i \<in> I. \<exists>j \<in> (J i). (g i) \<in> (X i j)"
            by (metis A2 LR0A0 UN_iff prod_mem)
          define H where A3:"H=(\<lambda>i. {j \<in> (J i). (g i) \<in> (X i j)})"
          have B1:"\<forall>i \<in> I. (H i) \<noteq> {}"
            using A3 B0 by auto
          define f where A4:"f=(\<lambda>i. SOME j. j \<in> (H i))"
          have B2:"\<forall>i \<in> I. (f i) \<in> (H i)"
            using A4 B1 some_in_eq by blast
          have B3:"f \<in> ?PIJ"
            using A3 B2 prod_mem by fastforce
          have B4:"g \<in> (Prod I (F f))"
            using A3 B2 \<open>F::('I \<Rightarrow> 'J) \<Rightarrow> 'I \<Rightarrow> 'X set \<equiv> \<lambda>(f::'I \<Rightarrow> 'J) i::'I. (X::'I \<Rightarrow> 'J \<Rightarrow> 'X set) i (f i)\<close> prod_mem by fastforce
          show "g \<in> ?R"
            using B3 B4 by blast
          qed
       show ?thesis
         using LR0 by blast
      qed
  have RL:"?R \<subseteq> ?L"
   proof-
      have RL0:"\<And>g. g \<in> ?R \<longrightarrow> g \<in> ?L"
        proof
          fix g assume A5:"g \<in> ?R"
          obtain f where A6:"f \<in> ?PIJ \<and> (\<forall>i \<in> I. (g i) \<in> (X i ((f i))))"
            using A3 A5 prod_mem by force
          have B5:"\<forall>i \<in> I. (\<exists>j \<in> (J i). (f i) = j)"
            by (meson A6 prod_mem)
          have B6:"\<forall>i \<in> I. (\<exists>j \<in> (J i). (g i) \<in> (X i j))"
            using A6 B5 by blast
          show "g \<in> ?L"
            by (simp add: A2 B6 prod_mem)
          qed
      show ?thesis
        using RL0 by blast
    qed
  show ?thesis
    using A2 A3 LR RL by fastforce
qed      
  

lemma cartesian_product_intersection_union:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. J i \<noteq> {}"
  shows "Prod I (\<lambda>i. (\<Inter>j \<in> (J i). (X i j))) = (\<Inter>f \<in> (Prod I J). (Prod I (\<lambda>i. (X i (f i)))))"
proof-
  define G where A2:"G=(\<lambda>i. (\<Inter>j \<in> (J i). (X i j)))"
  define F where A3:"F=(\<lambda>f i. (X i (f i)))"
  let ?PIJ="Prod I J"
  let ?L="Prod I G"
  let ?R="(\<Inter>f \<in>?PIJ. (Prod I (F f)))"
  have B0:"\<forall>g. g \<in> ?L \<longleftrightarrow> (\<forall>i \<in> I. \<forall>j \<in> (J i). (g i) \<in> (X i j))"
    by (simp add: \<open>G::'I \<Rightarrow> 'X set \<equiv> \<lambda>i::'I. \<Inter> ((X::'I \<Rightarrow> 'J \<Rightarrow> 'X set) i ` (J::'I \<Rightarrow> 'J set) i)\<close> prod_mem)
  have B1:"\<forall>g. g \<in> ?R \<longleftrightarrow> (\<forall>f \<in> ?PIJ. \<forall>i \<in> I. (g i) \<in> (X i (f i)))"
    by (simp add: A3 prod_mem)
  have B2:"\<forall>f. f \<in> ?PIJ \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (J i))"
    by (simp add: prod_mem)
  have LR:"?L \<subseteq> ?R"
    proof-
      have LR0:"\<And>g. g \<in> ?L \<longrightarrow> g \<in> ?R"
        proof
          fix g assume LR0A0:"g \<in> ?L"
          show "g \<in> ?R"
            by (metis B0 B1 LR0A0 prod_mem)
        qed
      show ?thesis
        using LR0 by blast
   qed
  have RL:"?R \<subseteq> ?L"
   proof-
      have RL0:"\<And>g. g \<in> ?R \<longrightarrow> g \<in> ?L"
        proof
          fix g assume A5:"g \<in> ?R"
          have RL0B0:"\<forall>f. f \<in> ?PIJ \<longrightarrow> (\<forall>i\<in>I. (g i) \<in> (X i (f i)))"
            by (meson A5 B1)
          have RL0B1:"\<forall>f \<in> ?PIJ. (\<forall>i \<in> I. (f i) \<in> (J i))"
            using B2 by fastforce
          have RL0B2:"(\<forall>i \<in> I. \<forall>j \<in> (J i). (g i) \<in> (X i j))"
          proof
            fix k assume "k \<in> I"
            show "\<forall>h \<in> (J k). (g k) \<in> (X k h)"
            proof
              fix h assume "h \<in> (J k)"
              show "(g k) \<in> (X k h)"
                by (metis A0 A1 RL0B0 \<open>(h::'J) \<in> (J::'I \<Rightarrow> 'J set) (k::'I)\<close> \<open>(k::'I) \<in> (I::'I set)\<close> projection_is_surjective)
            qed
          qed
          show "g \<in> ?L"
            using B0 RL0B2 by blast
      qed
      show ?thesis
        using RL0 by blast
  qed
  show ?thesis
    using A2 A3 LR RL by blast
qed

definition is_countable :: "'a set \<Rightarrow> bool" where
  "is_countable I \<equiv> (\<exists>f::'a \<Rightarrow> nat. inj_on f I)"


end
