theory Posets17
  imports Main
begin

section Settings
hide_const top bot
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev
declare [[show_consts,show_sorts,show_types, show_results]]


section Misc

lemma image_p: 
  "(\<And>a. a \<in> A \<Longrightarrow> P (f a)) \<Longrightarrow> (\<forall>y \<in> f ` A.  P(y))"  
  by blast

lemma un_to_ind_un: 
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Union>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Union>i \<in> I. f i))" 
   by simp

lemma int_to_ind_int:
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Inter>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Inter>i \<in> I. f i))" 
  by simp

definition Pow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Pow_ne X = Pow X - {{}}"

definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Fpow_ne X = Fpow X - {{}}"

lemma pow_ne_iff1:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<in> Pow X \<and> A \<noteq> {}" by (simp add: Pow_ne_def)

lemma pow_ne_iff2:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<subseteq> X \<and> A \<noteq> {}" 
  by (simp add: Pow_ne_def)

lemma pow_neI: "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<in> Pow_ne X" by(simp add:Pow_ne_def)

lemma pow_neD1: "A \<in> Pow_ne X \<Longrightarrow> A \<subseteq> X " by(simp add:Pow_ne_def)

lemma pow_neD2: " A \<in> Pow_ne X \<Longrightarrow> A \<noteq> {} " by(simp add:Pow_ne_def)

lemma pow_ne_iso0: "A \<in> Pow_ne X \<Longrightarrow> B \<in> Pow_ne A \<Longrightarrow> B \<subseteq> X"   by (drule pow_neD1)+ simp

lemma pow_ne_iso1:"A \<in> Pow_ne X \<Longrightarrow> B \<in> Pow_ne A \<Longrightarrow> B \<in> Pow_ne X"by(rule pow_neI,erule pow_ne_iso0,simp,erule pow_neD2)

lemma pow_ne_bot:"{} \<notin> Pow_ne X"by(simp add:Pow_ne_def)
               
lemma pow_ne_top: "X \<noteq> {} \<Longrightarrow> X \<in> Pow_ne X" by(simp add:Pow_ne_def)

lemma fpow_ne_iff1:"A \<in> Fpow_ne X \<longleftrightarrow> A \<in> Fpow X \<and> A \<noteq> {}"by (simp add: Fpow_ne_def)

lemma fpow_ne_iff2:"A \<in> Fpow_ne X \<longleftrightarrow> A \<subseteq> X \<and> finite A \<and> A \<noteq> {}" by (simp add: Fpow_Pow_finite fpow_ne_iff1)


lemma fpow_neI: "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<in> Fpow_ne X" by (simp add: Fpow_def fpow_ne_iff1)

lemma fpow_neD0:"A \<in> Fpow_ne X \<Longrightarrow> A \<in> Pow X " by (simp add: fpow_ne_iff2)

lemma fpow_neD0b:"A \<in> Fpow_ne X \<Longrightarrow> A \<in> Pow_ne X" by (simp add: fpow_ne_iff2 pow_ne_iff1)

lemma fpow_neD1: "A \<in> Fpow_ne X \<Longrightarrow> A \<subseteq> X " by (simp add: fpow_ne_iff2)

lemma fpow_neD2:"A \<in> Fpow_ne X \<Longrightarrow> A \<noteq> {} " by (simp add: fpow_ne_iff2)

lemma fpow_neD3:"A \<in> Fpow_ne X \<Longrightarrow> finite A "by (simp add: fpow_ne_iff2)

lemma fpow_ne_iso0:"A \<in> Fpow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<subseteq> X" by (drule fpow_neD1)+ simp

lemma fpow_ne_iso1:"A \<in> Fpow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<in> Fpow_ne X"by(rule fpow_neI,erule fpow_ne_iso0,simp,erule fpow_neD2, erule fpow_neD3)

lemma fpow_ne_iso2: "A \<in> Pow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<in> Fpow_ne X"by (metis dual_order.trans fpow_ne_iff2 pow_ne_iff2)

lemma fpow_ne_bot:"{} \<notin> Fpow_ne X"by (simp add: fpow_ne_iff1)

lemma ne_subset_ne:"A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}"by blast

definition CartesianProduct::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where "CartesianProduct I X = {f::('I \<Rightarrow> 'X). \<forall>i \<in> I. (f i) \<in> (X i)}"

abbreviation Prod::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where "Prod I X \<equiv> CartesianProduct I X"

lemma prod_mem: "f \<in> Prod I X \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (X i))"by (simp add: CartesianProduct_def)

lemma prod_memI:"(\<And>i. i \<in> I \<Longrightarrow> (f i) \<in> (X i)) \<Longrightarrow> f \<in> Prod I X" by(simp add:CartesianProduct_def)

lemma prod_memD:"f \<in> Prod I X \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i ) \<in> (X i))"by(simp add:CartesianProduct_def)

lemma prod_memE:"f \<in> Prod I X \<Longrightarrow> i \<in> I\<Longrightarrow> (f i ) \<in> (X i)" by(simp add:CartesianProduct_def)

definition choice::"'I set \<Rightarrow>('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X)" where"choice I X \<equiv> (\<lambda>i. SOME x. x \<in> X i)"

lemma choice_ne1:"\<lbrakk>I \<noteq> {}; (\<And>i. i \<in> I \<Longrightarrow> X i \<noteq> {})\<rbrakk> \<Longrightarrow> choice I X \<in> Prod I X"by (simp add: choice_def prod_memI some_in_eq)

lemma axiom_of_choice_lol: "\<lbrakk>I \<noteq> {}; (\<And>i. i \<in> I \<Longrightarrow> X i \<noteq> {})\<rbrakk> \<Longrightarrow> Prod I X \<noteq> {}" by (metis choice_ne1 empty_iff)

lemma axiom_of_choice_obtain:
  assumes A0:"I \<noteq> {}" "(\<And>i. i \<in> I \<Longrightarrow> X i \<noteq> {})"
  obtains f0 where "f0 \<in> Prod I X"
  by (meson assms choice_ne1)

lemma proj_surj1:
  assumes A0:"I \<noteq> {}" "(\<And>i. i \<in> I \<Longrightarrow> X i \<noteq> {})" and
          A1:"i \<in> I" "x \<in> X i"
  shows "(\<exists>f \<in> (Prod I X). (f i) = x)"
proof-
  obtain f0 where B3:"f0 \<in> Prod I X"
    by (meson assms axiom_of_choice_obtain)
  define f where "f=(\<lambda>j. if j=i then x else (f0 j))"
  have B4:"f \<in> Prod I X"
    by (metis B3 assms(4) f_def prod_mem)
  have B5:"f i = x"
    by (simp add: f_def)
  show "\<exists>f \<in> (Prod I X). (f i) = x"
    using B4 B5 by auto
qed


lemma projection_is_surjective:
  assumes A0:"I \<noteq> {}" and 
          A1:"\<forall>i \<in> I. X i \<noteq> {}" 
  shows "\<forall>i \<in> I. \<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
  by (simp add: A0 A1 proj_surj1)

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


lemma leq_iff_leq_eq:
  "\<lbrakk>a \<in> X; b \<in> X; antisym_on X R; (a, a) \<in> R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. (x, a) \<in> R \<longleftrightarrow> (x, b)\<in>R) \<Longrightarrow> a =b" 
  by (simp add: antisym_onD)

lemma geq_iff_geq_eq:
  "\<lbrakk>a \<in> X; b \<in> X; antisym_on X R;(a, a) \<in> R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. (a, x) \<in> R \<longleftrightarrow> (b, x) \<in> R) \<Longrightarrow> a =b" 
  by (simp add: antisym_onD)



section Definitions
subsection Bounds
definition ub::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"  where 
  "ub R A x \<equiv> (\<forall>a. a \<in> A \<longrightarrow> (a, x) \<in> R)"

abbreviation lb where
   "lb R A x \<equiv> ub (converse R) A x"

definition ubd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where  
  "ubd R X A \<equiv> {b \<in> X. ub R A b}"

abbreviation lbd where 
  "lbd R X A \<equiv> ubd (converse R) X A"

subsection ExtremeElements
definition is_greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
   "is_greatest R A m \<equiv> m \<in> ubd R A A"

abbreviation is_least::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
   "is_least R A m \<equiv> is_greatest (converse R) A m"

definition Greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "Greatest R A \<equiv> (THE m. is_greatest R A m)"

definition Least::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "Least R A \<equiv> (THE m. is_least R A m)"

definition is_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "is_sup R X A x \<equiv> (is_least R (ubd R X A) x)"

abbreviation is_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "is_inf R X A x \<equiv> is_sup (converse R) X A x"

definition Sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where  
  "Sup R X A \<equiv> (THE m. is_sup R X A m)"

abbreviation Inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where  
  "Inf R X A \<equiv> (THE m. is_sup (converse R) X A m)"

subsection Lattices
definition is_sup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_sup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup R X {a, b} x))"

definition is_fsup_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_fsup_closed R X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup R X {a1, a2} \<in> A)"

abbreviation is_inf_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_inf_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup (converse R) X {a, b} x))"

abbreviation is_finf_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_finf_closed R X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup (converse R) X {a1, a2} \<in> A)"

definition is_lattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_lattice R X \<equiv> ((X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf R X {a, b} x) \<and>  (\<exists>x. is_sup R X {a, b} x)))"

definition sup_distributive where
  "sup_distributive R X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X. x \<le> Sup R X {a, b} \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup R X {a1, b1}))"

definition inf_distributive where
  "inf_distributive R X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X.  Inf R X {a, b} \<le> x \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf R X {a1, b1}))"

definition distributive_lattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "distributive_lattice R X \<equiv> (is_lattice R X) \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<forall>z \<in> X. Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}})"

definition is_csup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_csup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup R X A x))"

definition is_csup_closed::"'a rel \<Rightarrow>'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_csup_closed R X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Sup R X E \<in> A)"

definition is_cinf_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_cinf_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf R X A x))"

definition is_cinf_closed::"'a rel \<Rightarrow>'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_cinf_closed R X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Inf R X E \<in> A)"

definition is_clattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_clattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>s. is_sup R X A s))"

definition subsemilattice_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subsemilattice_inf R X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf R X {a, b} i))"

definition subsemilattice_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subsemilattice_sup R X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup R X {a, b} i))"

definition sublattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "sublattice R X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>s \<in> A. is_sup R X {a, b} s) \<and> (\<exists>i \<in> A. is_inf R X {a, b} i))"


subsection SpecialSets
definition is_dir::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where 
  "is_dir X R \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X.  (a, c) \<in> R \<and>  (b, c) \<in> R))"

definition is_ord_cl::"'a set \<Rightarrow> 'a set\<Rightarrow> 'a rel \<Rightarrow> bool" where
   "is_ord_cl X A R \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and>  (a, b) \<in> R \<longrightarrow> b \<in> A )"

definition is_filter::"'a rel \<Rightarrow> 'a set\<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_filter R X F \<equiv> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (converse R)) \<and> is_ord_cl X F R"

abbreviation is_ideal ::"'a rel \<Rightarrow> 'a set\<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_ideal  R X I \<equiv> is_filter (converse R) X I"

definition is_pfilter::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_pfilter R X A \<equiv> (is_filter R X A) \<and> X \<noteq> A"

abbreviation is_pideal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_pideal R X A \<equiv> is_pfilter (converse R) X A"

definition filters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "filters_on R X \<equiv> {F. is_filter R X F}"

definition pfilters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "pfilters_on R X \<equiv> {F. is_pfilter R X F}"

definition filter_closure::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "filter_closure R X A \<equiv> if A={} then {Greatest R X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"

definition binary_filter_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow>'a set\<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "binary_filter_sup R X A B = {x \<in> X. \<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x) \<in> R}"

definition lorc::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where 
  "lorc R X a \<equiv> {y \<in> X. (a, y) \<in> R} "

abbreviation rolc where 
  "rolc R X a \<equiv> lorc (converse R) X a"

definition ord_cl_sets::"'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set set" where 
  "ord_cl_sets X R \<equiv> {A. A \<subseteq> X \<and> is_ord_cl X A R}"

definition up_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "up_cl R X A = {x \<in> X. \<exists>a \<in> A. (a, x) \<in> R}"

abbreviation dw_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "dw_cl R X A \<equiv> up_cl (converse R) X A"

subsection SpecialElements
definition is_compact::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "is_compact R X c \<equiv> c \<in> X \<and> (\<forall>A. A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R))"

definition compact_elements::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "compact_elements R X \<equiv> {c. is_compact R X c}"

definition compactly_generated::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "compactly_generated R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x))"

definition join_dense::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "join_dense R X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_sup R X Dx x)"

abbreviation meet_dense::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "meet_dense R X D \<equiv> join_dense (converse R) X D"

definition sup_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "sup_prime R X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup R X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

abbreviation inf_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "inf_prime R X A \<equiv> sup_prime (converse R) X A"

definition elem_sup_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "elem_sup_prime R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (x, Sup R X {a, b}) \<in> R \<longrightarrow> ((x,  a) \<in> R \<or> (x, b) \<in> R))"

abbreviation elem_inf_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "elem_inf_prime R X x \<equiv> elem_sup_prime (converse R) X x"

definition fin_sup_irr::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where  
  "fin_sup_irr R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Sup R X {a, b} \<longrightarrow> (x = a \<or> x = b))" 

abbreviation fin_inf_irr::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "fin_inf_irr R X x \<equiv> fin_sup_irr (converse R) X x"

definition meet_reducible::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "meet_reducible R X x \<equiv> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf R X A x)"

abbreviation meet_irr where 
  "meet_irr R X x \<equiv> \<not>(meet_reducible R X x)"

subsection Functions
definition isotone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
  "isotone Rx X Ry f \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1, x2) \<in> Rx \<longrightarrow> (f x1, f x2) \<in> Ry)"

abbreviation antitone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
   "antitone Rx X Ry f \<equiv> isotone Rx X (converse Ry) f"

definition extensive::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where 
  "extensive R X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, f x) \<in> R)"

definition idempotent::"'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where 
  "idempotent X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x)"

definition closure::" 'a rel \<Rightarrow> 'a set  \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow>  bool" where  
  "closure R X f \<equiv> extensive R X f \<and> idempotent X f \<and> isotone R X R f \<and> (f`X \<subseteq> X)"

definition closure_cond::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "closure_cond R X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<longrightarrow> x2 \<in> X \<longrightarrow> (x1, f x2) \<in> R \<longrightarrow> (f x1, f x2) \<in> R)"

definition closure_range::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "closure_range R X C\<equiv> C \<noteq> {} \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least R  (ubd R C {x}) c))"
  
abbreviation clr where 
  "clr R X C \<equiv> closure_range R X C"

definition extrema_dual::"('a \<Rightarrow> 'b) \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set  \<Rightarrow> bool" where
  "extrema_dual f Rx X Ry Y \<equiv>(\<forall>A. A \<subseteq> X \<longrightarrow> f (Sup Rx X A) = Inf Ry Y (f`A))"

definition dual_adj::"('a \<Rightarrow> 'b) \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a)" where
  "dual_adj f Rx X Ry Y \<equiv> (\<lambda>y. Sup Rx X {x \<in> X. (y,f x)\<in>Ry})"

definition rel_from_pair::"('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('b set \<Rightarrow> 'a set) \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
  "rel_from_pair f X g Y \<equiv> {(x, y). (x, y) \<in> (X \<times> Y) \<and> y \<in> f {x}}"

definition lgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a set \<Rightarrow> 'b set)" where
  "lgc_from_rel R X Y \<equiv> (\<lambda>A. {y. y \<in> Y \<and> (\<forall>x. x \<in> A \<longrightarrow> (x, y) \<in> R)})"

definition rgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b set \<Rightarrow> 'a set)" where
  "rgc_from_rel R X Y \<equiv> (\<lambda>B. {x. x \<in> X \<and> (\<forall>y. y \<in> B \<longrightarrow> (x, y) \<in> R)})"

definition galois_conn::"('a \<Rightarrow> 'b) \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> bool" where
  "galois_conn f Rx X g Ry Y \<equiv> (f`X \<subseteq> Y) \<and> (g`Y \<subseteq> X) \<and> (\<forall>x \<in> X. \<forall>y \<in> Y.  ((x,g y)\<in>Rx \<longleftrightarrow> (y,f x)\<in>Ry))"

abbreviation antisym where 
  "antisym R X \<equiv> antisym_on X R"

abbreviation trans where 
  "trans R X \<equiv> trans_on X R"

abbreviation ord where 
  "ord R X \<equiv> antisym_on X R \<and> trans_on X R"

definition refl::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "refl R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, x) \<in> R)"

definition diag::"'a set \<Rightarrow> 'a rel" where
  "diag X \<equiv> {(x, x). x \<in> X}"

definition ord_embedding::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> bool" where
  "ord_embedding Rx X Ry f \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<longrightarrow> ((x1,x2)\<in>Rx  \<longleftrightarrow> (f x1,f x2)\<in>Ry))"

definition ord_isomorphism::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> bool" where
  "ord_isomorphism Rx X Ry Y f \<equiv> ord_embedding Rx X Ry f \<and> f`X=Y"

section Bounds
subsection UpperBoundsPredicate

lemma diag_memI:
  "x \<in> X \<Longrightarrow> (x,x) \<in> diag X"
  by(simp add:diag_def)

lemma diag_memD:
  "(x,x)\<in>diag X \<Longrightarrow> x \<in> X"
  by(simp add:diag_def)

lemma diag_mem_iff:
  "(x,x)\<in>diag X \<longleftrightarrow> x \<in> X"
  by(simp add:diag_def)

lemma reflI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (x,x)\<in>R) \<Longrightarrow> refl R X" 
  by(simp add:refl_def)

lemma reflD1:
  "refl R X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (x,x)\<in>R)" 
  by(simp add:refl_def)

lemma reflE1:
  "refl R X \<Longrightarrow> ((\<And>x. x \<in> X \<Longrightarrow> (x,x)\<in>R) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  by(simp add:refl_def)

lemma ub_iff1:
  "ub R A x \<longleftrightarrow> (\<forall>a \<in> A. (a, x)\<in>R)" 
  by(auto simp add:ub_def)

lemma ubI:
  "(\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R) \<Longrightarrow> ub R A x" 
  by (simp add:ub_def)

lemma ubD:
  "\<lbrakk>ub R A x;  a \<in> A\<rbrakk>  \<Longrightarrow> (a, x) \<in> R " 
  by (simp add:ub_def)

lemma ubE:
  "ub R A x \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R)"
  by (simp add: ub_def)

lemma ubE2:
  "ub R A x \<Longrightarrow> ((\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (simp add: ub_def)

lemma ub_ant2:
  "\<lbrakk>A \<subseteq> B; ub R B x\<rbrakk> \<Longrightarrow> ub R A x"
   by (simp add:ub_def subsetD)

lemma ub_iso1:
  "\<lbrakk>x \<in> A; y \<in> A; trans_on A R; (x, y)\<in>R; ub R A x\<rbrakk> \<Longrightarrow> ub R A y" 
  by(intro ubI, rule_tac ?A="A" and ?r="R" and ?x="a" and ?y="x" and ?z="y" in trans_onD, simp+, erule ubE, simp+)

lemma ub_empty:
  "ub R {} x"
  by (simp add: ub_def)

lemma ub_singleton:
  "(x, x) \<in> R \<Longrightarrow> ub R {x} x"
  by (simp add: ub_def)

lemma ub_singletonI:
  "ub R {y} x \<Longrightarrow>(y, x) \<in> R"
  by (simp add: ubE)

lemma ub_singletonD:
  "(y, x) \<in> R \<Longrightarrow> ub R {y} x"
  by (simp add: ub_def)

lemma ub_singleton_simp:
  "ub R {y} x \<longleftrightarrow>(y, x) \<in> R"
  by (simp add: ub_def)

lemma ub_insert:
  "\<lbrakk>ub R F c; (x, c) \<in> R\<rbrakk> \<Longrightarrow> ub R (insert x F) c"
  by (simp add: ub_def)

lemma ub_binaryI:
  "(a, b) \<in> R \<Longrightarrow> (b, b) \<in> R \<Longrightarrow> ub R {a, b} b"
  by (simp add: ub_insert ub_singleton)

lemma ub_binaryD:
  "ub R {a, b} b \<Longrightarrow> (a, b) \<in> R"
  by (simp add: ubE)

lemma ub_binary_iff1:
  "(a, b) \<in> R \<and> (b, b) \<in> R \<longleftrightarrow> ub R {a, b} b"
  by (simp add: ub_iff1)

lemma ub_doubleE1:
  "ub R {a, b} c \<Longrightarrow> (a, c) \<in> R"
  by (simp add: ubE)

lemma ub_doubleE2:
  "ub R {a, b} c \<Longrightarrow> (b, c) \<in> R"
  by (simp add: ubE)

lemma ub_doubleI:
  "\<lbrakk>(a, c) \<in> R; (b, c) \<in> R\<rbrakk> \<Longrightarrow> ub R {a, b} c"
  by (simp add: ub_empty ub_insert)

lemma ub_double_iff1:
  "ub R {a, b} c \<longleftrightarrow>(a, c) \<in> R \<and> (b, c) \<in> R"
  by(auto, erule ub_doubleE1, erule ub_doubleE2, erule ub_doubleI, simp)

lemma ub_unionI:
  "\<lbrakk>ub R A x; ub R B x\<rbrakk> \<Longrightarrow> ub R (A \<union> B) x"
  by (simp add: ub_def)

lemma ub_unionD1:
  "ub R (A \<union> B) x \<Longrightarrow> ub R A x"
  by (simp add: ub_def)

lemma ub_unionD2:
  "ub R (A \<union> B) x \<Longrightarrow> ub R B x"
  by (simp add: ub_def)

lemma ub_unI:
  "(\<And>A. A \<in> S \<Longrightarrow> ub R A x) \<Longrightarrow> ub R (\<Union>S) x"
  by (simp add: ub_iff1)

lemma ub_unD:
  "ub R (\<Union>S) x \<Longrightarrow> A \<in> S \<Longrightarrow> ub R A x"
  using ub_ant2[of A "\<Union>S" R x] by blast

lemma ub_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> (f a, x) \<in> R) \<Longrightarrow> ub R (f`A) x"
  using image_p[of A "\<lambda>a. (a, x) \<in> R" f]
  by(simp add:ub_def image_p[of A "\<lambda>a. (a, x) \<in> R" f])
lemma fbdE1:"ub R (f`I) b \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i, b) \<in> R)" by(auto intro:ubE)


subsection UpperBoundsSet


lemma ubdI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> (a, b)\<in>R); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
   by(simp add: ubd_def ubI)

lemma ubdI2:
  "\<lbrakk>ub R A b; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  by (simp add: ubdI ub_def) 

lemma ubdD1:
  "\<lbrakk>b \<in> ubd R X A; x \<in> A\<rbrakk> \<Longrightarrow> (x, b)\<in>R"
  by (simp add: ubd_def ub_def)

lemma ubdD2:
  "b \<in> ubd R  X A \<Longrightarrow> b \<in> X"
  by (simp add: ubd_def)

lemma ubdD3:
  "b \<in> ubd R  X A \<Longrightarrow> ub R A b"
  by (simp add: ubd_def)

lemma ubd_D31:
  "b \<in> ubd R  X A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b)\<in>R)"
  by (simp add: ubdD1)

lemma ubd_mem_iff:
  "b \<in> ubd R  X A \<longleftrightarrow> (b \<in> X \<and> ub R A b)" 
   by(simp add: ubd_def)

lemma ubd_mem_iff2:
  "b \<in> ubd R  X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  (a, b)\<in>R))"
  by (simp add: ubd_mem_iff ub_def)

lemma ubd_mem_iff3:
  "b \<in> ubd R  X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. (a, b)\<in>R))"
  by (simp add: ubd_mem_iff ub_iff1)

lemma ubd_sub:
  "ubd R  X A \<subseteq> X"
   by(simp add: ubd_def)

lemma ubd_ant1:
  "A \<subseteq> B \<Longrightarrow> ubd R  X B \<subseteq> ubd R  X A"
  by (simp add: ubd_mem_iff subset_iff ub_ant2) 

lemma ubd_ant1b:
  "\<lbrakk>A \<subseteq> B; b \<in> ubd R  X B\<rbrakk> \<Longrightarrow> b \<in> ubd R  X A"
  using ubd_ant1 by blast

lemma ubd_iso2:
  "Y \<subseteq> X \<Longrightarrow> ubd R  Y A \<subseteq> ubd R  X A" 
  by (simp add:subset_iff ubd_def)

lemma ubd_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> ubd R  Y A \<rbrakk> \<Longrightarrow> x \<in> ubd R  X A"
  by (simp add: ubd_mem_iff in_mono)

lemma ubd_emptyI:
  "x \<in> X \<Longrightarrow> x \<in> ubd R  X {}"
  by (simp add: ubd_mem_iff3)

lemma ubd_empty:
  "ubd R  X {} = X"
   by(simp add: set_eq_iff ubd_mem_iff ub_def)

lemma ubd_singleton:
  "x \<in> X \<Longrightarrow> (x, x) \<in> R \<Longrightarrow> x \<in> ubd R  X {x}"
  by (simp add: ubd_def ub_singleton)

lemma ubd_singleton2:
  "\<lbrakk>x \<in> X; (y, x)\<in>R \<rbrakk> \<Longrightarrow>  x \<in> ubd R  X {y}"
  by (simp add: ub_singletonD ubdI2)

lemma ubd_singleton_iff:
  "x \<in> ubd R  X {y} \<longleftrightarrow> (x \<in> X \<and> (y, x)\<in>R)"
  by (simp add: ubd_mem_iff ub_singleton_simp)

lemma ubd_mem_insert:
  "\<lbrakk>c \<in> ubd R X F; (x, c) \<in> R\<rbrakk> \<Longrightarrow> c \<in> ubd R  X (insert x F)"
  by (simp add: ubd_mem_iff ub_insert)

lemma ubd_mem_binaryI:
  "\<lbrakk>(a, b)\<in>R; (b, b) \<in> R; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X {a, b}"
  by (simp add: ubdI2 ub_binaryI)

lemma ubd_mem_binaryD:
  "b \<in> ubd R  X {a, b} \<Longrightarrow> (a, b)\<in>R"
  by (simp add: ubdD1)

lemma ubd_mem_binary_iff1:
  "b \<in> ubd R X {a, b} \<longleftrightarrow> (a, b)\<in>R \<and> (b, b) \<in>R \<and>b \<in> X"
  by (meson ub_doubleE2 ubd_mem_binaryD ubd_mem_binaryI ubd_mem_iff)

lemma ubd_mem_doubleE1:
  "c \<in> ubd R  X {a, b} \<Longrightarrow> (a, c)\<in>R"
  by (simp add: ubdD1)

lemma ubd_mem_doubleE2:
  "c \<in> ubd R  X {a, b} \<Longrightarrow> (b, c)\<in>R"
  by (simp add: ubdD1)

lemma ubd_mem_doubleI:
  "\<lbrakk>(a, c)\<in>R; (b, c)\<in>R; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> ubd R  X {a, b}"
  by (simp add: ubd_empty ubd_mem_insert)

lemma ubd_mem_singleE:
  "x \<in> ubd R  X {a}\<Longrightarrow> (a, x) \<in> R"
  by (simp add: ubdD1)

lemma ubd_mem_binary:
  "b \<in> X \<Longrightarrow> (b, b) \<in> R \<Longrightarrow> (a, b)\<in>R \<longleftrightarrow> b \<in> ubd R  X {a, b}"
  by (simp add: ubd_mem_binary_iff1)

lemma ubd_mem_double:
  "c \<in> X \<Longrightarrow> c \<in> ubd R  X {a, b} \<longleftrightarrow> (a, c)\<in>R \<and> (b, c)\<in>R"
  by (simp add: ubd_mem_iff ub_double_iff1)

lemma upbd_neE1:
  "ubd R  X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> (a, x) \<in> R)"
  using ubd_mem_iff3 by fastforce

lemma upbd_neE3:
  "ubd R  X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. (a, x) \<in> R)"
  by (meson insertCI upbd_neE1)

lemma ubd_mem_unionI:
  "\<lbrakk>x \<in> ubd R  X A; x \<in> ubd R  X B\<rbrakk> \<Longrightarrow> x \<in> ubd R  X (A \<union> B)"
  by (simp add: ubd_mem_iff ub_unionI)

lemma ubd_mem_unionD1:
  " x \<in> ubd R  X (A \<union> B) \<Longrightarrow> x \<in> ubd R  X A "
  using ubd_ant1b[of A "A \<union> B" x R X] by blast

lemma ubd_mem_unionD2:
  " x \<in> ubd R  X (A \<union> B) \<Longrightarrow> x \<in> ubd R  X B "
  using ubd_ant1b[of B "A \<union> B" x R X]  by blast

lemma ubd_unI:
  "x \<in> X \<Longrightarrow> (\<And>A. A \<in> S \<Longrightarrow> x \<in> ubd R  X A) \<Longrightarrow> x \<in> ubd R  X (\<Union>S)"
  by (simp add: ubd_mem_iff3)

lemma ubd_unD:
  "x \<in> X \<Longrightarrow> x \<in> ubd R  X (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x \<in> ubd R  X A"
  using ubd_ant1b[of A "\<Union>S" x R X] by blast

lemma ubd_imageI:
  "x \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (f a, x)\<in>R) \<Longrightarrow> x \<in> ubd R  X (f`A)"
  by (simp add: ub_imageI ubdI2)

lemma ubd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> ub R A x \<Longrightarrow>ub R B x) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow>ub R B x \<Longrightarrow> ub R A x) \<Longrightarrow> ubd R  X A = ubd R  X B"
  by(auto simp add:set_eq_iff ubd_mem_iff)

lemma ubd_double1:
  " (a, b)\<in>R \<Longrightarrow>  ubd R  X {a, b} \<subseteq> ubd R  X {b}"
  by (simp add: ubd_ant1)

lemma ubd_double1b:
  " (a, b)\<in>R \<Longrightarrow> x \<in> ubd R  X {a, b} \<Longrightarrow> x \<in> ubd R  X {b}"
  by (simp add: ubd_mem_iff2)

lemma ubd_double2:
  "\<lbrakk>(a, b)\<in>R; a \<in>X; b \<in> X; trans_on X R\<rbrakk> \<Longrightarrow>  ubd R X {b} \<subseteq> ubd R  X {a, b}"
  by(auto simp add:ubd_def,meson trans_onD ub_insert ub_singletonI)

lemma ubd_double2b:
  "\<lbrakk>(a, b)\<in>R; a \<in>X; b \<in> X; trans_on X R\<rbrakk> \<Longrightarrow> x \<in> ubd R  X {b} \<Longrightarrow> x \<in> ubd R  X {a, b}"
  using ubd_double2 by fastforce

lemma ubd_double3:
  "\<lbrakk>(a, b)\<in>R; a \<in>X; b \<in> X; trans_on X R\<rbrakk> \<Longrightarrow> ubd R  X {a, b} = ubd R  X {b}"
  by (simp add: subset_antisym ubd_double1 ubd_double2)


subsection Composition

lemma lubd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> lbd R X (ubd R X A)"
  by (simp add: in_mono subsetI ubd_mem_iff3)

lemma lubd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R X E)) A"
  by (simp add: lubd_comp1)

lemma ulbd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ubd R X (lbd R X A)"
  by (simp add: in_mono subsetI ubd_mem_iff3)

lemma ulbd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. ubd R X E) \<circ> (\<lambda>E. lbd R X E)) A"
  by (simp add: ulbd_comp1)

lemma lubd_comp2:
  "A \<subseteq> B \<Longrightarrow> lbd R X (ubd R X A) \<subseteq> lbd R X (ubd R  X B)"
  by (simp add: ubd_ant1)

lemma lubd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) A  \<subseteq> ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) B"
  by (simp add:  ubd_ant1)

lemma ulbd_comp2:
  "A \<subseteq> B  \<Longrightarrow> ubd R  X (lbd R X A) \<subseteq> ubd R  X (lbd R X B)"
  by (simp add:  ubd_ant1)

lemma ulbd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) A  \<subseteq> ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) B"
  by (simp add:  ubd_ant1)

lemma lubd_comp3:
  "lbd R X (ubd R  X A) = lbd R X (ubd R  X (lbd R X (ubd R  X A)))"
  by (simp add: lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1)

lemma lubd_comp3b:
  " ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) A  = ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) A"
  using lubd_comp3 by force

lemma ulbd_comp3:
  "ubd R  X (lbd R X A) = ubd R  X (lbd R X (ubd R  X (lbd R X A)))"
  by (simp add: lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1)

lemma ulbd_comp3b:
  "((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) A  = ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) A"
  using ulbd_comp3 by force


section AbsoluteExtrema
subsection GreatestPredicate

lemma greatestI1:
  "m \<in> ubd R A A \<Longrightarrow> is_greatest R A m" 
  by (simp add: is_greatest_def)

lemma greatestI2:
  "\<lbrakk>ub R A m; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> (a, m) \<in> R); m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: ubI greatestI2)

lemma greatestI4:
  "\<lbrakk>m \<in> ubd R  X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: ubdD3 greatestI2)

lemma greatestD1:
  "is_greatest R A m \<Longrightarrow> (m \<in> A \<and> ub R A m)"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestD11:
  "is_greatest R A m \<Longrightarrow> m \<in> A"
  by (simp add: greatestD1)

lemma greatestD12:
  "is_greatest R A m \<Longrightarrow> ub R A m"
  by (simp add: greatestD1)

lemma greatestD2:
  "\<lbrakk>is_greatest R A m; a \<in> A\<rbrakk> \<Longrightarrow> (a, m) \<in>R"
  by (simp add: is_greatest_def ubdD1) 

lemma greatest_iff:
  "is_greatest R A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> (a, m)\<in>R))"
  by (simp add: ubd_mem_iff is_greatest_def ub_def)

lemma greatest_unique:
  "\<lbrakk>antisym_on A R; is_greatest R A m1; is_greatest R A m2\<rbrakk> \<Longrightarrow> m1 =m2"
  by (simp add: antisym_onD greatest_iff)

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest R A ma \<Longrightarrow> is_greatest R B mb \<Longrightarrow> (ma, mb)\<in>R"
  by (simp add: greatestD1 greatestD2 subset_iff)

lemma greatest_singleton:
  "(x, x) \<in> R \<Longrightarrow> is_greatest R {x} x"
  by (simp add: greatestI2 ub_singleton)

lemma singleton_ex_greatest:
  "(x, x) \<in> R \<Longrightarrow> (\<exists>m. is_greatest R {x} m)"
  by (meson greatest_singleton)

lemma greatest_insert1:
  "\<lbrakk>(x, x) \<in> R; ub R A x\<rbrakk> \<Longrightarrow> is_greatest R (insert x A) x"
  by (simp add: greatestI2 ub_insert)

lemma greatest_insert2:
  "is_greatest R A m \<Longrightarrow> (x, m)\<in>R \<Longrightarrow> is_greatest R (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma greatest_insert3:
  "\<lbrakk>trans_on X R; A \<subseteq> X; x \<in> X; (x,x)\<in>R\<rbrakk> \<Longrightarrow>is_greatest R A m \<Longrightarrow> (m, x)\<in>R \<Longrightarrow> is_greatest R (insert x A) x"
  by(rule greatestI2, meson greatestD11 greatestD2 in_mono trans_onD ubI ub_insert, blast) 

lemma lb_single_greatest1:
  "\<lbrakk>x \<in> X; (x, x) \<in> R\<rbrakk> \<Longrightarrow> is_greatest R (lbd R X {x}) x"
  by (simp add: greatest_iff ubd_singleton_iff)


subsection GreatestOperator

lemma greatest_equality:
  "\<lbrakk>antisym_on A R; (\<And>a. a \<in> A \<Longrightarrow> (a, m)\<in>R); m \<in> A\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: Greatest_def greatestI3 greatest_unique the_equality) 

lemma greatest_equality2:
  "\<lbrakk>antisym_on A R; is_greatest R A m\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: greatest_equality greatest_iff)

lemma greatest_equality3:
  "\<lbrakk>antisym_on A R;m \<in> ubd R A A\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: greatest_equality2 is_greatest_def)

lemma lb_single_greatest2:
  "\<lbrakk>(x, x) \<in> R; antisym_on X R; x \<in> X\<rbrakk> \<Longrightarrow> Greatest R (lbd R X {x}) = x"
  by (meson antisym_on_subset greatest_equality2 lb_single_greatest1 ubd_sub)

lemma greatest_exD0:
  "(\<exists>m. is_greatest R A m) \<Longrightarrow> A \<noteq> {}"
  using greatestD11 by force

lemma greatest_exD1:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> Greatest R A \<in> A"
  by (metis greatestD11 greatest_equality2)

lemma greatest_exD2:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, (Greatest R A)) \<in> R)"
  by (metis greatestD2 greatest_equality2)

lemma greatest_exD3:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> (Greatest R A) \<in> ubd R A A"
  by (simp add: greatest_exD1 greatest_exD2 ubd_mem_iff3)

lemma greatest_exD4:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow>  ub R A (Greatest R A)"
  by (metis greatestD12 greatest_equality2)

lemma greatest_exD5:
  "\<lbrakk>antisym_on B R; A \<subseteq> B; (\<exists>m. is_greatest R A m); (\<exists>m. is_greatest R B m)\<rbrakk> \<Longrightarrow> (Greatest R A, Greatest R B) \<in> R"
  by (metis antisym_on_subset greatest_equality2 is_greatest_iso2)

lemma greatest_singleton2:
  "(x, x) \<in> R  \<Longrightarrow> Greatest R {x} = x"
  by (simp add: antisym_on_def greatest_equality2 greatest_singleton)

lemma greatest_insert1b:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; x \<in> X; (x, x) \<in> R; ub R A x\<rbrakk> \<Longrightarrow> Greatest R (insert x A) = x"
  by (meson antisym_on_subset greatest_equality2 greatest_insert1 insert_subset)

lemma greatest_insert2b:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; x \<in> X; is_greatest R A m\<rbrakk> \<Longrightarrow> (x, m)\<in>R \<Longrightarrow> Greatest R (insert x A) = m"
  by (meson antisym_on_subset greatest_equality2 greatest_insert2 insert_subsetI)

lemma greatest_insert3b:
  "\<lbrakk>ord R X; A \<subseteq> X; x \<in> X; (x,x) \<in>R;is_greatest R A m\<rbrakk> \<Longrightarrow> (m, x)\<in>R \<Longrightarrow> Greatest R (insert x A) =  x"
  by (meson antisym_on_subset greatest_equality2 greatest_insert3 insert_subset)

lemma greatest_ub:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; is_greatest R A m\<rbrakk> \<Longrightarrow> ubd R A A = {m}"
  by (metis antisym_on_subset emptyE greatest_unique insertI1 is_greatest_def subset_iff subset_singletonD)

section Extrema
subsection Suprema


lemma is_supI1:
  "is_least R (ubd R X A) x \<Longrightarrow> is_sup R X A x"
  by (simp add: is_sup_def) 

lemma is_supD1:
  "is_sup R X A x \<Longrightarrow> (is_least R (ubd R  X A) x)"
  by (simp add: is_sup_def)

lemma is_supI2:
  "x \<in> lbd R (ubd R  X A) (ubd R  X A) \<Longrightarrow> is_sup R X A x"
  by (simp add: is_greatest_def is_supI1)

lemma is_supD2:
  "is_sup R X A x \<Longrightarrow> x \<in> lbd R (ubd R X A) (ubd R  X A)"
  by (simp add: is_greatest_def is_sup_def)

lemma is_supI3:
  "\<lbrakk>lb R (ubd R X A) x; x \<in> (ubd R X A)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestI2 is_supI1)

lemma is_supD31:
  "is_sup R X A x \<Longrightarrow> lb R (ubd R  X A) x"
  by (simp add: greatestD12 is_supD1)

lemma is_supD32:
  "is_sup R X A x \<Longrightarrow> x \<in> (ubd R X A)"
  by (simp add: greatest_iff is_sup_def)

lemma is_supI4:
  "\<lbrakk>lb R (ubd R  X A) x; x \<in> X; ub R A x\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI3 ubdI2)

lemma is_supE1:
  "is_sup R X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_supD32[of R X A x] ubdD2[of x R X A])

lemma is_supI5:
  "\<lbrakk>(\<And>a. a \<in> (ubd R  X A) \<Longrightarrow> (x, a) \<in> R); x \<in> (ubd R X A)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI1 greatestI3)

lemma is_supI6:
  "\<lbrakk>x \<in> X; ub R A x; (\<And>a. a \<in> (ubd R X A) \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI5 ubdI2)

lemma is_supI7:
  "\<lbrakk>x \<in> X; ub R A x; (\<And>a. a \<in> X \<Longrightarrow> ub R A a \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI4 ub_def ubd_mem_iff)

lemma is_supI8:
  "\<lbrakk>x \<in> X; (x, x) \<in> R; (\<And>z. z \<in> ubd R X A \<longleftrightarrow> (x, z) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI1 greatest_iff)

lemma is_supI9:
  "\<lbrakk>x \<in> X; (x, x) \<in> R; (\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z))\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI7)

lemma is_supI10:
  "\<lbrakk>x \<in> X; (\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R); (\<And>a. a \<in> X \<Longrightarrow> ub R A a \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI4 ub_def ubd_mem_iff)


lemma is_supE2:
  "is_sup R X A x \<Longrightarrow> ub R A x" 
  by(simp add:  ubdD3[of x R X A] is_supD32[of R X A x])            

lemma is_supE3:
  "\<lbrakk>is_sup R X A x; y \<in> ubd R X A\<rbrakk> \<Longrightarrow> (x, y)\<in>R "
  by (metis converseD greatestD2 is_sup_def)
                     
lemma is_supE4:
  "\<lbrakk>is_sup R X A x; y \<in> X; ub R A y\<rbrakk> \<Longrightarrow> (x, y)\<in>R "
  by (simp add: ubd_mem_iff is_supE3)
        
lemma is_supE5:
  "\<lbrakk>trans_on X R; (x, x) \<in> R; A \<subseteq> X;is_sup R X A x; z \<in> X;  (x, z) \<in> R\<rbrakk> \<Longrightarrow> z \<in> ubd R X A"
  by(rule ubdI2, meson in_mono is_supE1 is_supE2 trans_onD ubE ubI, blast)

lemma is_supD1121:
  "\<lbrakk>is_sup R X A x; a \<in> A \<rbrakk> \<Longrightarrow> (a, x) \<in> R"
  by (meson is_supE2 ubE)

lemma is_supE6:
  "\<lbrakk>trans_on X R; A \<subseteq> X; z \<in> X; is_sup R X A x; (x, z) \<in> R\<rbrakk> \<Longrightarrow> ub R A z"
  by (meson is_supE1 is_supE2 is_supE4 is_supE5 ubd_mem_iff)

lemma is_supE7:
  "\<lbrakk>trans_on X R; A \<subseteq> X; z \<in> X;is_sup R X A x;  (x, z) \<in> R; a \<in> A\<rbrakk> \<Longrightarrow> (a, z) \<in> R"
  by (meson is_supE6 ubE)

lemma is_supD41:
  "\<lbrakk>trans_on X R; A \<subseteq> X; z \<in> X;is_sup R X A x\<rbrakk> \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> (x, z) \<in> R \<Longrightarrow> ub R A z)"
  by (simp add: is_supE6)

lemma is_supD42:
  "\<lbrakk>trans_on X R; A \<subseteq> X; z \<in> X;is_sup R X A x\<rbrakk> \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> ub R A z \<Longrightarrow>  (x, z) \<in> R)"
  by (simp add: is_supE4)

lemma is_supD5:
  "\<lbrakk>trans_on X R; A \<subseteq> X;is_sup R X A x\<rbrakk> \<Longrightarrow> (\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z))"
  by (meson is_supD41 is_supD42)

lemma is_sup_iff1:
  "\<lbrakk>trans_on X R;x \<in> X; A \<subseteq> X; (x,x)\<in>R; (\<forall>a. a \<in> A \<longrightarrow> (a,  a) \<in> R)\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z)) \<longleftrightarrow> is_sup R X A x)"
  by (meson is_supD5 is_supI9)

lemma sup_iff2:
  "\<lbrakk>trans_on X R; A \<subseteq> X; (s,s)\<in>R; (\<forall>a. a \<in> A \<longrightarrow> (a,  a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  (s, z) \<in> R \<longleftrightarrow> z \<in> ubd R X A)"
  by (meson dual_order.refl is_supE1 is_supE3 is_supE5 is_supI5 ubdD2)

lemma is_sup_unique:
  "\<lbrakk>antisym_on X R; is_sup R X A m1;  is_sup R X A m2\<rbrakk> \<Longrightarrow> m1 = m2"
  by (simp add: antisym_on_def is_supD32 is_supE1 is_supE3)

lemma is_sup_iso1:
  "A \<subseteq> B \<Longrightarrow> is_sup R X A ma \<Longrightarrow> is_sup R X B mb \<Longrightarrow> (ma, mb)\<in>R "
  by (simp add: is_supE1 is_supE2 is_supE4 ub_ant2)

lemma is_sup_iso2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_sup R Y A my \<Longrightarrow> is_sup R X A mx \<Longrightarrow> (mx, my) \<in> R"
  by (simp add: in_mono is_supE1 is_supE2 is_supE4)

lemma sup_maxI1:
  "is_sup R X A x \<Longrightarrow> x \<in> A \<Longrightarrow> (is_greatest R A x)"
  by (simp add: greatestI2 is_supE2)

lemma sup_maxE1:
  "(is_greatest R A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestD11 greatestD12 is_supI6 ubdD1)

lemma sup_maxE2:
  "(is_greatest R A x) \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestD11 in_mono sup_maxE1)

lemma sup_max_eq:
  "A \<subseteq> X \<Longrightarrow> (is_sup R X A x \<and> x \<in> A) \<longleftrightarrow> (is_greatest R A x)"
  by (metis greatestD11 sup_maxE2 sup_maxI1)

lemma sup_max_eq2:
  "(is_sup R A A x) \<longleftrightarrow> (is_greatest R A x)"
  by (meson dual_order.refl is_supE1 sup_maxE2 sup_maxI1)

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup R B A s"
  by (meson is_supE2 is_supE3 is_supI6 ubd_iso2b)

lemma sup_singleton:
  "s \<in> X \<Longrightarrow> (s, s) \<in> R \<Longrightarrow> is_sup R X {s} s"
  by (simp add: greatest_singleton sup_maxE1)

lemma sup_emptyI:
  "is_least R X i \<Longrightarrow> is_sup R X {} i"
  by (simp add: is_sup_def ubd_empty)

lemma sup_emptyD:
  "is_sup R X {} i \<Longrightarrow> is_least R X i "
  by (simp add: is_sup_def ubd_empty)

lemma sup_empty:
  "is_sup R X {} i \<longleftrightarrow> (is_least R X i)"
  by (simp add: ubd_empty is_sup_def)

lemma binary_supI1:
  "\<lbrakk>a \<in> X; b \<in> X; (a, b)\<in>R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X {a, b} b"
  by (simp add: greatest_insert2 greatest_singleton sup_maxE1)

lemma binary_supI2:
  "\<lbrakk>a \<in> X; b \<in> X; (b, a) \<in> R; (a,a) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X {a, b} a"
  by (simp add: greatest_insert1 sup_maxE1 ub_singleton_simp)

lemma binary_supD21:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X; is_sup R X {a, b} s; (c, a) \<in> R; trans_on X R\<rbrakk> \<Longrightarrow>  (c, s) \<in> R"
  by (meson insertI1 is_supD1121 trans_onD)

lemma binary_supD22:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup R X {a, b} s; trans_on X R; (c ,b) \<in> R\<rbrakk> \<Longrightarrow>  (c, s) \<in> R"
  by (simp add: binary_supD21 insert_commute)

lemma binary_supD31:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow>  (a, s) \<in> R"
  by (simp add: is_supD1121)

lemma binary_supD32:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow>  (b, s) \<in> R"
  by (simp add: is_supD1121)

lemma binary_supD4:
  "\<lbrakk>trans_on X R; (s,s)\<in>R; (a, a) \<in>R; (b, b) \<in> R; a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> ((s, c) \<in> R \<longleftrightarrow> (a, c) \<in> R \<and> (b, c) \<in> R)"
  by (simp add: sup_iff2 ubd_mem_double)


lemma sup_insert1:
  "\<lbrakk>ub R A x; x \<in> X; (x, x) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) x"
  by (simp add: greatest_insert1 sup_maxE1)

lemma sup_insert2:
  "\<lbrakk>is_sup R X A m; (x, m)\<in>R\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) m"
  by (meson in_mono is_supE1 is_supE2 is_supE4 is_supI7 subset_insertI ub_def ub_insert)

lemma sup_insert3:
  "\<lbrakk>A \<subseteq> X; trans_on X R;is_sup R X A m; (x, x) \<in> R;(m, x)\<in>R; x \<in> X\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) x"
  by (simp add: is_supD41 sup_insert1)

lemma sup_insert61:
  "\<lbrakk>trans_on X R;A \<subseteq> X; is_sup R X A s1; is_sup R X {s1, x} s2\<rbrakk> \<Longrightarrow> ub R A s2"
  by (meson insertI1 is_supD1121 is_supD5 is_supE1)

lemma sup_insert62:
  "\<lbrakk>trans_on X R;A \<subseteq> X;is_sup R X A s1; is_sup R X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> ubd R  X A"
  by (simp add: is_supE1 sup_insert61 ubd_mem_iff)

lemma sup_insert7:
  "\<lbrakk>trans_on X R;A \<subseteq> X;is_sup R X A s1; is_sup R X {s1, x} s2; u \<in> ubd R  X (insert x A)\<rbrakk> \<Longrightarrow>  (s2, u) \<in> R"
  by (simp add: ubd_mem_iff2 is_supE3)

lemma ub_eq_sup_eq:
  "(\<And>x. ub R A x \<longleftrightarrow> ub R B x) \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (meson is_supE1 is_supE2 is_supE4 is_supI7)

lemma Upper_eq_sup_eq:
  "ubd R  X A = ubd R  X B \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (simp add: is_sup_def)

lemma sup_equality:
  "\<lbrakk>is_sup R X A m; antisym_on X R\<rbrakk> \<Longrightarrow> Sup R X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

lemma sup_exI:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; (\<exists>s. is_sup R X A s); (\<And>s. is_sup R X A s \<Longrightarrow> P s)\<rbrakk> \<Longrightarrow> P (Sup R X A)"
  using sup_equality  by metis

lemma sup_unc:
  "\<lbrakk>trans_on X R; A \<subseteq> X; B \<subseteq> X; antisym_on X R;is_sup R X (A \<union> B) s; is_sup R X A s1; is_sup R X B s2; is_sup R X {s1, s2} s3\<rbrakk> \<Longrightarrow> s=s3"
  by (smt (verit, ccfv_threshold) Un_least antisym_on_def binary_supD4 dual_order.eq_iff is_supD5 is_supE1 is_sup_iso1 le_supI2 sup.coboundedI1 ub_unionI)


lemma sup_families1:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i. i \<in> I \<longrightarrow> is_sup R X (A i) (s i)" and A2:"trans_on X R" and A3:"\<forall>i. i \<in> I \<longrightarrow> A i \<subseteq> X"
  shows "is_sup R X (\<Union>(A`I)) t \<longleftrightarrow> is_sup R X (s`I) t"
proof(rule Upper_eq_sup_eq)
  show "ubd R X (\<Union> (A ` I)) = ubd R X (s ` I)" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix u assume L:"u \<in> ?L"  show "u \<in> ?R" by (metis A1 L image_eqI is_supE3 ubdD2 ubd_imageI ubd_unD)
    qed
    next show "?R \<subseteq> ?L"
    proof
      fix u assume R:"u \<in> ?R" show "u \<in> ?L" 
      apply(rule ubd_unI, meson R ubdD2)
        using A1 A2 A3 R fbdE1 ubdD2 ubdD3  by (metis (full_types) image_iff is_supD5 ubdI2)
    qed
  qed
qed   

lemma sup_families1b:
  "\<lbrakk>trans_on X R; antisym_on X R; (\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X); A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si); x \<in> X\<rbrakk> \<Longrightarrow> ub R (Sup R X ` A) x \<Longrightarrow> ub R (\<Union> A) x"  
  by (metis fbdE1 is_supD41 sup_equality ub_unI)
lemma sup_families2b:
  "\<lbrakk>trans_on X R; antisym_on X R; (\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X); A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si); x \<in> X; ub R (\<Union>A) x\<rbrakk>   \<Longrightarrow>  ub R ((Sup R X) ` A) x" 
  by (metis is_supD5 sup_equality ub_imageI ub_unD)
lemma sup_families:
  "\<lbrakk>trans_on X R; antisym_on X R; (\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X); A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si)\<rbrakk> \<Longrightarrow>(is_sup R X ((\<lambda>Ai. Sup R X Ai)`A) s) \<longleftrightarrow> (is_sup R X (\<Union>A) s)"  
  by(rule Upper_eq_sup_eq, rule ubd_eqI1,simp add: sup_families1b,simp add: sup_families2b) 

lemma sup_finite:
  assumes A0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b \<in> X. is_sup R  X {a1, a2} b" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"trans_on X R" and
          A5:"antisym_on X R"
  shows "\<exists>b \<in> X. is_sup R X A b"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"s1 \<in> X" "is_sup R X F s1"
    using insert.hyps(4) insert.prems by blast
  obtain s2 where B2:"s2 \<in> X" "is_sup R X {s1, x} s2"
    by (meson A0 B0(1) insert.prems insert_subset)
  have B3:"is_sup R X (insert x F) s2"
  proof(rule is_supI5)
    show "\<And>a. a \<in> ubd R X (insert x F)  \<Longrightarrow> (s2, a) \<in> R"   by (meson A4 B0(2) B2(2) insert.prems insert_subset sup_insert7) 
    show "s2 \<in> ubd R X (insert x F)" by (metis A4 B0(1) B0(2) B2(1) B2(2) binary_supD32 insert.prems insert_subset sup_insert62 ubd_mem_insert)
  qed
  then show ?case
    using B2(1) by blast
qed

lemma bsup_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_sup R X {a1, a2} (Sup R X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans_on X R" and
          A5:"antisym_on X R"
  shows "is_sup R X A (Sup R X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"is_sup R X F s1"
    using insert.hyps(4) insert.prems by blast
  have B1:"s1 \<in> X" by (meson B0 is_supE1)
  obtain s2 where B2:"is_sup R X {s1, x} s2"
    using A0 B1 insert.prems by auto
  have B3:"s2 \<in> ubd R  X (insert x F)"
    by (meson A4 B0 B2 insert.prems insertCI insert_subset is_supD1121 sup_insert62 ubd_mem_insert)
  have B4:"\<And>u. u \<in> ubd R  X (insert x F) \<longrightarrow> (s2, u) \<in> R"
    by (meson A4 B0 B2 insert.prems insert_subset sup_insert7)
  have B3:"is_sup R X (insert x F) s2"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: A5 sup_equality)
qed

lemma bsup_commute:
  "is_sup R X {a, b} c \<longleftrightarrow> is_sup R X {b, a } c "
  by (simp add: insert_commute)

lemma bsup_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup R X {a, b} =  Sup R X  {b, a}"
  by (simp add: insert_commute)

lemma bsup_idem1:
  "\<lbrakk>(a, a) \<in> R; a\<in> X; antisym_on X R\<rbrakk> \<Longrightarrow> Sup R X {a, a} = a"
  by (simp add: sup_equality sup_singleton)

lemma sup_singleton2:
  "\<lbrakk>(a, a) \<in> R; a\<in> X; antisym_on X R\<rbrakk> \<Longrightarrow> Sup R X {a} = a"
  using bsup_idem1 by auto

lemma sup_ge1:
  "\<lbrakk>trans_on X R; c \<in> X; a \<in> X;b \<in> X; (c, a) \<in> R; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (c, s) \<in> R " 
  by (meson binary_supD31 is_supE1 trans_onD) 
lemma sup_ge2:
  "\<lbrakk>trans_on X R; c \<in> X; a \<in> X;b \<in> X; (c, b) \<in> R; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (c, s) \<in> R " 
  by (meson binary_supD32 is_supE1 trans_onD)
lemma sup_ge3:
  "\<lbrakk>trans_on X R; c \<in> X; a \<in> X;b \<in> X; (b, c) \<in> R; (a, c) \<in> R;is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (s, c) \<in> R " 
  by (simp add: is_supE4 ub_insert ub_singleton_simp)
lemma sup_ge4:
  "\<lbrakk>trans_on X R; x \<in> X; y \<in> X;z \<in> X; (x, y) \<in> R; is_sup R X {y, z} syz; is_sup R X {x, z} sxz\<rbrakk>  \<Longrightarrow> (sxz, syz) \<in> R " 
  by (metis sup_ge1 binary_supD32 is_supE1 sup_ge3)
lemma sup_ge5:
  "\<lbrakk>trans_on X R;is_sup R X {x1, x2} sx; is_sup R X {y1, y2} sy; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;(x1,y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow>(sx, sy) \<in> R"
  by (metis sup_ge1 sup_ge2 is_supE1 sup_ge3)
lemma ge_sup_iff:
  "\<lbrakk>trans_on X R; is_sup R X {a, b} s; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((s, c) \<in> R \<longleftrightarrow> (a, c) \<in> R \<and> (b, c) \<in> R)"
  by (meson binary_supD31 binary_supD32 is_supE1 sup_ge3 trans_onD)
lemma sup_assoc1:
  "\<lbrakk>trans_on X R; antisym_on X R; is_sup R X {a, b} sab; is_sup R X {sab, c} sab_c; is_sup R X {b, c} sbc; is_sup R X {a, sbc} sbc_a;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sbc_a = sab_c" 
  by (smt (verit, best) sup_ge1 antisym_onD binary_supD32 bsup_commute is_supE1 sup_ge3)
lemma sup_assoc2:
  "\<lbrakk>trans_on X R; antisym_on X R; is_sup R X {b, c} sbc; is_sup R X {a, sbc} sbc_a; is_sup R X {a, c} sac; is_sup R X {b, sac} sac_b;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sac_b = sbc_a" 
  by (meson bsup_commute sup_assoc1)
lemma sup_idem2:
  "\<lbrakk>a \<in> X; b \<in> X; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> is_sup R X {a, s} s"  
  by (simp add: binary_supD31 binary_supI1 is_supE1 is_supE2 is_supE4)
lemma sup_idem3:
  "\<lbrakk>a \<in> X; b \<in> X; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> is_sup R X {b, s} s" 
  by (simp add: bsup_commute sup_idem2)
lemma sup_upper_bounds:
  "\<lbrakk>is_sup R X A s; trans_on X R; A \<subseteq> X\<rbrakk> \<Longrightarrow>  ubd R X {s} = ubd R X A" 
  by (meson is_supD41 is_supE4 ub_singletonD ub_singletonI ubd_eqI1)

lemma ge_sup1:
  "\<lbrakk>antisym R X; a \<in> X; b \<in> X; (a, b)\<in>R;(b,b)\<in>R\<rbrakk> \<Longrightarrow>  Sup R X {a, b} = b"
  by (simp add: binary_supI1 sup_equality)

lemma ge_sup2:
  "\<lbrakk>antisym R X;a \<in> X; b \<in> X;(b, a)\<in>R;(a,a)\<in>R\<rbrakk> \<Longrightarrow> Sup R X {a, b} = a"
  by (simp add: binary_supI2 sup_equality)

subsection Duality

lemma sup_imp_inf_ub:
  "is_sup R X A s \<Longrightarrow>  is_inf R X (ubd R X A) s"
  by (simp add: is_supD1 sup_maxE2 ubd_sub)
  
lemma sup_if_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_inf R X (ubd R  X A) s \<Longrightarrow>  is_sup R X A s"
  by (metis converse_converse is_supD31 is_supE1 is_supE2 is_supI4 lubd_comp1 ub_ant2)
  
lemma inf_imp_sup_lb:
  "is_inf R X A s \<Longrightarrow>  is_sup R X (lbd R X A) s"
  using sup_imp_inf_ub by fastforce
  
lemma inf_if_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_sup R X (lbd R X A) s \<Longrightarrow>  is_inf R X A s"
  by (simp add: sup_if_inf_ub)


subsection Misc
definition pwr where "pwr X \<equiv> {(A, B). A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B}"

lemma pwr_memI:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> (A, B) \<in> pwr X"
  by (simp add: pwr_def) 

lemma pwr_memD:
  "(A, B) \<in> pwr X \<Longrightarrow> A \<subseteq> B \<and> B \<subseteq> X"
  by (simp add: pwr_def) 

lemma pwr_mem_iff:
  "(A, B) \<in> pwr X \<longleftrightarrow> (A \<subseteq> B) \<and> (B \<subseteq> X)"
  by(rule iffI, simp add:pwr_memD, simp add:pwr_memI)

lemma powsimp1:
  "A \<subseteq> Pow X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<subseteq> X"
  by auto

lemma powrel1:
  "antisym_on (Pow X) (pwr X)"  
  by(auto simp add:antisym_on_def pwr_def)

lemma powrel2:
  "trans_on (Pow X) (pwr X)"  
  by(auto simp add:trans_on_def pwr_def)

lemma powrel3:
  "refl_on (Pow X) (pwr X)"  
  by(auto simp add:refl_on_def pwr_def)

lemma powrel4a:
  "A \<subseteq> Pow X \<Longrightarrow> a \<in> Pow X \<Longrightarrow> lb (pwr X) A a \<Longrightarrow> a \<subseteq> X \<inter> \<Inter> A"
  by (metis Inf_greatest PowD converse_iff le_inf_iff pwr_memD ub_def)

lemma powrel4:
  "A \<subseteq> Pow X \<Longrightarrow> is_inf (pwr X) (Pow X) A (X \<inter>(\<Inter>A))" 
  apply(rule is_supI10, simp)
  apply(rule converseI)
  apply(rule pwr_memI)
  apply (simp add: Inter_lower le_infI2, simp add:powsimp1)
  apply(rule converseI)
  apply(rule pwr_memI)
  apply (metis powrel4a)
  by blast

lemma powrel5:
  "A \<subseteq> Pow X \<Longrightarrow> is_sup (pwr X) (Pow X) A (\<Union>A)" 
  by(auto simp add:is_sup_def is_greatest_def ubd_def ub_def pwr_def)
lemma powrel6:
  "C \<subseteq> Pow X \<Longrightarrow> antisym_on C (pwr X)" 
   by (meson antisym_on_subset powrel1)
lemma powrel7:
  "C \<subseteq> Pow X \<Longrightarrow> trans_on C (pwr X)"  
  by (meson powrel2 trans_on_subset)  
lemma powrel8:
  "(x, y) \<in> pwr X \<Longrightarrow> x \<subseteq> y"  
  by (simp add: pwr_def) 
lemma powrel9:
  "\<lbrakk>A \<subseteq> C; C\<subseteq> Pow X\<rbrakk> \<Longrightarrow> is_sup (pwr X) (Pow X) A (\<Union>A)"
  by(auto simp add:is_sup_def is_greatest_def ubd_def ub_def pwr_def)

lemma powrel4b:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (pwr X) (Pow X) A (\<Inter>A)"
  by (metis Inf_lower2 Int_absorb1 equals0I powrel4 powsimp1) 

lemma uni_sup_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Union>A \<in> S\<rbrakk> \<Longrightarrow> is_sup (pwr (\<Union>S)) S A (\<Union>A) "
  by (meson powrel9 subset_Pow_Union sup_in_subset)

lemma uni_inf_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Inter>A \<in> S\<rbrakk> \<Longrightarrow> is_inf (pwr (\<Union>S)) S A (\<Inter>A) "
  by (metis Union_upper inf.absorb_iff2 le_supE powrel4 subset_Pow_Union subset_Un_eq sup_in_subset)


lemma lattice_id6:
  "\<lbrakk>trans_on X R; A \<subseteq> X; B \<subseteq> X; is_sup R X A s; is_inf R X B i\<rbrakk> \<Longrightarrow> (s, i) \<in> R \<Longrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. (a, b)\<in>R) "
  by (meson converse.cases in_mono is_supD1121 is_supE1 trans_onD)

lemma lattice_id7:
  "\<lbrakk>A \<subseteq> lbd R X B; is_sup R X A s; is_inf R X B i\<rbrakk> \<Longrightarrow> (s,i) \<in> R "
  using inf_imp_sup_lb is_sup_iso1  by metis

lemma lattice_id8:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup R X A s; is_inf R X B i;(\<forall>a \<in> A. \<forall>b \<in> B. (a, b)\<in>R)\<rbrakk> \<Longrightarrow> (s, i) \<in> R"
  by (meson converse_iff in_mono is_supE1 is_supE4 ubI)
  

lemma lattice_id9:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup R X A s; is_inf R X B i;(\<forall>a \<in> A. lb R B a)\<rbrakk> \<Longrightarrow> (s, i) \<in> R"
  using is_supD42 is_supE1 is_supD5 ubI lattice_id8 ubE by fastforce 

lemma least_inf:
  "\<lbrakk>antisym_on X R; is_least R X bot\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Inf R X {x, bot} = bot"
  by (metis Sup_def antisym_on_converse binary_supI1 greatestD1 greatestD2 sup_equality)

lemma least_sup:
  "\<lbrakk>antisym_on X R;is_least R X bot; (x,x)\<in> R\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Sup R X {x, bot} = x"
  by (meson binary_supI2 converseD greatestD11 greatestD2 sup_equality)

lemma greatest_inf:
  "\<lbrakk>antisym_on X R; is_greatest R X top; (x,x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Inf R X {x, top} = x"
  by (metis Sup_def antisym_on_converse converseI converse_converse least_sup)


lemma greatest_sup:
  "\<lbrakk>antisym_on X R; is_greatest R X top\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Sup R X {x, top} = top"
  by (simp add: binary_supI1 greatestD11 greatestD2 sup_equality)



subsection MinimaMaxima

definition is_maximal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_maximal R A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> (x, a) \<in> R \<longrightarrow> a =x)"

definition is_minimal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_minimal R A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> (a, x) \<in> R\<longrightarrow> a = x)"

lemma maximalD1:
  "is_maximal R A x \<Longrightarrow> x \<in> A"
  by(simp add:is_maximal_def)

lemma maximalD2:
  "is_maximal R A x \<Longrightarrow>(\<forall>a. a \<in> A \<and> (x, a) \<in> R \<longrightarrow> a =x)"
  by(simp add:is_maximal_def)

lemma maximalD3:
  "is_maximal R A x \<Longrightarrow> a \<in> A \<Longrightarrow> (x, a) \<in> R \<Longrightarrow> a = x"
  by(simp add:is_maximal_def)

lemma maximalI1:
  "\<lbrakk>x \<in> A; (\<And>a. \<lbrakk>a \<in> A; (x, a) \<in> R\<rbrakk> \<Longrightarrow> a = x)\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by(simp add:is_maximal_def)

subsection SupSemilattices


lemma ssupD2:
  "\<lbrakk>is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X {a, b} x) "
  by (simp add: is_sup_semilattice_def)

lemma ssupD3:
  "\<lbrakk>antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {a, b} (Sup R X {a, b}) "
  using ssupD2 sup_equality by metis

lemma ssupD4:
  "\<lbrakk>antisym_on X R;is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  (Sup R X {a, b}) \<in> X"
  by (metis is_supE1 ssupD3) 

lemma bsup_geI1:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X; (c, a) \<in> R\<rbrakk>  \<Longrightarrow> (c, Sup R X {a, b}) \<in> R"
  by (simp add: binary_supD21 ssupD3 ssupD4)

lemma bsup_geI2:
  "\<lbrakk>ord R X;is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (c, b)\<in>R\<rbrakk>  \<Longrightarrow> (c, Sup R X {a, b}) \<in> R"
  by (simp add: binary_supD22 ssupD3 ssupD4)

lemma bsup_geI3:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (a, c) \<in> R; (b, c)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {a, b}, c) \<in> R"
  by (meson ssupD3 sup_ge3)

lemma bsup_geI4:
  "\<lbrakk>ord R X; is_sup_semilattice R X; x \<in> X; y \<in> X; z \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {x, z}, Sup R X {y, z}) \<in> R"
  by (simp add: binary_supD32 bsup_geI1 bsup_geI3 ssupD3 ssupD4)

lemma bsup_geI5:
  "\<lbrakk>ord R X; is_sup_semilattice R X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;(x1,y1)\<in>R; (x2, y2)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {x1, x2}, Sup R X {y1, y2})\<in>R"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)


lemma bsup_rev:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X; (Sup R X {a, b}, c) \<in> R\<rbrakk>  \<Longrightarrow> (a, c)\<in>R \<and> (b, c)\<in>R"
  by (meson ge_sup_iff ssupD3)

lemma bsup_iff:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((Sup R X {a, b}, c) \<in> R \<longleftrightarrow> (a, c)\<in>R \<and> (b, c)\<in>R)"
  using bsup_rev[of X R] bsup_geI3[of X R] by metis


lemma bsupI:
  "\<lbrakk>ord R X; is_sup_semilattice R X; (\<And>s. is_sup R X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Sup R X {a, b})"
  by (metis is_sup_semilattice_def sup_equality)

lemma bsup_commute1:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, b} = Sup R X {b, a}"
  by (simp add: insert_commute)

lemma bsup_assoc1:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a, b}, c} =Sup R X {a, Sup R X {b, c}}"
  proof-
    assume A:"ord R X" "is_sup_semilattice R X" "a \<in> X" "b \<in> X" "c \<in> X"
    obtain B0:"Sup R X {b, c} \<in> X" and B1:"(Sup R X {a, b}) \<in> X" by(simp add: A ssupD4)
    have B2:"(c, Sup R X {b, c}) \<in> R" by (meson A B0 binary_supD32 ssupD3)
    have B3:"(Sup R X {Sup R X {a, b}, c}, Sup R X {a, Sup R X {b, c}}) \<in> R"   by (metis A binary_supD32 bsup_commute1 bsup_geI2 bsup_geI3 ssupD3 ssupD4)
    also have B4:"(Sup R X {a, Sup R X {b, c}}, Sup R X {Sup R X {a, b}, c}) \<in> R"   by (metis A binary_supD31 binary_supD32 bsup_geI3 bsup_rev ssupD3 ssupD4)
    then show "Sup R X {Sup R X {a, b}, c}=Sup R X {a, Sup R X {b, c}}" by (meson A B0 B1 antisym_onD calculation ssupD4) 
qed

lemma binf_assoc1:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, c} =Inf R X {a, Inf R X {b, c}}"
  using bsup_assoc1[of X "converse R" a b c]  by (simp add: Sup_def is_sup_semilattice_def)

lemma bsup_assoc11:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {c, Sup R X {a, b}} =Sup R X {a, Sup R X {b, c}}"
  by (metis bsup_assoc1 bsup_commute1)

lemma binf_assoc11:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {c, Inf R X {a, b}} =Inf R X {a, Inf R X {b, c}}"
  using bsup_assoc11[of X "converse R" a b c] by (simp add: Sup_def is_sup_semilattice_def)

lemma bsup_assoc12:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {c, Sup R X {a, b}} =Sup R X {Sup R X {b, c},a}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc13:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a, b}, c} =Sup R X {Sup R X {b, c},a}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc14:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b, a}, c} =Sup R X {Sup R X {b, c},a}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc15:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b, a}, c} =Sup R X {Sup R X {c,b},a}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc2:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, Sup R X {b, c}} = Sup R X {b, Sup R X {a, c}}"
  by (metis bsup_assoc1 doubleton_eq_iff)

lemma binf_assoc2:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {a, Inf R X {b, c}} = Inf R X {b, Inf R X {a, c}}"
  using bsup_assoc2[of X "converse R" a b c] by (simp add: Sup_def is_sup_semilattice_def)

lemma bsup_assoc2a:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b, c},a} = Sup R X {b, Sup R X {a, c}}"
  by (metis bsup_assoc1 doubleton_eq_iff)

lemma bsup_assoc2b:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b, c},a} = Sup R X {Sup R X {a, c},b}"
  by (metis bsup_assoc1 doubleton_eq_iff)

lemma bsup_assoc2c:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a,Sup R X {b, c}} = Sup R X {Sup R X {a, c},b}"
  by (metis bsup_assoc1 doubleton_eq_iff)

lemma binf_assoc2a:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {b, c},a} = Inf R X {b, Inf R X {a, c}}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma binf_assoc2b:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {b, c},a} = Inf R X {Inf R X {a, c},b}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma binf_assoc2c:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {a, Inf R X {b, c}} = Inf R X {Inf R X {a, c},b}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma binf_assoc2d:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, c} = Inf R X {a, Inf R X {b, c}}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma bsup_idem2:
  "\<lbrakk>ord R X;is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {a, Sup R X {a, b}} =  Sup R X {a, b}"
  by (simp add: bsupI sup_equality sup_idem2)

lemma bsup_idem3:
  "\<lbrakk>ord R X;is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a, b}, b} =  Sup R X {a, b}"
  by (metis bsup_idem2 doubleton_eq_iff)

lemma bsup_ge1:
  "\<lbrakk>antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X; (b,b)\<in>R; (a, b)\<in>R\<rbrakk> \<Longrightarrow>  Sup R X {a, b} = b"
  by (simp add: binary_supI1 sup_equality)

lemma bsup_ge2:
  "\<lbrakk>antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X; (a,a)\<in>R; (b, a)\<in>R\<rbrakk> \<Longrightarrow>  Sup R X {a, b} = a"
  by (simp add: binary_supI2 sup_equality)

lemma ge_bsup1:
  "\<lbrakk>antisym_on X R;is_sup_semilattice R X; a \<in> X; b \<in> X; Sup R X {a, b} = b\<rbrakk> \<Longrightarrow> (a, b)\<in>R"
  by (metis binary_supD31 ssupD3)

lemma ge_bsup2:
  "\<lbrakk>antisym_on X R;is_sup_semilattice R X; a \<in> X; b \<in> X; Sup R X {a, b} = a\<rbrakk> \<Longrightarrow>  (b, a)\<in>R"
  by (simp add: bsup_commute2 ge_bsup1)

lemma bsup_finite2:
  "\<lbrakk>ord R X; is_sup_semilattice R X; A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup R X A (Sup R X A)"
  by (simp add: bsup_finite ssupD3)

lemma fsup_geI1:
  "\<lbrakk>ord R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; a \<in> A\<rbrakk> \<Longrightarrow> (a, Sup R X A) \<in>R"
  using is_supD1121[of R X A "Sup R X A" a]  bsup_finite2[of X R A] by blast

lemma fsup_ub:
  "\<lbrakk>ord R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> ub R A (Sup R X A)"
  using is_supD32[of R X A "Sup R X A"] bsup_finite2[of X R A]   by (simp add: ubdD3)

lemma fsup_lub:
  "\<lbrakk>ord R X;is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> ubd R X A\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R"
  using is_supE3[of R X A "Sup R X A" b] bsup_finite2[of X R  A] by fastforce

lemma fsup_lub2:
  "\<lbrakk>ord R X;is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> X; ub R A b\<rbrakk> \<Longrightarrow>(Sup R X A, b) \<in> R"
  by (simp add: fsup_lub ubdI2)

lemma fsup_lub3:
  "\<lbrakk>ord R X; is_sup_semilattice R X;  A \<in> Fpow_ne X; b \<in> ubd R X A\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R"
  by (simp add: fpow_ne_iff2 fsup_lub)
lemma fsup_closedD1:
  "\<lbrakk>ord R X; is_fsup_closed R X A\<rbrakk> \<Longrightarrow> (\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup R X {a1, a2} \<in> A)"
  by (simp add: is_fsup_closed_def)

lemma finite_sup_closed2:
  assumes A0: " (\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup R X {a1, a2} \<in> A)" and 
          A1: "finite E" and
          A2: "E \<noteq> {}" and
          A3: "E \<subseteq> A" and
          A4: "A \<subseteq> X" and
          A5: "is_sup_semilattice R X" and 
          A6:"antisym_on X R" and 
          A7:"trans_on X R"
  shows "Sup R X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  obtain s where A6: "is_sup R X F s"
    by (meson A4 A5 A6 A7 bsup_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset subset_trans)
  have B0: "s \<in> A"
    by (metis A4 A5 A6 assms(7) insert.hyps(4) insert.prems(1) insert_subset sup_equality)
  have B1: "x \<in> A"
    using insert.prems(1) by auto
  obtain t where A7: "is_sup R X {x, s} t"
    by (meson A4 A5 A6 B1 in_mono is_supE1 ssupD2)
  have B2: "t \<in> A"
    by (metis A0 A7 B0 B1 assms(7) sup_equality)
  have B3: "t \<in> ubd R  X (insert x F)"
    by (metis A4 A6 A7 B2 assms(8) insert.prems(1) insert_commute insert_subset is_supE2 subset_iff sup_insert61 ub_double_iff1 ubd_mem_iff ubd_mem_insert)
  have B4: "\<And>y. y \<in> ubd R X (insert x F) \<longrightarrow> (t, y)\<in>R"
    by (meson A4 A6 A7 assms(8) bsup_commute insert.prems(1) insert_subset subset_trans sup_insert7)
  have B5: "is_sup R X (insert x F) t"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: B2 assms(7) sup_equality)
qed

lemma sup_semilattice_fsup_closed:
  "\<lbrakk>ord R X;is_fsup_closed R X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> Sup R X E \<in> A "
  by (metis finite_sup_closed2 is_fsup_closed_def)

lemma sup_semilattice_fsup:
  "\<lbrakk>ord R X;is_sup_semilattice R X; A \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (simp add: bsup_finite2 fpow_ne_iff2)

lemma fsupI:
  "\<lbrakk>ord R X; is_sup_semilattice R X; (\<And>s E. is_sup R X E s \<Longrightarrow> P s); F \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> P (Sup R X F)"
  using sup_semilattice_fsup by blast

lemma sup_semilattice_fsup_props0:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, b, c}  \<in> X"
  by(erule fsupI,simp add:is_supE1,simp add: is_supE1,simp add: fpow_ne_iff2)

lemma sup_assoc_ubd1:
  "\<lbrakk>trans_on X R; a \<in>X; b \<in> X; c \<in> X; is_sup R X {b, c} s; x \<in> ubd R  X {a, s}\<rbrakk> \<Longrightarrow> x \<in> ubd R  X {a, b, c}"
  by (metis ge_sup_iff ub_double_iff1 ubd_mem_iff ubd_mem_insert)


lemma finite_inf_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>  Inf R X {a1, a2} \<in> A" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> A" and
          A4:"A \<subseteq> X" and
          A5:"is_inf_semilattice R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "Inf R X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)  then show ?case    using A0 by fastforce
next
  case (insert x F)
  obtain i where A8:"is_inf R X F i"    by (metis A4 A5 A6 A7 antisym_on_converse bsup_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset is_sup_semilattice_def subset_trans trans_on_converse)
  have B0:"i \<in> A" by (metis A4 A5 A6 A8 Sup_def antisym_on_converse insert.hyps(4) insert.prems(1) insert_subset sup_equality)
  have B1:"x \<in> A" using insert.prems(1) by auto
  obtain t where A9:"is_inf R X {x, i} t" by (meson A4 A5 A8 dual_order.trans insert.prems(1) insert_subset is_supE1 ssupD2)
  have B2:"t \<in> A" by (metis A0 A6 A9 B0 B1 antisym_on_converse sup_equality the_equality)  
  have B3:"t \<in> (lbd R X (insert x F))"  by (meson A4 A7 A8 A9 bsup_commute insert.prems(1) insertCI insert_subset is_supD1121 subset_trans sup_insert62 trans_on_converse ubd_mem_insert)
  have B4:"\<And>y. y \<in> (lbd R X (insert x F)) \<longrightarrow> (y,t)\<in>R"  by (meson A4 A7 A8 A9 bsup_commute converse_iff insert.prems(1) insert_subset subset_trans sup_insert7 trans_on_converse)
  have B5:"is_inf R X (insert x F) t"  by (simp add: B3 B4 is_supI5)
  then show ?case   by (metis B2 A6 Sup_def antisym_on_converse sup_equality)
qed


subsection Lattices

lemma lattI1:
  "\<lbrakk>X \<noteq> {}; (\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf R X {a, b} x) \<and>  (\<exists>x. is_sup R X {a, b} x))\<rbrakk> \<Longrightarrow> is_lattice R X"
  by (simp add: is_lattice_def)

lemma lattI2:
  "\<lbrakk>is_inf_semilattice R X; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> is_lattice R X"
  by (simp add: is_sup_semilattice_def lattI1)

lemma lattI3:
  "is_inf_semilattice R X \<and> is_sup_semilattice R X \<Longrightarrow> is_lattice R X"
  by (simp add: lattI2)

lemma lattD1:
  "is_lattice R X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_lattice_def)

lemma lattD21:
  "\<lbrakk>is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf R X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD22:
  "\<lbrakk>is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_sup R X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD32:
  "\<lbrakk>antisym_on X R;is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_sup R X {a, b} (Sup R X {a, b}) "
  by (metis lattD22 sup_equality)

lemma lattD31:
  "\<lbrakk>antisym_on X R; is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_inf R X {a, b} (Inf R X {a, b})"
  by (metis Sup_def antisym_on_converse lattD21 sup_equality)

lemma lattD41:
  "is_lattice R X \<Longrightarrow> is_inf_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD42:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD4:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice R X \<and> is_inf_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD5:
  "\<lbrakk>antisym_on X R; is_lattice R X; x \<in> X; y \<in> X; Sup R X {x, y} = y\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  by (simp add: ge_bsup1 lattD42)

lemma latt_iff:
  "is_lattice R X \<longleftrightarrow> (is_inf_semilattice R X) \<and> (is_sup_semilattice R X)"
  by(rule iffI,simp add:lattD4,simp add:lattI3)

lemma latt_ge_iff1:
  "\<lbrakk>ord R X; is_lattice R X; (y,y)\<in>R;x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> ((x, y)\<in>R \<longleftrightarrow> Sup R X {x, y} = y)"
  by (auto simp add: bsup_ge1 lattD42 lattD5)

lemma latt_ge_iff2:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> ((y, x)\<in>R \<longleftrightarrow> Sup R X {x, y} = x)"
  by (simp add: bsup_commute2 latt_ge_iff1)

lemma lattice_absorb1:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {x, y}} = x"
  by (meson binary_supD31 bsup_ge2 converseD is_supE1 lattD31 lattD42)

lemma lattice_absorb13:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y,x}} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb12:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Inf R X {x, y},x} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb14:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Inf R X {y,x},x} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb15:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Inf R X {x,y},x} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb2:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x,Sup R X {x, y}} = x"
  by (meson antisym_on_converse binary_supD31 binary_supI2 converse_iff is_sup_unique lattD31 lattD32 lattD42 ssupD4)

lemma lattice_absorb21:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Sup R X {x, y},x} = x"
  by (simp add: insert_commute lattice_absorb2)

lemma lattice_absorb22:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x,Sup R X {y,x}} = x"
  by (simp add: insert_commute lattice_absorb2)

lemma lattice_absorb23:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Sup R X {y,x},x} = x"
  by (simp add: insert_commute lattice_absorb2)

lemma distrib_sup_le: 
  "\<lbrakk>ord R X;is_lattice R X;x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {x, Inf R X {y, z}}, Inf R X {Sup R X {x, y}, Sup R X {x, z}})\<in>R"
  by (smt (verit, del_insts) binary_supD31 binary_supD32 converse_iff is_supE1 lattD31 lattD32 sup_ge3 sup_ge5 trans_on_converse)

lemma distrib_inf_le: 
  "\<lbrakk>ord R X;is_lattice R X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {Inf R X {x, y}, Inf R X {x, z}}, Inf R X {x, Sup R X {y, z}}) \<in> R"
  by (smt (verit, del_insts) binary_supD31 binary_supD32 converse_iff is_supE1 lattD31 lattD32 sup_ge3 sup_ge5 trans_on_converse)

lemma mod_sup_le:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X; (x, z)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {x, Inf R X {y, z}}, Inf R X {Sup R X {x, y}, z})\<in>R"
  by (smt (verit, del_insts) binary_supD31 binary_supD32 converse_iff is_supE1 lattD31 lattD32 sup_ge3 sup_ge4 trans_on_converse)
subsection DistributiveLattices

lemma distribD1:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" and
          A4:" x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  obtain A5:"is_sup_semilattice R X" and A6:"is_inf_semilattice R X" using A0 lattD4 by blast
  obtain A7:"Inf R X {y, z} \<in> X" and A8:"Inf R X {x, z} \<in> X" and A9:"Sup R X {x, y} \<in> X"  by (meson A0 A1 A4 A5 is_supE1 lattD31 ssupD4)
  have B0:"Sup R X {x, Inf R X {y, z}} = Sup R X {Sup R X {x, Inf R X {x, z}}, Inf R X {y, z}}"  (*x \<or> (x \<and> z) = ((x \<or> (x \<and> z) \<or> (z \<and> y)))*)
    by (metis A0 A1 A2 A4 lattice_absorb1 reflD1)
  have B1:"... = Sup R X {x, Sup R X {Inf R X {z, x}, Inf R X {z, y}}}" (* x \<or> ((z \<and> x) \<or> (z \<and> y)) *)
    using bsup_assoc14[of X R "Posets17.Inf R X {x, z}" x "Posets17.Inf R X {y, z}"]
    by (metis A1 A4 A5 A7 A8 bsup_assoc15 doubleton_eq_iff)
  have B2:"... = Sup R X {x, Inf R X {z, Sup R X {x, y}}}" (*x \<or> (z \<and> (x \<or> y))*)
    by (simp add: A3 A4) 
  have B3:"... = Sup R X {Inf R X {Sup R X {x, y}, x}, Inf R X {Sup R X {x, y}, z}}"
    by (metis A0 A1 A2 A4 lattice_absorb21[of X R x y] doubleton_eq_iff refl_def)
  have B4:"... = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    by (simp add: A3 A4 A9)
  show ?thesis
    by (simp add: B0 B1 B2 B3 B4)
qed

lemma distI1:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" 
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" 
proof- 
  fix x y z assume A4:"x\<in>X""y\<in>X""z\<in>X"
  then show "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" 
  by(simp add:A0 A1 A2 A3 A4 distribD1[of R X x y z])
qed

lemma distribD2:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3: "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" and
          A4: "x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
proof-
  obtain A5:"is_sup_semilattice R X" and A6:"is_inf_semilattice R X" using A0 lattD4 by blast
  obtain A7:"Sup R X {z, y} \<in> X" and A8:"Sup R X {x, z} \<in> X" and A9:"Inf R X {x, y} \<in> X" by (meson A0 A1 A4 A5 is_supE1 lattD31 ssupD4) 
  have B0:"Inf R X {x, Sup R X {y, z}} = Inf R X {Inf R X {x, Sup R X {x, z}}, Sup R X {y, z}}"(*x \<and> (x \<or> z) = ((x \<and> (x \<or> z)) \<and> (z \<or> y)))*)
    by (metis A0 A1 A2 A4 lattice_absorb2 reflE1)  
  have B1:"... = Inf R X {Inf R X {x, Sup R X {z, x}}, Sup R X {z, y}}" (*(x \<and> (z \<or> x)) \<and> (z \<or> y)*)
    by (simp add: insert_commute)
  have B2:"... = Inf R X {x, Inf R X {Sup R X {z, x}, Sup R X {z, y}}}" (* x \<and> ((z \<or> x) \<or> (z \<or> y)) *)
    using binf_assoc2d[of X R x "Sup R X {z, x}" "Sup R X {z, y}"]  by (simp add: A1 A4 A5 A6 ssupD4)
  have B3:"... = Inf R X {x, Sup R X {z, Inf R X {x, y}}}" (*x \<and> (z \<or> (x \<and> y))*)
    by (simp add: A3 A4) 
  have B4:"... = Inf R X {Sup R X {Inf R X {x, y}, x}, Sup R X {Inf R X {x, y}, z}}" (* ((x \<and> y) \<or> x) \<and> ((x \<and> y) \<or> z) *)
    by (metis A0 A1 A2 A4 lattice_absorb15[of X R x y] doubleton_eq_iff refl_def)
  have B5:"... = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    by (simp add: A3 A4 A9)
  show ?thesis
    by (simp add: B0 B1 B2 B3 B4 B5)
qed

lemma distI2:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" 
proof- 
  fix x y z assume A4:"x\<in>X""y\<in>X""z\<in>X"
  then show "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" 
  by(simp add:A0 A1 A2 A3 A4 distribD2[of R X x y z])
qed

lemma distribD3:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  fix x y z assume A4:"x\<in>X""y\<in>X""z\<in>X"
  let ?a="Sup R X {x, Inf R X {y, z}}" let ?b="Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  obtain A5:"?a\<in>X" and A6:"?b\<in>X"  by (meson A0 A1 A4(1) A4(2) A4(3) is_supE1 lattD31 lattD42 ssupD4)
  have B0:"(?a, ?b)\<in>R"   by (simp add: A0 A1 A4(1) A4(2) A4(3) distrib_sup_le) 
  also have B1:"(?b, ?a)\<in>R" by (simp add: A3 A4(1) A4(2) A4(3)) 
  then show "?a=?b" by (meson A1 A5 A6 antisym_onD calculation)
qed

lemma distribD4:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
proof-
  fix x y z assume A4:"x\<in>X""y\<in>X""z\<in>X"
  let ?a="Inf R X {x, Sup R X {y, z}}" let ?b="Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  obtain A5:"?a\<in>X" and A6:"?b\<in>X"  by (meson A0 A1 A4(1) A4(2) A4(3) is_supE1 lattD31 lattD42 ssupD4)
  have B0:"(?a, ?b)\<in>R"  using A3 A4(1) A4(2) A4(3) by presburger
  also have B1:"(?b, ?a)\<in>R" by (simp add: A0 A1 A4(1) A4(2) A4(3) distrib_inf_le)
  then show "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" by (meson A1 A5 A6 antisym_onD calculation)
qed


lemma distI3:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R" 
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  have B0:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    by (metis A0 A1 A3 distrib_inf_le antisym_on_def is_supE1 lattD31 lattD42 ssupD4)
  then show B1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" 
  proof-
     fix x y z assume A4:"x \<in> X" "y \<in> X" "z \<in> X"
     then show "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
      by(simp add: A0 A1 A2 A3 A4 B0 distribD1[of R X x y z])
  qed
qed


lemma distI4:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow>  (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {Inf R X {x, y}, Inf R X {x, z}} = Inf R X {x, Sup R X {y, z}}"
proof-
  have B0:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow>  Inf R X {Sup R X {x, y}, Sup R X {x, z}}= Sup R X {x, Inf R X {y, z}}"
    by (metis A0 A1 A3 distrib_sup_le antisym_on_def is_supE1 lattD31 lattD42 ssupD4)
  then show B1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {Inf R X {x, y}, Inf R X {x, z}} = Inf R X {x, Sup R X {y, z}}" 
  proof-
     fix x y z assume A4:"x \<in> X" "y \<in> X" "z \<in> X"
     then show "Sup R X {Inf R X {x, y}, Inf R X {x, z}} = Inf R X {x, Sup R X {y, z}}"
      by(simp add: A0 A1 A2 A3 A4 B0 distribD2[of R X x y z])
  qed
qed


lemma distr_latticeI1:
  "\<lbrakk>ord R X; refl R X; is_lattice R X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R)\<rbrakk> \<Longrightarrow> distributive_lattice R X"
  by(simp add:distributive_lattice_def distribD3)

lemma distr_latticeI2:
  "\<lbrakk>ord R X; refl R X; is_lattice R X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R)\<rbrakk> \<Longrightarrow> distributive_lattice R X"
  by(simp add:distributive_lattice_def distI3)


lemma distr_latticeD1:
  "\<lbrakk>distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}} "
  by (simp add: distributive_lattice_def insert_commute)

lemma distr_latticeD2:
  "\<lbrakk>distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup R X {Inf R X {y, z}, x} = Inf R X {Sup R X {y, x}, Sup R X {z, x}}"
  by (simp add: distributive_lattice_def insert_commute)
 
lemma distr_latticeD3:
  "\<lbrakk>ord R X; refl R X; distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  using distribD2 distributive_lattice_def by fastforce
 
lemma distr_latticeD4:
  "\<lbrakk>ord R X; refl R X; distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf R X {Sup R X {y, z}, x} = Sup R X {Inf R X {y, x}, Inf R X {z, x}}"
  by (simp add: distr_latticeD3 insert_commute)


lemma lattice_ne_inf_le_sup:
  "\<lbrakk>trans R X; A \<subseteq> X; A \<noteq> {}; is_inf R X A i; is_sup R X A s\<rbrakk> \<Longrightarrow> (i, s) \<in> R"
  by (meson converse_iff equals0I in_mono is_supD1121 is_supE1 trans_on_def)

lemma lattice_in_inf_le_sup:
  "\<lbrakk>trans R X; A \<subseteq> X; B \<subseteq> X; A \<inter> B \<noteq> {}; is_inf R X A i; is_sup R X B s\<rbrakk> \<Longrightarrow> (i, s)\<in>R"
proof-
  assume A0:"trans R X" "A \<subseteq> X" "B \<subseteq> X" "A \<inter> B \<noteq> {}" "is_inf R X A i"  "is_sup R X B s"
  obtain x where B0:"x \<in> A \<inter> B"   using A0(4) by blast
  obtain B1:"x \<in> X"using A0(2) B0 by blast
  then obtain B2:"(i, x)\<in>R" and B3:"(x,s)\<in>R"  using A0(5) A0(6) B0 is_supD1121 by fastforce
  then show "(i,s)\<in>R" by (meson A0(1) A0(5) A0(6) B1 is_supE1 trans_onD)
qed

lemma lattice_id0:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> lb R {Sup R X {x, y}, Sup R X {y, z}, Sup R X {x, z}} (Inf R X {x, y})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD32 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)

lemma lattice_id1:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  lb R {Sup R X {x, y}, Sup R X {y, z}, Sup R X {x, z}} (Inf R X {y, z})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD31 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD32 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD32 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  

lemma lattice_id2:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> lb R {Sup R X {x, y}, Sup R X {y, z}, Sup R X {x, z}} ( Inf R X {x, z})"
  using lattice_id0[of X R x z y]  by (simp add: insert_commute)

lemma lattice_id3:
  "\<lbrakk>ord R X;is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> ub R {Inf R X {x, y}, Inf R X {y, z}, Inf R X {x, z}} (Sup R X {x, y})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD31 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)

lemma lattice_id4:
  "\<lbrakk>ord R X;is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  ub R {Inf R X {x, y}, Inf R X {y, z}, Inf R X {x, z}} (Sup R X {y, z})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD32 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD32 bsup_geI2 converseD is_supE1 lattD31 lattD42)


lemma lattice_id5:
  "\<lbrakk>ord R X;is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  ub R {Inf R X {x, y}, Inf R X {y, z}, Inf R X {x, z}} (Sup R X {x, z})"
  using lattice_id3[of X R x z y] by (simp add: insert_commute)
lemma distr_latticeD5:
  "distributive_lattice R X \<Longrightarrow> is_lattice R X" 
  by (simp add: distributive_lattice_def)

lemma distrib_I3:
  "\<lbrakk>ord R X;distributive_lattice R X;refl R X;x\<in>X;y\<in>X;z\<in>X ;Inf R X {x, z} = Inf R X {y, z}; Sup R X {x, z}=Sup R X {y, z}\<rbrakk> \<Longrightarrow> x=y"
proof-
  assume A0:"ord R X" "distributive_lattice R X" "refl R X" "x\<in>X" "y\<in>X"  "z\<in>X"  " Inf R X {x, z} = Inf R X {y, z}" " Sup R X {x, z}=Sup R X {y, z}"
  obtain A1:"is_lattice R X" and A2:"(x,x)\<in>R"  by (metis A0(2) A0(3) A0(4) distr_latticeD5 reflE1) 
  then have B0:"x = Inf R X {x, Sup R X {x, z}}" using A1 A0(1,3,4,6) lattice_absorb2[of X R x z] by simp
  also have B1:"... = Inf R X {x, Sup R X {y, z}}"  by (simp add: A0(8))
  also have B2:"... = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" using A0(1-6) distr_latticeD3[of X R x y z] by fastforce
  also have B3:"... = Sup R X {Inf R X {y, x}, Inf R X {y, z}}"   by (simp add: A0(7) insert_commute) 
  also have B4:"... = Inf R X {y, Sup R X {x, z}}"   by (simp add: A0(1-6) distr_latticeD3)
  also have B5:"... = Inf R X {y, Sup R X {y, z}}"   by (simp add: A0(8))
  also have B6:"... = y"   by (meson A0(1) A0(3) A0(5) A0(6) A1 lattice_absorb2 refl_def)
  then show "x=y"   by (simp add: calculation)
qed

subsection CompleteLattices

lemma csupD2:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X A x)"
  by (simp add: is_csup_semilattice_def)
lemma csupD4:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (metis csupD2 sup_equality)
lemma csupD50:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A) \<in> X"
  by (metis csupD4 is_supE1)

lemma csupD51:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> ub R A (Sup R X A)"
  by (meson csupD4 is_supE2)

lemma csupD52:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A) \<in> ubd R X A"
  by (simp add: csupD4 is_supD32) 
    
 lemma csupD61:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> ubd R X A \<Longrightarrow> (Sup R X A, b) \<in> R "
  by (meson csupD4 is_supD5 ubdD2 ubdD3)   

lemma csupD62:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> X \<Longrightarrow> ub R A b \<Longrightarrow>  (Sup R X A, b)\<in>R"
  by (simp add: csupD61 ubdI2)

lemma cinfD2:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (simp add: is_cinf_semilattice_def)

lemma clatD21:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X A x)"
  by (simp add: is_clattice_def)

lemma clatD22:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (meson clatD21 inf_if_sup_lb ubd_sub)

lemma clatD1:
  "is_clattice R X \<Longrightarrow> is_csup_semilattice R X"
  by (simp add: is_clattice_def is_csup_semilattice_def)

lemma clatD2:
  "is_clattice R X \<Longrightarrow> is_cinf_semilattice R X"
  by (metis inf_if_sup_lb is_cinf_semilattice_def is_clattice_def ubd_sub)

lemma csupD3:
  "is_csup_semilattice R X \<Longrightarrow> (\<exists>x. is_greatest R X x)"
  by (metis is_csup_semilattice_def order_refl sup_max_eq2)

lemma cinfD3:
  "is_cinf_semilattice R X \<Longrightarrow> (\<exists>x. is_least R X x)"
  by (metis dual_order.refl is_cinf_semilattice_def sup_max_eq2)

lemma cinfD4:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf R X A (Inf R X A)"
  by (metis antisym_on_converse cinfD2 is_sup_unique the1I2)

lemma clatD41:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (simp add: clatD21 sup_exI)

lemma cinfD50:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf R X A) \<in> X"
  by (meson cinfD4 is_supE1)

lemma cinfD51:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> lb R A (Inf R X A)"
  by (meson cinfD4 is_supE2)

lemma cinfD52:
  "\<lbrakk>ord R X; is_cinf_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf R X A) \<in> lbd R X A"
  by (simp add: cinfD4 is_supD32) 
    
lemma cinfD61:
  "\<lbrakk>ord R X; is_cinf_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> lbd R X A \<Longrightarrow> (b, Inf R X A) \<in> R "
  by (metis cinfD4 converseD is_supE3)

lemma cinfD62:
  "\<lbrakk>ord R X; is_cinf_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> X \<Longrightarrow> lb R A b \<Longrightarrow>  (b,Inf R X A)\<in>R"
  by (simp add: cinfD61 ubdI2)

lemma csup_inf:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; lbd R X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (meson ubd_sub csupD2 inf_if_sup_lb)

lemma cinf_sup:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; ubd R  X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X A x)"
  by (meson cinfD2 sup_if_inf_ub ubd_sub)
lemma csup_fsup:
  "is_csup_semilattice R X \<Longrightarrow> is_sup_semilattice R X"
  by (simp add: is_csup_semilattice_def is_sup_semilattice_def)

lemma cinf_sinf:
  "is_cinf_semilattice R X \<Longrightarrow> is_inf_semilattice R X"
  by (simp add: is_cinf_semilattice_def is_sup_semilattice_def)

lemma clatD31:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup R X A \<in> X"
  by (simp add: clatD1 csupD50)

lemma clatD32:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf R X A \<in> X"
  by (simp add: clatD2 cinfD50)
lemma clat_lattice:
  "is_clattice R X \<Longrightarrow> is_lattice R X"
  using cinf_sinf clatD1 clatD2 csup_fsup is_lattice_def ssupD2 by fastforce

lemma sup_iso1b:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis csupD4 dual_order.trans is_sup_iso1 ne_subset_ne)

lemma sup_iso1:
  "\<lbrakk>ord R X;is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis clatD21 dual_order.trans is_sup_iso1 sup_equality)

lemma sup_iso2:
  "\<lbrakk>ord R X;is_clattice R X; is_clattice R Y;A \<subseteq> Y; Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R Y A)\<in>R"
  by (smt (verit, ccfv_SIG) antisym_on_subset clatD21 is_sup_iso2 subset_trans sup_equality trans_on_subset)

lemma inf_anti1:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Inf R X B, Inf R X A)\<in>R"
  by (smt (verit, ccfv_SIG) antisym_on_converse clatD22 converseD is_sup_iso1 is_sup_unique subset_trans the_equality)

lemma pow_is_clattice2:
  "is_inf (pwr X) (Pow X) {} X"
  by (metis Union_Pow_eq empty_subsetI inf_if_sup_lb powrel5 subset_Pow_Union ubd_empty)

lemma pow_is_clattice:
  "is_clattice (pwr X) (Pow X)"
  by (meson Pow_not_empty is_clattice_def powrel5)

section Functions
subsection Isotonicity

lemma isotoneI1:
  "(\<And>x1 x2. x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, x2) \<in> Rx \<Longrightarrow> (f x1, f x2) \<in> Ry) \<Longrightarrow> isotone Rx X Ry f" 
  by (simp add: isotone_def)

lemma isotoneD1:
  "isotone Rx X Ry f \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, x2) \<in> Rx \<Longrightarrow> (f x1, f x2) \<in> Ry" 
  by (simp add: isotone_def)

lemma isotoneD2:
  "isotone Rx X Ry f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> isotone Rx A Ry f"  
  by (simp add: isotone_def subset_iff) 

lemma isotone_emp:
  "isotone Rx {} Ry f"
   by(blast intro:isotoneI1)

lemma isotoneD31: 
  "\<lbrakk>isotone R X Ry f; ub R A b; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> ub Ry (f`A) (f b)" 
   by (simp add: isotone_def subsetD ubE ub_imageI)

lemma isotoneD32: 
  "\<lbrakk>isotone R X Ry f; lb R A b; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> lb Ry (f`A) (f b)"
  by (meson converse.cases converseI isotoneD1 subsetD ubE ub_imageI) 


lemma isotoneD41: 
   "\<lbrakk>isotone R X Ry f; b \<in>ubd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> ubd Ry (f`X) (f`A)"
   by (simp add: isotoneD31 ubd_mem_iff)

lemma isotoneD42: 
   "\<lbrakk>isotone R X Ry f; b \<in>lbd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> lbd Ry (f`X) (f`A)"
   by (simp add: isotoneD32 ubd_mem_iff)

lemma isotoneD51:
   "\<lbrakk>isotone R  X Ry f; is_greatest R A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_greatest Ry (f`A) (f x)"
    by (meson greatestD11 greatestD12 greatestI2 image_eqI isotoneD31 isotoneD2 order_refl) 

lemma isotoneD52:
   "\<lbrakk>isotone R  X Ry f; is_least R A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_least Ry (f`A) (f x)"
  by (meson is_greatest_def isotoneD2 isotoneD42 order_refl)

lemma isotoneD61:
  "\<lbrakk>isotone R  X Ry f; is_sup R X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> ub Ry (f`A) (f x)" 
  by (simp add: is_supE1 is_supE2 isotoneD31) 

lemma isotoneD62:
  "\<lbrakk>isotone R  X Ry f; is_inf R X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> lb Ry (f`A) (f x)"
  by (simp add: is_supE1 is_supE2 isotoneD32) 

subsection Extensivity

lemma extensiveI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (x, f x) \<in> R) \<Longrightarrow> extensive R X f" 
  by (simp add:extensive_def)

lemma extensiveD1:
  "extensive R X f \<Longrightarrow> x \<in> X \<Longrightarrow> (x, f x) \<in> R" 
  by (simp add:extensive_def)

lemma extensive_sub:
  "extensive R X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> extensive R A f" 
  by (simp add: extensive_def in_mono) 

lemma extensive_emp:
  "extensive R {} f"  
  by (simp add: extensive_def) 

lemma extensiveD2:
  "\<lbrakk>trans R X; (f`X) \<subseteq> X; extensive R X f; ub R (f`X) b; b \<in> X\<rbrakk> \<Longrightarrow> ub R X b"
proof(rule ubI)
  fix a assume A0:"trans R X " "f`X \<subseteq> X"  "extensive R X f" "ub R (f`X) b" "b \<in> X" "a\<in>X"
  then have "(a, f a)\<in>R"  by (simp add: extensiveD1)
  also have "(f a, b)\<in>R" by(meson A0 fbdE1)
  then show "(a,b)\<in>R" using A0(1) trans_onD[of X R a "f a" b]
    using A0(2) A0(5) A0(6) calculation by blast
qed
    
lemma extensiveD3:
  "\<lbrakk>trans R X;(f`X) \<subseteq> X;extensive R X f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (x,f y)\<in>R"
  using extensiveD1[of R X f y] trans_onD[of X R x y "f y"] by blast

lemma extensiveD4:
  "\<lbrakk>trans R X; extensive R X f; (f`X) \<subseteq> X; x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  (f x1, f x2)\<in>R\<rbrakk> \<Longrightarrow> (x1, (f x2))\<in>R"
  using extensiveD1[of R X f x1] trans_onD[of X R x1 "f x1" "f x2"] by blast

lemma extensive_ub:
  "trans R X \<Longrightarrow> extensive R X f \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> ubd R X (f ` A) \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> R"
proof-
  fix a assume A0:"trans R X" "extensive R X f" "f`X \<subseteq> X" "A \<subseteq> X" " b \<in> ubd R X (f ` A)" "a \<in> A"
    then have "(a, f a)\<in>R" by (metis extensiveD1 in_mono)  
    also have "(f a, b)\<in>R"  by (meson A0(5) A0(6) fbdE1 ubdD3) 
    then show "(a,b)\<in>R" using A0(1) trans_onD[of X R a "f a" b]
      by (metis A0(3) A0(4) A0(5) A0(6) calculation image_subset_iff in_mono ubdD2)
qed
  

lemma extensive_ub_imp0:
  "trans R X \<Longrightarrow> extensive R X f \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> ubd R (f ` X) (f ` A) \<Longrightarrow> ub R A b"
  apply(rule ubI)
  proof-
    fix a assume A0:"trans R X" "extensive R X f" "f`X \<subseteq> X" "A \<subseteq> X" " b \<in> ubd R (f ` X) (f ` A)" "a \<in> A"
    then have "(a, f a)\<in>R" by (metis extensiveD1 in_mono)  
    also have "(f a, b)\<in>R"  by (meson A0(5) A0(6) fbdE1 ubdD3) 
    then show "(a,b)\<in>R" using A0(1) trans_onD[of X R a "f a" b]
      by (metis A0(3) A0(4) A0(5) A0(6) calculation image_subset_iff in_mono ubdD2)
qed

lemma extensive_ub_imp:
  "\<lbrakk>trans R X; extensive R X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd R (f`X) (f`A) \<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  apply(rule ubdI2,simp add: extensive_ub_imp0)
  using ubd_mem_iff2 by fastforce

lemma extensive_ub_imp2:
  "\<lbrakk>trans R X;extensive R X f; (f`X \<subseteq> X); A \<subseteq> X; b \<in> ubd R X (f`A)\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  by(rule ubdI,simp add: extensive_ub,simp add: ubd_mem_iff2)

lemma is_iso_extD1:
  "\<lbrakk>isotone R X R f;  extensive R X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x))\<in>R"
  by (simp add: extensive_def image_subset_iff)

lemma is_iso_sup:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A x \<Longrightarrow> is_sup R (f`X) (f`A) y  \<Longrightarrow> (y, f x)\<in>R"
  by (simp add: is_supE1 is_supE4 isotoneD61)

lemma is_iso_inf:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf R A X x \<Longrightarrow> is_inf R (f`X) (f`A) y  \<Longrightarrow> (f x, y)\<in>R"
  by (meson converseD in_mono is_supE1 is_supE2 isotoneD32 order_refl ubE)
subsection Idempotency

lemma idempotentD1:
  "\<lbrakk>idempotent X f; x \<in> X \<rbrakk> \<Longrightarrow>  f (f x) = f x"
  by (simp add: idempotent_def)

lemma idempotentD3:
  "\<lbrakk>idempotent X f; y \<in> f`X \<rbrakk> \<Longrightarrow>  f y = y"
  by (auto simp add: idempotent_def)

lemma iso_idemD1:
  "\<lbrakk>(x,x)\<in>R;isotone R X R f; idempotent X f; x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x))\<in>R"
  by (simp add: idempotentD1 isotoneD1)

lemma iso_idemD2:
  "\<lbrakk>isotone R X R f; idempotent X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  (x1,f x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
   using idempotentD1[of X  f x2] isotoneD1[of R X R f x1 "f x2"] by presburger 
lemma iso_idemD3:
  "\<lbrakk>isotone R X R f; idempotent X f; f`X \<subseteq> X; x1 \<in> X;x2 \<in> X;   (x1,f x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
  by (simp add: image_subset_iff iso_idemD2)
lemma idemp_iff:
  "idempotent X f \<longleftrightarrow> (\<forall>x \<in> X. (f \<circ> f) x = f x)"
  using idempotent_def by auto
lemma idempotentI2:
  "\<lbrakk>antisym R X; extensive R X f; isotone R X R f;  f`X \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (f (f x), f x)\<in>R)\<rbrakk> \<Longrightarrow> idempotent X f"
  by (simp add: antisym_onD idempotent_def image_subset_iff is_iso_extD1)

lemma idempotent_isotoneD1:
  "\<lbrakk>idempotent X f; isotone R X R f;  f`X \<subseteq> X;  y \<in> f`X;  x \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (f x, y)\<in>R"
   using rev_subsetD[of "y" "f`X" "X"] isotoneD1[of R "X" R "f" "x" "y"] idempotentD3[of "X" "f" "y"] by simp

lemma isotoneI2:
  "\<lbrakk>refl R X; trans R X;extensive R X f; f`X \<subseteq> X; closure_cond R X f\<rbrakk> \<Longrightarrow> isotone R X R f"
  by (simp add: closure_cond_def extensiveD3 isotone_def)

lemma idempotentI3:
  "\<lbrakk>antisym R X;extensive R X f;  f`X \<subseteq> X; closure_cond R X f\<rbrakk> \<Longrightarrow> idempotent X f"
  by (simp add: antisym_onD closure_cond_def extensive_def idempotent_def image_subset_iff)

subsection Closures 

lemma closureI3:
  "\<lbrakk>trans R X; refl R X; antisym R X;extensive R X f; f`X \<subseteq> X;  closure_cond R X f\<rbrakk> \<Longrightarrow> closure R X f"
  by (simp add: closure_def idempotentI3 isotoneI2)
lemma closureD1:
  "\<lbrakk>closure R X f;  x \<in> X\<rbrakk> \<Longrightarrow> f x \<in> X"
  by (simp add: image_subset_iff closure_def)
lemma closureD2:
  "\<lbrakk>closure R X f;  y \<in> f`X\<rbrakk> \<Longrightarrow> y \<in> X"
  by(simp add: closure_def[of R X f] subsetD[of "f`X" X y])

lemma closureD3:
  "closure R X f \<Longrightarrow> closure_cond R X f"
  by(simp add:closure_cond_def[of R X f] closure_def[of R X f] iso_idemD3[of R X f])
lemma closureD4:
  "\<lbrakk>closure R X f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (f x,f y)\<in>R"
  by (simp add: closure_def isotone_def)

lemma closureD5:
  "\<lbrakk>closure R X f; x \<in> X\<rbrakk> \<Longrightarrow> (x,f x)\<in>R"
  by(simp add:closure_def extensive_def)

lemma closureD7:
  "\<lbrakk>closure R X f; x \<in> X;  y \<in> (f`X) ;  (x, y)\<in>R\<rbrakk> \<Longrightarrow> (f x, y)\<in>R"
  by (meson closure_def idempotent_isotoneD1)
lemma closureD8:
  "\<lbrakk>trans R X; closure R X f;  x \<in> X;  y \<in> (f`X) ;  (f x, y)\<in>R\<rbrakk> \<Longrightarrow>  (x, y)\<in>R"
  by (meson closureD1 closureD2 closureD5 trans_onD)
lemma closureD9:
  "\<lbrakk>closure R X f;  y \<in> f`X\<rbrakk>  \<Longrightarrow> (f y,y)\<in>R"
  by (metis closureD2 closureD5 closure_def idempotentD3)
lemma closureD10:
  "\<lbrakk>antisym R X;closure R X f;  x \<in> X;  (f x,x)\<in>R\<rbrakk> \<Longrightarrow> x = f x"
  by (simp add: antisym_onD closureD1 closureD5)

lemma closureD11:
  "\<lbrakk>antisym R X;closure R X f;  x \<in> X; (f x,x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> f `X"
  using closureD10 by fastforce 

lemma cl_sup_eq_sup_cl1:
  "\<lbrakk>closure R X f; is_sup R X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s) \<in> ubd R  (f`X) (f`A)"
  by (meson closure_def is_supD32 isotoneD41)

lemma cl_le_cl_iff_le:
  "\<lbrakk>closure R X f;  is_inf R X A i;  A \<subseteq> X\<rbrakk> \<Longrightarrow> (f i) \<in> lbd R (f`X) (f`A)"
  by (meson closure_def is_supD32 isotoneD42)

lemma cl_sup_eq_sup_cl2:
  "\<lbrakk>trans R X;closure R X f;  is_sup R X A s; b \<in> ubd R (f`X) (f`A); A \<subseteq> X\<rbrakk> \<Longrightarrow> (s, b)\<in>R"
  by (meson closure_def converse.cases extensive_ub_imp is_supD2 ubdD1)

lemma cl_sup_eq_sup_cl3:
  "\<lbrakk>trans R X;closure R X f; is_sup R X A s; b \<in> ubd R (f`X) (f`A);A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s, b)\<in>R"
  by (meson cl_sup_eq_sup_cl2 closureD7 is_supE1 ubd_mem_iff)

lemma cl_sup_eq_sup:
  "\<lbrakk>trans R X;closure R X f;  is_sup R X A s;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s)"
  by (simp add: cl_sup_eq_sup_cl1 cl_sup_eq_sup_cl3 is_supI5)

lemma cl_sup_ge_sup_cl11:
  "\<lbrakk>trans R X;closure R X f; is_sup R X A s1; is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> (s1, s2)\<in>R"
  by (meson extensive_ub_imp2 closure_def is_supD32 is_supE3)

lemma cl_sup_ge_sup_cl2:
  "\<lbrakk>trans R X;closure R X f;  is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq>  X\<rbrakk> \<Longrightarrow> (s2, f s1)\<in>R"
  by (meson closureD1 closure_def is_supE1 is_supE2 is_supE4 isotoneD31)

lemma cl_sup_ge_sup_cl3:
  "\<lbrakk>closure R X f;  is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s2, f s1)\<in>R"
  by (meson closureD1 closure_def is_supE1 is_supE4 iso_idemD3 isotoneD61)

lemma cl_sup_ge_sup_cl4:
  "\<lbrakk>trans R X;closure R X f; is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s1, f s2)\<in>R"
  by (simp add: cl_sup_ge_sup_cl11 closureD4 is_supE1)

lemma cl_sup_ge_sup_cl:
  "\<lbrakk>antisym R X;trans R X;closure R X f; is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2"
  by (simp add: antisym_on_def cl_sup_ge_sup_cl3 cl_sup_ge_sup_cl4 closureD1 is_supE1)

subsection ClosureRanges
lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R C {x}) c)) \<rbrakk> \<Longrightarrow> clr R X C"
  by (simp add:closure_range_def)
lemma clrD2:
  "clr R X C \<Longrightarrow> C \<subseteq> X"
  by (simp add:closure_range_def)

lemma clrD2b:
  "clr R X C \<Longrightarrow> x \<in> C \<Longrightarrow>x \<in> X"
  by(drule clrD2,simp add:subsetD)
lemma clrD3:
  "clr R X C \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R  C {x}) c))"
  by (simp add:closure_range_def)

lemma clrD4:
  "clr R X C \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R  C {x}) c)"
  by (simp add:closure_range_def)

lemma clrD5:
  "clr R X C \<Longrightarrow>  (\<And>x. x \<in> X  \<Longrightarrow> ((ubd R  C {x}) \<noteq> {}))"
  by (metis clrD3 greatest_exD0)
lemma clrD6:
  "clr R X C \<Longrightarrow>  x \<in> X \<Longrightarrow> (ubd R C {x}) \<noteq> {}"
  by (simp add: clrD5)

lemma clrD7:
  "clr R X C \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c \<in> C.  (x, c)\<in>R)"
  by (simp add: clrD6 upbd_neE3)

lemma is_clr_cofinal1:
  "clr R X C \<Longrightarrow> is_greatest R X m \<Longrightarrow> (\<exists>c \<in> C.  (m, c)\<in>R)"
  by (simp add: clrD7 greatestD11)

lemma is_clr_cofinal2:
  "antisym R X \<Longrightarrow> clr R X C \<Longrightarrow> is_greatest R X m \<Longrightarrow> c \<in> C \<Longrightarrow> (m, c)\<in>R \<Longrightarrow> m =c"
  by (simp add: antisym_onD clrD2b greatestD11 greatestD2)

lemma is_clr_cofinal:
  "antisym R X\<Longrightarrow>clr R X C \<Longrightarrow> is_greatest R X m \<Longrightarrow> m \<in> C"
  by (metis is_clr_cofinal1 is_clr_cofinal2)

definition cl_from_clr::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "cl_from_clr R C \<equiv> (\<lambda>x. Least R  (ubd R  C {x}))"

lemma clr_equality:
  "\<lbrakk>antisym R X; clr R X C;is_least R (ubd R  C {x}) c\<rbrakk> \<Longrightarrow> cl_from_clr R C x = c"
  by (metis Greatest_def Least_def antisym_on_converse antisym_on_subset cl_from_clr_def clrD2 greatest_equality2 ubd_sub)

lemma cl_range1:
  assumes A0:"antisym R X" and A1:"clr R X C" and A2:"x \<in> X" 
  shows "(cl_from_clr R C) x \<in> C"
proof-
  obtain c where A3:"is_least R (ubd R  C {x}) c"
    by (meson A1 A2 clrD4)
  then have "(cl_from_clr R C) x = c"
    by (meson A0 A1 clr_equality)
  also have "c \<in> C"
    by (meson A3 greatestD11 ubdD2)
  finally show "(cl_from_clr R C) x \<in> C" by simp
qed

lemma cl_range2:
  "antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> (cl_from_clr R C)`X \<subseteq> C"
  by (simp add: cl_range1 image_subset_iff)

lemma cl_range3:
  "refl R C \<Longrightarrow> antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr R C) x = x"
  by (simp add: clr_equality greatest_iff reflD1 ubdD1 ubd_singleton)

lemma cl_range31:
  "refl R X \<Longrightarrow> antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr R C) x = x"
  by (simp add: cl_range3 clrD2b refl_def)

lemma cl_range3b:
  "refl R C \<Longrightarrow> antisym R X \<Longrightarrow>clr R X C  \<Longrightarrow> c \<in> C \<Longrightarrow> (\<exists>x \<in> X.  (cl_from_clr R C) x = c)"
  by (meson cl_range3 clrD2b)

lemma cl_range4:
  "refl R C \<Longrightarrow> antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> (cl_from_clr R C)`C = C"
  by (simp add: cl_range3)
lemma cl_range5:
  "refl R C \<Longrightarrow> antisym R X  \<Longrightarrow> clr R X C \<Longrightarrow> x \<in> C  \<Longrightarrow> x \<in>  cl_from_clr R C ` X"
  by (metis cl_range3 clrD2b rev_image_eqI)

lemma clr_induced_closure_id:
  "\<lbrakk>refl R C; antisym R X ; clr R X C\<rbrakk>  \<Longrightarrow>  (cl_from_clr R C)`X = C"
   by (rule order_antisym, auto simp add: cl_range2 cl_range5)

lemma cl_ext1:
  "\<lbrakk>refl R C; antisym R X ;clr R X C\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> (x, (cl_from_clr R C) x)\<in>R"
  by (metis clrD4 clr_equality greatestD11 ubd_mem_singleE)

lemma cl_ext2:
  "\<lbrakk>refl R C; antisym R X ;clr R X C\<rbrakk>\<Longrightarrow> extensive R X (cl_from_clr R C)"
  by (simp add: cl_ext1 extensive_def)

lemma cl_lt_ub1:
  "\<lbrakk>refl R C; antisym R X; clr R X C; x \<in> X; c \<in> ubd R C {x}\<rbrakk> \<Longrightarrow> ((cl_from_clr R C) x, c)\<in>R"
  by (metis clrD3 clr_equality is_supE3 is_supI1)

lemma cl_lt_ub2:
  "\<lbrakk>refl R C; antisym R X; clr R X C; x \<in> X; c \<in> C; (x,c)\<in>R\<rbrakk> \<Longrightarrow> ((cl_from_clr R C) x, c)\<in>R"
  by (simp add: ubd_singleton2 cl_lt_ub1)

lemma cl_iso1:
  "\<lbrakk>refl R C; antisym R X;trans R X;clr R X C; x \<in> X;y \<in> X; (x, y)\<in>R\<rbrakk>\<Longrightarrow> ((cl_from_clr R C) x, (cl_from_clr R C) y)\<in>R"
  by (simp add: cl_ext2 cl_lt_ub2 cl_range1 clrD2 clr_induced_closure_id extensiveD3)

lemma cl_iso2:
  "\<lbrakk>refl R C; antisym R X;trans R X;clr R X C\<rbrakk> \<Longrightarrow> isotone R X R (cl_from_clr R C)"
  by (simp add: cl_iso1 isotone_def)

lemma cl_ide:
  "\<lbrakk>refl R C; antisym R X;clr R X C\<rbrakk> \<Longrightarrow> idempotent X (cl_from_clr R C) "
  by (simp add: cl_range1 cl_range3 idempotent_def)

lemma cl_is_closure:
  "\<lbrakk>refl R C; antisym R X;trans R X;clr R X C\<rbrakk> \<Longrightarrow> closure R X (cl_from_clr R C)"
  by(simp add:closure_def cl_ext2 cl_ide cl_iso2 clr_induced_closure_id clrD2)

lemma closure_of_in_ub:
  "closure R X f \<Longrightarrow>x \<in> X \<Longrightarrow> (f x) \<in> (ubd R  (f`X) {x})"
  by (simp add: ubd_singleton2 closureD5)

lemma closure_of_lt_ub:
  "closure R X f \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in>  (ubd R (f`X) {x}) \<Longrightarrow> ((f x), y)\<in>R"
  by (simp add: closureD7 ubd_singleton_iff)

lemma closure_of_least_closed1:
  "closure R X f \<Longrightarrow> x \<in> X \<Longrightarrow> is_least R (ubd R  (f`X) {x}) (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub greatestI3)

lemma closure_of_least_closed2:
  assumes A0:"antisym R X"  and A1:"closure R X f" and A2:"x \<in> X"
 shows "Least R (ubd R  (f`X) {x}) =  (f x)"
proof-
  obtain B0:"antisym R (f`X)"  by (meson A0 A1 antisym_on_subset closure_def)
  have B1:"is_least R (ubd R  (f`X) {x}) (f x)"  by (simp add: A1 A2 closure_of_least_closed1)
  then show "Least R (ubd R  (f`X) {x}) =  (f x)"
    by (metis B0 Posets17.Greatest_def Posets17.Least_def antisym_on_converse antisym_on_subset greatest_equality2 ubd_sub)
qed

lemma closure_induced_clr:
  "\<lbrakk>antisym R X; closure R X f; X \<noteq> {}\<rbrakk> \<Longrightarrow> clr R X (f`X)"
  by (meson closure_def closure_of_least_closed1 clrI1 image_is_empty)

lemma closure_induced_clr_id:
  "\<lbrakk>antisym R X; closure R X f; X \<noteq> {};x\<in>X\<rbrakk>  \<Longrightarrow> (cl_from_clr R (f`X)) x = f x"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

lemma closure_induced_clr_dual:
  "\<lbrakk>antisym R X; closure R X f1; closure R X f2; (\<And>x. x \<in> X \<Longrightarrow> (f1 x,f2 x)\<in>R)\<rbrakk> \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (metis closureD11 closureD2 idempotentD3 closure_def subsetI)
                    
lemma clr_induced_closure_dual:
  "\<lbrakk>refl R C; antisym R X;clr R X C1; clr R X C2; C2 \<subseteq> C1; x \<in> X\<rbrakk> \<Longrightarrow> (((cl_from_clr R C1) x),((cl_from_clr R C2) x))\<in>R"
  by (metis clrD4 clr_equality converseD greatest_iff ubd_iso2b)
lemma extensiveI4:
  "refl R X \<Longrightarrow> (\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> extensive R X f"
proof(rule extensiveI1)
  fix x assume A0:"refl R X" "(\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) " " f`X \<subseteq> X" "x \<in> X"
  have B0:"is_sup R X {x} x" by (metis A0(1) A0(4) reflE1 sup_singleton)
  have B1:"{x} \<subseteq> X"   by (simp add: A0(4))
  show "(x, f x) \<in> R"  using A0(2) B0 B1 by blast
qed
lemma idempotentI4:
  "\<lbrakk>refl R X; antisym R X; (\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup R X A s1 \<Longrightarrow> is_sup R X (f`A) s2 \<Longrightarrow> f s1 = f s2);  f`X \<subseteq> X\<rbrakk> \<Longrightarrow> idempotent X f"
  unfolding idempotent_def apply(auto)
proof-
  fix x assume A0:"refl R X" "antisym R X" "(\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup R X A s1 \<Longrightarrow> is_sup R X (f`A) s2 \<Longrightarrow> f s1 = f s2)" "f`X \<subseteq> X" "x \<in> X "
  have B0:"is_sup R X {x} x"   by (meson A0(1) A0(5) reflE1 sup_singleton)
  have B1:"is_sup R X (f`{x}) (f x)"   by (metis A0(1) A0(4) A0(5) image_empty image_insert image_subset_iff reflE1 sup_singleton)
  have B2:"{x} \<subseteq> X"  by (simp add: A0(5))
  show "f (f x) = f x"
    by (metis A0(3) B0 B1 B2)
qed


lemma isotoneI4:
  assumes A0:"(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s))" and A1:"f`X \<subseteq>X " and A2:"refl R X"
  shows "isotone R X R f"
proof- 
  have P:"\<And>x1 x2. \<lbrakk>x1 \<in> X;x2 \<in> X; (x1, x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
    proof-
      fix x1 x2 assume A2:"x1 \<in> X""x2 \<in> X" "(x1,x2)\<in>R"
      have B01:"is_sup R X {x1, x2} x2"   by (meson A2(1) A2(2) A2(3) assms(3) binary_supI1 reflD1)
      have B02:"is_sup R (f`X) (f`{x1, x2}) (f x2)"  by (meson A2 B01 assms(1) empty_subsetI insert_subset)
      show "(f x1, f x2)\<in>R"   using B02 is_supD1121 by fastforce
    qed
  show ?thesis
    by (simp add: P isotoneI1)
qed

lemma clrD8:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk> \<Longrightarrow> (cl_from_clr R C) i \<in> lbd R X A"
  by (smt (verit, ccfv_threshold) cl_lt_ub2 cl_range1 clrD2b converseD converseI is_supD1121 is_supE1 refl_def subsetD ubd_mem_iff3)
lemma clrD9:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk>  \<Longrightarrow> ((cl_from_clr R C) i,i)\<in>R"
  by (metis clrD8 converse.simps is_supE3)
lemma clrD10:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk>\<Longrightarrow> (cl_from_clr R C) i = i"
  by (meson antisym_on_def cl_ext2 cl_range1 clrD2b clrD9 extensiveD1 is_supE1 refl_def)
lemma clrD11:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk> \<Longrightarrow>  i \<in> C"
  by (metis cl_range1 clrD10 is_supE1)

lemma moore_clI1:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> x \<in> Pow X \<Longrightarrow> is_least (pwr X) (ubd (pwr X) C {x})  (X \<inter> (\<Inter>(ubd (pwr X) C {x}))) "
  by(auto simp add:closure_range_def is_greatest_def ubd_def  ub_def pwr_def)

lemma moore_clI2:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> clr (pwr X) (Pow X) C"
  by (metis empty_iff empty_subsetI closure_range_def moore_clI1)

lemma moore_clI3:
  "C \<subseteq> Pow X \<Longrightarrow> X \<in> C \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> E \<noteq> {} \<Longrightarrow> (\<Inter>E) \<in> C) \<Longrightarrow> clr (pwr X ) (Pow X) C"
  by (metis Inf_insert insert_not_empty insert_subsetI moore_clI2)

lemma clr_cinf_semilattice1:
  assumes A0:"clr R X C" and A1:"is_cinf_semilattice R X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows "\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R C A x \<and> is_inf R X A x)"
proof-
  let ?f="(cl_from_clr R C)"
  fix A assume P0:"A \<subseteq> C" and P1:"A \<noteq> {}"
  then have B0:"A \<subseteq> X"   using A0 clrD2 by blast
  then obtain m where B1:"is_inf R X A m"  by (meson A1 P1 is_cinf_semilattice_def)
  then have B2:"\<And>a. a \<in> A \<Longrightarrow> (?f m, a)\<in>R"
  proof-
    fix a assume P2:"a \<in> A" 
    then have B20:"a \<in> C" using P0 by auto
    have B21:"(m, a)\<in>R"   using B1 P2 is_supE2 ubE by fastforce
    then have B22:"(?f m, ?f a)\<in>R"  by (metis A0 A2 A3 B1 B20 P0 cl_range31 clrD10)
    also have B23:"?f a = a"  by (meson A0 A2 A3 B20 cl_range31)
    finally show "(?f m, a)\<in>R" by simp
  qed
  have B3:"?f m \<in> lbd R X A" by (simp add: A0 A2 A3 B1 P0 clrD8)
  have B4:"?f m \<in> lbd R C A"  by (metis A0 A2 A3 B1 P0 cl_range31 clrD11 is_supE2 ubdI2)
  have B5:"(?f m, m) \<in> R"  by (meson A0 A2 A3 B1 P0 clrD9)
  also have B5:"(m, ?f m)\<in> R"using A0 A2 A3 B1 P0 calculation clrD10 by fastforce
  then have B6:"?f m = m" by (metis A0 A2 A3 B1 P0 clrD10)
  have B7:"is_inf R C A m"  by (meson A0 A2 A3 B1 P0 closure_range_def clrD11 sup_in_subset)
  show "(\<exists>x. is_inf R C A x \<and> is_inf R X A x)"
    using B1 B7 by blast
qed

lemma clr_clattice1:
  assumes A0:"clr R X C" and A1:"is_clattice R X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows "\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"
proof-
  fix A assume A2:"A \<subseteq> C" then have B0:"A \<subseteq> X"   using A0 clrD2 by blast
  also have B1:"ubd R C A \<subseteq> X" by (meson A0 clrD2 dual_order.trans ubd_sub)
  then obtain x where B2:"is_inf R X (ubd R C A) x"  using A1 A4 assms(3) clatD22 by blast
  then have B1:"is_sup R C A x"   by (metis A0 A2 A3 assms(3) clrD11 clrD2 converse_converse inf_if_sup_lb sup_in_subset ubd_sub)
  then show "(\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"  using B2 by auto
qed



lemma clr_is_clattice:
  "\<lbrakk>clr R X C; is_clattice R X; antisym R X; trans R X; refl R X\<rbrakk> \<Longrightarrow> is_clattice R C"
  by (metis clr_clattice1 is_clattice_def closure_range_def)

lemma closure_range_is_clattice:
  "\<lbrakk>closure R X f; is_clattice R X; antisym R X; trans R X; refl R X\<rbrakk> \<Longrightarrow> is_clattice R (f`X)"
  using closure_induced_clr clr_is_clattice is_clattice_def by blast

section Subsets
subsection Directedness

lemma is_dirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X.  (a, c) \<in> R \<and>  (b, c) \<in> R)) \<Longrightarrow> is_dir X R"
  by (simp add: is_dir_def)

lemma is_dirE1:
  "is_dir X R \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. (a, c)\<in>R \<and> (b, c)\<in>R)"
  by (simp add: is_dir_def)

lemma is_dirD1:
  "is_dir X R \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. ub R {a,b} c)"
  by (simp add: is_dirE1 ub_double_iff1)

lemma is_dir_empty:
   "is_dir {} R"
  using is_dir_def by auto

lemma is_dir_singleton:
  "(x,x)\<in>R \<Longrightarrow> is_dir {x} R"
  by (metis is_dirI1 singletonD)

lemma is_dir_singleton2:
  "refl R X \<Longrightarrow> x \<in> X \<Longrightarrow> is_dir {x} R"
  by (simp add: is_dir_singleton reflD1)


lemma updir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. (a1,c)\<in>R \<and> (a2,c)\<in>R)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans R X" 
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> (a, c)\<in>R)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case  using A0 by auto
next
  case (insert x F) obtain c1 where P0:"c1 \<in> X" and P1:"(\<forall>a. a\<in>F\<longrightarrow>(a,c1)\<in>R)" using insert.hyps(4) insert.prems by blast
  then obtain c2 where P2:"c2\<in>X" and P3:"(c1, c2) \<in> R \<and> (x, c2) \<in> R"   by (meson A0 insert.prems insert_subset)
  then have P4:"\<And>a. a \<in> (insert x F)\<Longrightarrow>(a, c2) \<in> R"
  proof-
    fix a assume P5:"a\<in>(insert x F)"
    show "(a,c2)\<in>R"
    proof(cases "a=x")
      case True then show ?thesis   by (simp add: P3)
    next
      case False  then show ?thesis  by (meson A4 P0 P1 P2 P3 P5 in_mono insert.prems insertE trans_onD)
    qed
  qed
  then show ?case  using P2 by blast
qed
  
lemma updir_finite2:
  "\<lbrakk>is_dir X R;A \<subseteq> X;trans R X;finite A;A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c)"
  by (metis is_dir_def ubI updir_finite1)

lemma updir_finite_obtain:
  assumes "is_dir X R" and "A \<in> Fpow_ne X" and "trans R X"
  obtains c where "c \<in> X \<and> ub R A c"
  by (metis assms(1) assms(2) assms(3) fpow_ne_iff2 updir_finite2)

lemma updir_finite3:
  "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c)) \<Longrightarrow> is_dir X R"
proof(rule is_dirI1)
  fix a b assume A0:"(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c))" and A1:"a \<in> X" and A2:"b \<in> X"
  then obtain B0:"{a,b} \<subseteq> X" and B1:"finite {a,b}" and B2:"{a,b} \<noteq> {}" by blast
  then obtain c where B3:"c \<in> X" and B4:"ub R {a,b} c"  by (meson A0)
  then have B4:"(a, c) \<in> R \<and> (b, c) \<in> R"  by (simp add: ub_double_iff1)
  then show "\<exists>c\<in>X. (a, c) \<in> R \<and> (b, c) \<in> R"  using B3 by auto
qed

lemma is_dirI2:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>i. is_sup R X {a, b} s)) \<Longrightarrow> is_dir X R"
  by (metis binary_supD32 is_dir_def is_supE1)

lemma is_dirI4:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_sup_semilattice R X; A \<subseteq> X; (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (Sup R X {a, b} \<in> A))\<rbrakk> \<Longrightarrow> is_dir A R"
proof(rule is_dirI1)
  fix a b assume A0:"antisym R X" and A1:"refl R X" and A2:"trans R X" and A3:"is_sup_semilattice R X" and A4:"A \<subseteq> X" and
                 A5:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (Sup R X {a, b} \<in> A))"  and A6:"a \<in> A" and A7:"b \<in> A"
  let ?c="Sup R X {a,b}"
  have B0:"?c \<in> A \<and> (a,?c)\<in>R \<and> (b,?c)\<in>R"    by (meson A0 A1 A2 A3 A4 A5 A6 A7 bsup_geI1 bsup_geI2 reflE1 subset_eq)
  then show "\<exists>c::'a\<in>A. (a, c) \<in> R \<and> (b, c) \<in> R" by blast
qed
lemma is_dirI5:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_sup_semilattice R X; A \<subseteq> X; is_fsup_closed R X A\<rbrakk> \<Longrightarrow> is_dir A R"
  by (simp add: is_dirI4 is_fsup_closed_def)

subsection OrderClosure
lemma is_ord_clE1:
  "is_ord_cl X A R  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> (a, b)\<in>R \<Longrightarrow> b \<in> A "
   by (simp add:is_ord_cl_def)

lemma is_ord_clI1:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; (a,b)\<in>R\<rbrakk> \<Longrightarrow> b \<in> A ) \<Longrightarrow> is_ord_cl X A R"
  by (auto simp add:is_ord_cl_def)

lemma is_ord_empty:
  "is_ord_cl X {} R "
  by (simp add: is_ord_cl_def)
lemma is_ord_cl_space:
  "is_ord_cl X X R "
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_comp1:
  "is_ord_cl X A R \<Longrightarrow> is_ord_cl X (X-A) (converse R)"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_comp2:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl X (X-A) (converse R) \<Longrightarrow> is_ord_cl X A R"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_un:
  "A \<in> (Pow (Pow X)) \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> is_ord_cl X Ai R) \<Longrightarrow>  is_ord_cl X (\<Union>A) R "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_in:
  "A \<in> (Pow (Pow X)) \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> is_ord_cl X Ai R) \<Longrightarrow>  is_ord_cl X (\<Inter>A) R "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_un3:
  "(f`I)\<in> (Pow (Pow X)) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> is_ord_cl X (f i) R) \<Longrightarrow>  is_ord_cl X (\<Union>i \<in> I. f i) R "
  by (metis (mono_tags, lifting) f_inv_into_f inv_into_into is_ord_cl_un)

lemma is_ord_cl_in3:
  "(f`I)\<in> (Pow (Pow X)) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> is_ord_cl X (f i) R) \<Longrightarrow>  is_ord_cl X (\<Inter>i \<in> I. f i) R "
  by (metis (mono_tags, lifting) f_inv_into_f inv_into_into is_ord_cl_in)
lemma ord_cl_memI1:
  "is_ord_cl X A R \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a. a \<in> A \<and> (a,x)\<in>R) \<Longrightarrow> x \<in> A"
  by(auto simp add:is_ord_cl_def)

lemma ord_cl_dwdir_inf:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A (converse R)" and A2:"is_ord_cl X A R"
  shows "\<And>a b. \<lbrakk>a \<in> A; b \<in> A; is_inf R X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> A"
proof-
  fix a b assume A3:"a \<in>A" and A4:"b\<in>A" and A5:"is_inf R X {a, b} i"
  then obtain c where B0:"c \<in> A" and B1:"(c,a)\<in>R" and B2:"(c,b)\<in>R"   by (meson A1 converse.cases is_dirE1)
  then have B3:"c \<in> lbd R X {a, b}" by (meson A0 converse_iff in_mono ubd_mem_double)
  then have B4:"(c, i) \<in> R"   by (meson A5 converseD is_supE3)
  then have B5:"(i, c)\<in>(converse R)" by simp
  also have B6:"i\<in>X"  by (meson A5 is_supE1)
  then show "i\<in>A"  by (meson A2 B0 B4 is_ord_clE1)
qed

lemma ord_cl_updir_sup:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A R" and A2:"is_ord_cl X A (converse R)"
  shows "\<And>a b. \<lbrakk>a \<in> A; b \<in> A; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> s \<in> A"
  by (metis A0 A1 A2 converse_converse ord_cl_dwdir_inf)

lemma up_cl_bot:
  "\<lbrakk>is_least R X bot; A \<subseteq>X; is_ord_cl X A R; bot \<in> A\<rbrakk> \<Longrightarrow> A=X"
  by (meson converseD greatestD2 is_ord_cl_def subset_antisym subset_eq)

subsection Filters
subsection DefinitionAndBasicProps
lemma filterI1:
  "\<lbrakk> F \<noteq> {}; F \<subseteq> X; is_dir F (converse R);  is_ord_cl X F R\<rbrakk> \<Longrightarrow> is_filter R X F" 
  by (simp add: is_filter_def)

lemma idealI1:
  "\<lbrakk>F \<noteq> {}; F \<subseteq> X; is_dir F R;  is_ord_cl X F (converse R)\<rbrakk> \<Longrightarrow> is_ideal R X F" 
  by (simp add: is_filter_def)

lemma filterI2:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_inf_semilattice R X; F \<noteq> {}; F \<subseteq> X; is_finf_closed R X F; is_ord_cl X F R\<rbrakk> \<Longrightarrow> is_filter R X F" 
proof-
  assume A0:"antisym R X" and A1:"refl R X" and A2 :"trans R X" and A3:"is_inf_semilattice R X" and
         A4:"F \<noteq> {}" and A5:"F \<subseteq> X" and A6:"is_finf_closed R X F" and A7:"is_ord_cl X F R"
  then obtain B0:"antisym (converse R) X" and B1:"refl (converse R) X" and B2:"trans (converse R) X" and
              B3:"is_sup_semilattice (converse R) X" and B4:"is_fsup_closed (converse R) X F"  by (simp add: is_fsup_closed_def is_sup_semilattice_def refl_def)
  then have B5:"is_dir F (converse R)" using is_dirI5[of X "(converse R)" F] using A5 by blast
  show "is_filter R X F"
    by (simp add: A4 A5 A7 B5 filterI1)
qed

lemma idealI2:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_sup_semilattice R X; F \<noteq> {}; F \<subseteq> X; is_fsup_closed R X F; is_ord_cl X F (converse R)\<rbrakk> \<Longrightarrow> is_ideal R X F"
  by (simp add: idealI1 is_dirI5) 
        
lemma filterD1: 
  "is_filter R X F \<Longrightarrow> F \<noteq> {}" 
  by (simp add: is_filter_def)
lemma filterD2:
  "is_filter R X F \<Longrightarrow> F \<subseteq> X" 
  by (simp add: is_filter_def)
lemma filterD21:
  "is_filter R X F \<Longrightarrow> x \<in> F \<Longrightarrow> x \<in> X" 
  using filterD2 by blast
lemma filterD3: 
  "is_filter R X F \<Longrightarrow> (is_dir F (converse R))"
  by (simp add: is_filter_def)
lemma filterD4:
  "is_filter R X F \<Longrightarrow> (is_ord_cl X F R)" 
  by (simp add: is_filter_def)
lemma filter_greatestD1:
  "is_greatest R X m \<Longrightarrow> is_filter R X F \<Longrightarrow>  (\<exists>f. f \<in> F \<and> (f, m)\<in>R)"
  by (metis is_filter_def ex_in_conv filterD21 greatestD2)

lemma filter_greatestD2:
  "is_greatest R X m \<Longrightarrow> is_filter R X F \<Longrightarrow>  m \<in> F"
  using filterD4 greatestD11 filter_greatestD1 is_ord_clE1 by fastforce

lemma filter_finf_closed: 
  "\<lbrakk>is_filter R X F; a \<in> F;  b \<in> F;  is_inf R X {a, b} i\<rbrakk>\<Longrightarrow> i \<in> F"
  by (meson is_filter_def ord_cl_dwdir_inf)

subsection FiniteInfClosure

lemma filter_finf_closed1:
  "\<lbrakk>antisym R X; is_inf_semilattice R X; is_filter R X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf R X {a, b} \<in> F"
  proof-
    assume A0:"antisym R X" and A1:"is_inf_semilattice R X" and A2:"is_filter R X F" and A3:"a\<in>F" and A4:"b\<in>F"
    obtain i where B0:"is_inf R X {a,b} i"  by (meson A1 A2 A3 A4 filterD21)
    have B1:"i \<in> F"
      by (meson A2 A3 A4 B0 filter_finf_closed)
    show "Inf R X {a, b} \<in> F"
      by (metis A0 B0 B1 antisym_on_converse sup_equality the_equality)
qed

lemma filter_finf_closed3:
  "\<lbrakk>antisym R X; trans R X; is_inf_semilattice R X; is_filter R X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf R X A \<in> F"
  by (simp add: is_filter_def filter_finf_closed1 finite_inf_closed2)

lemma filter_finf_closed4:
  "\<lbrakk>antisym R X; trans R X;is_inf_semilattice R X; is_filter R X F; A \<in> Fpow_ne F\<rbrakk> \<Longrightarrow> Inf R X A \<in> F"
  by (simp add: filter_finf_closed3 fpow_ne_iff2)

lemma min_filter1:
  "(top,top)\<in>R \<Longrightarrow> antisym R X \<Longrightarrow> is_greatest R X top \<Longrightarrow> is_filter R X {top}"
  by (simp add: is_filter_def antisym_onD greatest_iff is_dir_singleton is_ord_cl_def)

lemma min_filter1b:
  "refl R X \<Longrightarrow> antisym R X \<Longrightarrow> is_greatest R X top \<Longrightarrow> is_filter R X {top}"
  by (simp add: is_filter_def antisym_onD greatest_iff is_dir_singleton is_ord_cl_def)

lemma min_filter2:
  "\<lbrakk>is_greatest R X top; is_filter R X F\<rbrakk> \<Longrightarrow>{top} \<subseteq> F"
  by (simp add: filter_greatestD2)

lemma inf_dwdir:
  "\<lbrakk>is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_dir X (converse R)"
  by (metis binary_supD31 binary_supD32 is_dirI1 is_supE1)

lemma filters_max0:
  "is_inf_semilattice R X \<Longrightarrow> is_filter R X X"
  by (simp add: Posets17.is_filter_def inf_dwdir is_ord_cl_def)
lemma filters_max1:
  "is_cinf_semilattice R X \<Longrightarrow>is_filter R X X"
  by (simp add: cinf_sinf filters_max0)
section SetOfFilters

lemma filters_on_iff:
  "F \<in> filters_on R X \<longleftrightarrow> is_filter R X F"
  by (simp add: filters_on_def)

lemma filters_is_clr1:
  "(filters_on R X) \<subseteq> Pow X"
  using filterD2 filters_on_iff by fastforce

lemma filters_is_clr1b:
  "is_inf_semilattice R X \<Longrightarrow> X \<in> filters_on R X"
  by (simp add: filters_max0 filters_on_iff)

lemma filter_inter_upcl:
  "(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F) \<Longrightarrow> is_ord_cl X (\<Inter>EF) R"
  by (meson Inter_iff filterD4 is_ord_cl_def)

lemma filter_pow_memD:
  "EF \<in> Pow(filters_on R X) \<Longrightarrow> (\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F)"
  using filters_on_iff by auto 

lemma is_pfilterD1: 
  "is_pfilter R X A \<Longrightarrow> is_filter R X A" 
  by(simp add:is_pfilter_def)

lemma is_pfilterD2:
  "is_pfilter R X A \<Longrightarrow>  X \<noteq> A"
  by(simp add:is_pfilter_def)

lemma is_pfilterD3:
  "is_pfilter R X A \<Longrightarrow>  A \<subseteq> X"
  using filterD2 is_pfilter_def by blast

lemma is_pfilterD4:
  "\<lbrakk>is_least R X bot; is_pfilter R X A\<rbrakk> \<Longrightarrow> bot \<notin> A"
  by (metis filterD4 is_pfilterD3 is_pfilter_def up_cl_bot)

lemma is_pfilterI1:
  "\<lbrakk>is_filter R X A; X \<noteq> A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by(simp add:is_pfilter_def)

lemma is_pfilterI2:
  "\<lbrakk>is_least R X bot; bot \<notin> A; is_filter R X A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by (metis greatestD11 is_pfilterI1)

lemma pfilters_memD0:
  "F \<in> pfilters_on R X \<Longrightarrow> is_pfilter R X F"
  by (simp add:pfilters_on_def)

lemma pfilters_memD1:
  "F \<in> pfilters_on R X \<Longrightarrow> is_filter R X F"
  by (simp add:pfilters_on_def is_pfilterD1)

lemma pfilters_memD2:
  "F \<in> pfilters_on R X \<Longrightarrow> F \<noteq> X"
  using is_pfilterD2 pfilters_memD0 by blast

lemma pfilters_memD3:
  "F \<in> pfilters_on R X  \<Longrightarrow> F \<subseteq> X"
  by (simp add:pfilters_on_def is_pfilterD3)

lemma pfilters_memI:
  "is_pfilter R X F \<Longrightarrow> F \<in> pfilters_on R X"
  by (simp add: pfilters_on_def)

lemma maximal_pfiltersD1:
  "is_maximal (pwr X) (pfilters_on R X) F \<Longrightarrow> H \<in> pfilters_on R X \<Longrightarrow> F \<subseteq> H \<Longrightarrow> F=H  "
  by (metis maximalD3 pfilters_memD3 pwr_mem_iff)

lemma maximal_pfiltersI1:
  "\<lbrakk>F \<in> pfilters_on R X; (\<And>H. \<lbrakk>H  \<in> pfilters_on R X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F =H)\<rbrakk> \<Longrightarrow>  is_maximal (pwr X) (pfilters_on R X) F "
  by (metis maximalI1 pwr_mem_iff)

lemma maximal_pfiltersI2:
  "\<lbrakk>F \<in> pfilters_on R X; (\<And>H. \<lbrakk>H  \<in> pfilters_on R X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F \<supseteq> H)\<rbrakk> \<Longrightarrow>  is_maximal (pwr X) (pfilters_on R X) F "
  by (metis maximal_pfiltersI1 subset_antisym)


subsection IntersectionOfFilters
subsubsection Upclosed

lemma filter_inter_upcl2:
  "EF \<in> Pow (filters_on R X) \<Longrightarrow> is_ord_cl X (\<Inter>EF) R"
  by (simp add: filter_inter_upcl filter_pow_memD)
subsubsection Nonempty

lemma filter_inter_ne:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F);is_greatest R X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (metis InterI empty_iff filter_greatestD2)

lemma filter_inter_ne2:
  "\<lbrakk>EF \<in> Pow (filters_on R X);is_greatest R X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (simp add: filter_inter_ne filters_on_iff subset_iff)

lemma filter_inter_sub1:
  "\<lbrakk>EF \<in> Pow_ne (filters_on R X); x \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> x \<in> X"
  by (metis Inter_iff ex_in_conv filterD2 filters_on_iff in_mono pow_ne_iff2)

lemma filter_inter_sub2:
  "\<lbrakk>EF \<in> Pow_ne (filters_on R X)\<rbrakk> \<Longrightarrow> \<Inter>EF \<subseteq> X"
  by (simp add: filter_inter_sub1 subset_iff)
subsubsection InfimaClosed

lemma filter_inter_double:
  "\<lbrakk>antisym R X; is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); x \<in> \<Inter>EF; y \<in> \<Inter>EF; F \<in> EF\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in> F "
  by (metis (full_types) InterD filter_finf_closed1 filter_pow_memD pow_ne_iff1)

lemma filter_inter_inf:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); x \<in> \<Inter>EF; y \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in> \<Inter>EF "
  by (simp add: filter_inter_double)

lemma filter_inter_dwdir3:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X)\<rbrakk> \<Longrightarrow>is_dir (\<Inter>EF) (converse R)"
proof-
  assume A0:"antisym R X" and A1:"is_inf_semilattice R X" and A2:"EF \<in> Pow_ne (filters_on R X)"
  have B0:"\<And>a b. \<lbrakk>a \<in> \<Inter> EF; b \<in> \<Inter> EF\<rbrakk> \<Longrightarrow> \<exists>c\<in>\<Inter> EF. (a, c) \<in> (converse R) \<and> (b, c) \<in>(converse R)"
  proof-
    fix a b assume P0:"a \<in> \<Inter> EF" and P1:"b \<in> \<Inter> EF"
    then obtain B01:"Inf R X {a,b} \<in> \<Inter>EF" and B02:"(a, Inf R X {a,b}) \<in> (converse R)" and B03:"(b, Inf R X {a,b}) \<in>(converse R)"
      by (metis A0 A1 A2 Sup_def antisym_on_converse binary_supD31 binary_supD32 filter_inter_inf filter_inter_sub1 is_sup_semilattice_def ssupD3)
    then show "\<exists>c\<in>\<Inter> EF. (a, c) \<in> (converse R) \<and> (b, c) \<in>(converse R)" by auto
  qed
  show "is_dir (\<Inter>EF) (converse R)"   using B0 is_dirI1 by blast
qed

lemma filter_inter_dir2:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_dir (\<Inter>{F1, F2}) (converse R)"
  by(erule filter_inter_dwdir3, simp,simp add: filters_on_iff pow_neI)

subsubsection ClosedUnderIntersection

lemma filter_inter_closed1:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); is_greatest R X top\<rbrakk> \<Longrightarrow>  is_filter R X (\<Inter>EF)"
  by (metis is_filter_def filter_inter_dwdir3 filter_inter_ne filter_inter_sub2 filter_inter_upcl filter_pow_memD pow_ne_iff1)

lemma filter_inter_closed2:
  "\<lbrakk>antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (\<And>E. \<lbrakk>E \<subseteq> (filters_on R X); E \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Inter>E) \<in> (filters_on R X))"
  by (simp add: filter_inter_closed1 filters_on_iff pow_neI)

subsection FilterMembership

lemma filter_memI:
  "\<lbrakk>is_filter R X F; x \<in> X\<rbrakk> \<Longrightarrow>y \<in> F \<Longrightarrow> (y, x)\<in>R \<Longrightarrow> x \<in> F"
  by (meson filterD4 is_ord_clE1) 
lemma filter_bsup_memI1: 
  "\<lbrakk>antisym R X; is_sup_semilattice R X; x \<in> F; is_filter R X F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F"
  by (meson binary_supD31 filterD21 filterD4 is_ord_clE1 ssupD3 ssupD4) 
lemma filter_bsup_memI2:
   "\<lbrakk>antisym R X; is_sup_semilattice R X; x \<in> F; is_filter R X F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {y, x} \<in> F" 
   by (simp add: filter_bsup_memI1 insert_commute)

lemma filter_ex_elem: 
  "\<lbrakk>is_filter R X F\<rbrakk> \<Longrightarrow> \<exists>f. f \<in> F" 
  by (simp add: ex_in_conv filterD1)

lemma filter_is_clr:
  "\<lbrakk>antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> clr (pwr X) (Pow X) (filters_on R X)"
  by (simp add: cinf_sinf filter_inter_closed2 filters_is_clr1 filters_is_clr1b moore_clI3)

lemma filter_closure_of_empty1:
  "\<lbrakk>(top,top)\<in>R; antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
proof-
  assume A0:"(top,top)\<in>R" and A1:"antisym R X" and A2:"is_inf_semilattice R X" and A3:"is_greatest R X top" and
         A4:"X \<noteq> {}"
  show " is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
  apply(rule greatestI3)
    apply (metis A3 converseI filter_greatestD2 filters_on_iff insert_subsetI pwr_mem_iff ubdD2 ubd_mem_singleE)
    by (metis A0 A1 A3 filters_is_clr1 filters_on_iff min_filter1 powsimp1 pwr_memI subset_insertI ubd_singleton_iff)
qed


lemma filter_closure_of_empty1b:
  "\<lbrakk>refl R X; antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
  by (simp add: filter_closure_of_empty1 greatestD11 greatestD2)

lemma filter_closure_of_empty2:
  "\<lbrakk>(top,top)\<in>R; antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (cl_from_clr (pwr X) (filters_on R X)) {} = {top}"
  by (metis clr_equality filter_closure_of_empty1 filter_is_clr powrel1)

lemma filter_closure_iff:
  "A \<noteq> {} \<Longrightarrow> x \<in> filter_closure R X A  \<longleftrightarrow> (x \<in> X \<and> ( \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R))"
  by (simp add: filter_closure_def)

lemma filter_closure_memI1:
  "(x \<in> X \<and> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R)) \<Longrightarrow> x \<in> filter_closure R X A"
  by (metis filter_closure_iff ne_subset_ne)

lemma filter_closure_memI2:
  "(x \<in> X \<and>  F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R) \<Longrightarrow> x \<in> filter_closure R X A"
  by (metis filter_closure_iff ne_subset_ne)

lemma filter_closure_memD1:
  "\<lbrakk>A \<noteq> {}; x \<in> filter_closure R X A\<rbrakk> \<Longrightarrow> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R)"
  by (simp add: filter_closure_iff)

lemma filter_closure_ne_simp:
  "A \<noteq> {} \<Longrightarrow> filter_closure R X A = {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and>(Inf R X F ,x)\<in>R}"
  by (simp add: filter_closure_def)

lemma filter_closure_singleton:
  "\<lbrakk>(a,a)\<in>R;antisym R X;A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> filter_closure R X A"
  apply(rule_tac ?F="{a}"  in filter_closure_memI2, simp)
  by (metis Sup_def antisym_on_converse converse_iff in_mono sup_equality sup_singleton)

lemma filter_closure_singletonb:
  "\<lbrakk>refl R X;antisym R X;A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> filter_closure R X A"
  by (simp add: filter_closure_singleton reflD1 subsetD)

lemma filter_closure_obtains:
  assumes "A \<noteq> {}" and "x \<in> filter_closure R X A"
  obtains Fx where "Fx \<subseteq> A \<and> finite Fx \<and> Fx \<noteq> {}  \<and> (Inf R X Fx, x)\<in>R"
  by (meson assms filter_closure_iff)

lemma filter_closure_empty:
  "antisym R X \<Longrightarrow> is_greatest R X top \<Longrightarrow> filter_closure R X {} = {top}"
  by (simp add: filter_closure_def greatest_equality2)

lemma filter_closure_ne:
  "\<lbrakk>antisym R X;refl R X;X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> filter_closure R X A \<noteq> {}"
  by (metis (no_types, lifting) empty_iff filter_closure_def filter_closure_singleton in_mono insert_not_empty ne_subset_ne reflD1 subset_emptyI)

lemma filter_closure_superset:
  "\<lbrakk>antisym R X;refl R X;X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure R X A"
  by (meson filter_closure_singleton in_mono reflD1 subsetI)

lemma ne_filter_cl1:
  "\<lbrakk>trans R X;antisym R X;refl R X;A \<subseteq> X; A \<noteq> {};is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure R X A) R"
proof-
  assume A0:"trans R X" and A1:"antisym R X" and A2:"refl R X" and A3:"A \<subseteq> X" and A4:"A \<noteq> {}" and A5:"is_inf_semilattice R X" 
  have B0:"\<And>a b. \<lbrakk>a \<in>  filter_closure R X A; b \<in> X; (a,b)\<in>R\<rbrakk> \<Longrightarrow> b \<in>  filter_closure R X A"
  proof-
    fix a b assume P0:"a \<in> filter_closure R X A" and P1:"b \<in> X" and P2:"(a,b)\<in>R"
    obtain F where B01:"F \<subseteq> A" and B02:"finite F" and B03:"F \<noteq> {}" and B04:"(Inf R X F,a)\<in>R"   by (meson A4 P0 filter_closure_memD1)
    also have B05:"Inf R X F \<in> X" by (meson A0 A1 A3 A5 B01 B02 B03 filter_finf_closed3 filters_max0 subset_trans)
    then have B06:"(Inf R X F, b) \<in>R"
      by (meson A0 A4 B04 P0 P1 P2 filter_closure_iff trans_onD)
    then have B01:"\<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  b) \<in> R"   using B01 B02 B03 by blast
    then show "b \<in>  filter_closure R X A"
      by (simp add: P1 filter_closure_memI1)
  qed
  show "is_ord_cl X (filter_closure R X A) R"  using B0 is_ord_clI1 by blast
qed


lemma filter_cl0:
  "\<lbrakk>refl R X;antisym R X;A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure R X A"
  by (simp add: filter_closure_singletonb subsetI)

lemma filter_cl1:
  "\<lbrakk>refl R X;antisym R X;trans R X;is_inf_semilattice R X; is_greatest R X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure R X A) R"
  by (metis filterD4 filter_closure_empty min_filter1b ne_filter_cl1)

lemma filter_cl_empty:
  "\<lbrakk>antisym R X;is_greatest R X top; (top,top)\<in>R\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X {}) (converse R)"
  by (simp add: filter_closure_empty is_dir_singleton)

lemma filter_cl_emptyb:
  "\<lbrakk>antisym R X;is_greatest R X top; refl R X\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X {}) (converse R)"
  by (simp add: filter_cl_empty greatest_iff)


lemma filter_cl2a:
  assumes csinf:"is_inf_semilattice R X" and 
          A0:"A \<subseteq> X" and
          A1:"A \<noteq> {}" and 
          A2:"antisym R X" and
          A3:"refl R X" and 
          A4:"trans R X"
  shows "is_dir (filter_closure R X A) (converse R)"
proof-
  have B0:"\<And>a b. \<lbrakk>a \<in> filter_closure R X A; b \<in> filter_closure R X A\<rbrakk> \<Longrightarrow> (\<exists>c\<in>filter_closure R X A. (c, a)\<in>R \<and> (c,b)\<in>R)"
  proof-
    fix a b assume P0:"a \<in> filter_closure R X A"  and P1:"b \<in> filter_closure R X A" then
    obtain Fa Fb where B01:"Fa \<subseteq> A" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R" and 
                       B05:"Fb \<subseteq> A" and B06:"finite Fb" and B07:"Fb \<noteq> {}" and B08:"(Inf R X Fb, b)\<in>R" 
    by (meson A1 assms(3) filter_closure_obtains)
    then obtain B01b:"Fa \<subseteq> X" and B015b:"Fb \<subseteq> X" using A0 by blast
    let ?Fab="Fa \<union> Fb"
    obtain B09:"?Fab \<subseteq> A" and B10:"finite ?Fab" and B11:"?Fab \<noteq> {}"   by (simp add: B01 B02 B03 B05 B06)
    then have B12:"?Fab \<subseteq> X"  using A0 by auto
    also have B13:"Inf R X (?Fab) \<in>  (filter_closure R X A)"   by (metis A2 A3 A4 B09 B10 B11 calculation csinf filter_closure_memI1 filter_finf_closed3 filters_max0 reflD1)
    obtain B14:"Fa \<subseteq> ?Fab" and B15:"Fb \<subseteq> ?Fab" by simp
    have B16:"is_inf R X Fa (Inf R X Fa)"
      by (metis A0 A2 A4 B01 B02 B03 Sup_def antisym_on_converse bsup_finite2 csinf is_sup_semilattice_def subset_trans trans_on_converse)
    have B17:"is_inf R X Fb (Inf R X Fb)"
      by (metis A2 A4 B015b B06 B07 Sup_def antisym_on_converse bsup_finite2 csinf is_sup_semilattice_def trans_on_converse)
    have B18:"(Inf R X ?Fab, Inf R X Fa)\<in>R"
      by (metis A2 A4 B10 B11 B12 B14 B16 Sup_def antisym_on_converse bsup_finite2 converseD csinf is_sup_iso1 is_sup_semilattice_def trans_on_converse) 
     have B19:"(Inf R X ?Fab, Inf R X Fb)\<in>R"
      by (metis A2 A4 B10 B11 B15 B17 Sup_def antisym_on_converse bsup_finite2 calculation converseD csinf is_sup_iso1 is_sup_semilattice_def trans_on_converse)
    have B20:"Inf R X ?Fab \<in> X"
      by (meson A1 B13 filter_closure_iff)
    then obtain B21:"(Inf R X ?Fab, a) \<in> R" and B22:"(Inf R X ?Fab, b)\<in>R" by (meson A4 B18 B19 B20 B04 B08  A1 B16 B17 P0 P1 filter_closure_iff is_supE1 trans_onD) 
    then show "(\<exists>c\<in>filter_closure R X A. (c,a)\<in>R \<and> (c, b)\<in>R)"   using B13 B21 B22 by blast
  qed
  show ?thesis by (simp add: B0 is_dirI1)
qed


lemma filter_cl2:
  assumes toped:"is_greatest R X top" and
          csinf:"is_inf_semilattice R X" and 
          A0:"A \<subseteq> X" and 
          A1:"antisym R X" and
          A2:"refl R X" and 
          A3:"trans R X"
  shows "is_dir (filter_closure R X A) (converse R)"
proof(cases "A={}")
  case True  then show ?thesis  by (meson A1 A2 filter_cl_emptyb toped)
next
  case False  then show ?thesis
    by (simp add: A0 A1 A2 A3 csinf filter_cl2a)
qed

lemma filter_cl_range:
  "\<lbrakk>antisym R X; refl R X; is_greatest R X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<subseteq> X"
  by (metis filterD2 filter_closure_empty filter_closure_iff min_filter1b subset_eq)

lemma filter_cl3a:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X A)"
  by (metis is_filter_def filter_cl2a filter_closure_iff filter_closure_ne ne_filter_cl1 subsetI)

lemma filter_cl3:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X A)"
  by (simp add: filterI1 filter_cl1 filter_cl2 filter_cl_range filter_closure_ne is_sup_semilattice_def)

lemma filter_cl_least1a:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; is_filter R X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure R X A)\<rbrakk> \<Longrightarrow> \<exists>Fx. Fx \<in> Fpow_ne A \<and> (Inf R X Fx, x)\<in>R \<and> Inf R X Fx \<in> F"
  by (smt (verit) filter_closure_iff filter_finf_closed3 fpow_ne_iff2 subset_trans)

lemma filter_cl_least1b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; is_filter R X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure R X A)\<rbrakk> \<Longrightarrow> x \<in> F"
  by (smt (verit, ccfv_SIG) filterD4 filter_cl_least1a filter_closure_iff is_ord_clE1)

lemma filter_cl_least1:
  assumes A0:"is_greatest R X top" and 
          A1:" is_inf_semilattice R X" and
          A2:"is_filter R X F" and
          A3:"A \<subseteq> F" and 
          A4:"x \<in>  (filter_closure R X A)" and
          A5:"antisym R X" and
          A6:"trans R X" and
          A7:"refl R X"
  shows " x \<in>F"
proof(cases "A={}")
  case True then show ?thesis
    using A0 A2 A4 A5 filter_closure_empty min_filter2 by fastforce
next
  case False  then show ?thesis by (meson A1 A2 A3 A4 A5 A6 A7 filter_cl_least1b) 
qed


lemma filter_cl_least2a:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; is_filter R X F; A \<subseteq> F; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<subseteq> F"
  using filter_cl_least1b by (metis subsetI) 

lemma filter_cl_least2:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_greatest R X top; is_inf_semilattice R X; is_filter R X F; A \<subseteq> F\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<subseteq> F"
  using filter_cl_least1 by (metis subsetI) 

lemma filter_cl_is_ub_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<in>  (ubd (pwr X) (filters_on R X) {A})"
  by (metis filterD2 filter_cl0 filter_cl3a filters_on_iff pwr_memI ubd_singleton_iff)
lemma filter_cl_is_ub:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<in>  (ubd (pwr X)  (filters_on R X) {A})"
  by (metis (no_types, lifting) filter_cl_is_ub_ne filter_closure_empty filter_closure_of_empty1b greatestD11)

lemma filter_cl_lt_ub_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> X; A \<noteq> {};F \<in>  (ubd (pwr X) (filters_on R X) {A})\<rbrakk> \<Longrightarrow> ((filter_closure R X A), F)\<in>(pwr X)"
  by (metis filter_cl_least1b filters_on_iff pwr_memD pwr_memI subsetI ubd_singleton_iff)
  
lemma filter_cl_lt_ub:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> F \<in>  (ubd (pwr X)  (filters_on R X) {A}) \<Longrightarrow> ((filter_closure R X A), F)\<in>(pwr X)"
  by (metis (no_types, opaque_lifting) filter_cl_lt_ub_ne filter_closure_empty filter_greatestD2 filters_on_iff insert_subsetI pwr_mem_iff ubd_singleton_iff)

lemma filter_cl_is_lub_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;A \<noteq> {}; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_inf (pwr X) (Pow X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A)"
  by (smt (verit, best) filter_cl_is_ub_ne filter_cl_lt_ub_ne filters_is_clr1 is_supD1 is_supI5 sup_maxE1 ubdD2 ubd_iso2b)

lemma filter_cl_is_lub:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_inf (pwr X) (Pow X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A) "
  by (metis (no_types, lifting) PowI filter_cl_is_lub_ne filter_cl_range filter_closure_empty filter_closure_of_empty1b sup_maxE1)
lemma filter_cl_is_lub_ne2:
  "\<lbrakk>antisym R X;trans R X; refl R X;A \<noteq> {}; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (pwr X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A)"
  by (metis filter_cl_is_lub_ne filter_cl_is_ub_ne sup_maxI1)
lemma filter_cl_is_lcl:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (pwr X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A) "
  by (metis filter_cl_is_lub filter_cl_is_ub sup_maxI1)

lemma filter_closure_eq_closure:                                      
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> filter_closure R X A = (cl_from_clr (pwr X) (filters_on R X)) A "
  by (metis clr_equality filter_cl_is_lcl filter_is_clr powrel1)


lemma filter_closure_of_filters1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> F \<in> A \<Longrightarrow> F \<subseteq> (filter_closure R X (\<Union>A))"
  by (metis Union_Pow_eq Union_mono Union_upper filter_cl0 filters_is_clr1 order.trans)

lemma filter_closure_of_filters2_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in>filters_on R X"
  by (metis all_not_in_conv cSup_least empty_Union_conv filterD1 filterD2 filter_cl3a filters_on_iff in_mono)

lemma filter_closure_of_filters2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X;is_greatest R X top\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in>filters_on R X"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1b)

lemma filter_closure_of_filters3_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in> ubd (pwr X) (filters_on R X) A"
  by (smt (verit, ccfv_SIG) filter_closure_of_filters1 filter_closure_of_filters2_ne filters_is_clr1 powsimp1 pwr_memI ubdI)

lemma filter_closure_of_filters3:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in>ubd (pwr X)  (filters_on R X) A"
  by (metis filter_closure_of_filters2 filter_closure_of_filters3_ne ubd_emptyI)

lemma filter_closure_of_filters4:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X;is_greatest R X top; G \<in> ubd (pwr X) (filters_on R X) A\<rbrakk> \<Longrightarrow> (filter_closure R X (\<Union>A)) \<subseteq> G"
  by (metis Sup_le_iff filter_cl_least2 filters_on_iff powrel8 ubd_mem_iff2)

lemma filter_closure_of_filters5:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) A (filter_closure R X (\<Union>A))"
  by (smt (verit, ccfv_SIG) filter_closure_of_filters3 filter_closure_of_filters4 filters_is_clr1 in_mono is_supI5 powsimp1 pwr_memI ubd_sub)

lemma filters_on_lattice_inf01:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2}"
  by (metis IntE bsup_idem1 filterD21 reflD1)

lemma pfilters_on_lattice_inf01:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2}"
  by (meson filters_on_lattice_inf01 is_pfilterD1)

lemma filters_on_lattice_inf02:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  by (simp add: filterD21 filter_bsup_memI1 filter_bsup_memI2 latt_iff)
  

lemma pfilters_on_lattice_inf02:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  by (meson filters_on_lattice_inf02 is_pfilterD1)

lemma filters_on_lattice_inf03:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup R X {f1, f2} \<in> F1 \<inter> F2 "
  by (meson filters_on_lattice_inf02)

lemma pfilters_on_lattice_inf03:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup R X {f1, f2} \<in> F1 \<inter> F2 "
  by (meson pfilters_on_lattice_inf02)

lemma filter_on_lattice_sup01: 
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F" 
   by (simp add: filter_bsup_memI2 lattD42)


lemma pfilter_on_lattice_sup01: 
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F "
  by (simp add: filter_on_lattice_sup01 is_pfilterD1)


lemma filter_on_lattice_top0:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X\<rbrakk> \<Longrightarrow> is_filter R X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> (a, x) \<in> R"
  by (meson filterD2 filter_on_lattice_sup01 lattD5 singleton_iff subset_iff)

lemma pfilter_on_lattice_top0:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X\<rbrakk> \<Longrightarrow> is_pfilter R X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> (a, x) \<in> R"
  by (simp add: filter_on_lattice_top0 is_pfilterD1)

lemma filter_on_lattice_top:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;  is_filter R X {x}\<rbrakk> \<Longrightarrow>  is_greatest R X x"
  by(rule greatestI1, rule ubdI, simp add: filter_on_lattice_top0, simp add:filterD21)

lemma pfilter_on_lattice_top:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;  is_pfilter R X {x}\<rbrakk> \<Longrightarrow>  is_greatest R X x"
  by (simp add: filter_on_lattice_top is_pfilterD1)

lemma filter_on_lattice_eq:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup R X {f1, f2})}"
  apply(auto simp add:set_eq_iff)
  apply (metis bsup_idem1 filterD21 reflD1)
  apply (simp add: filterD21 filter_bsup_memI1 lattD42)
  by (simp add: filterD21 filter_on_lattice_sup01)

lemma pfilter_on_lattice_eq:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup R X {f1, f2})}"
  by (simp add: filter_on_lattice_eq is_pfilterD1)

lemma filter_inter_dir3:
  assumes "antisym R X" "trans R X" "refl R X"  "is_inf_semilattice R X" "is_filter R X F1" "is_filter R X F2"
  shows "is_dir (F1 \<inter> F2) (converse R)"
  using assms filter_inter_dir2 by auto

lemma filters_on_lattice_inf2b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (converse R)"
  using filter_inter_dir3 lattD4 by blast

lemma pfilters_on_lattice_inf2b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (converse R)"
  by (simp add: filters_on_lattice_inf2b is_pfilterD1)

lemma filters_upcl:
  "\<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (R)"
  by (smt (verit, ccfv_threshold) Int_iff filter_memI is_ord_clI1) 

lemma pfilters_upcl:
  "\<lbrakk>is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (R)" 
  by (simp add: filters_upcl is_pfilterD1)

lemma filter_on_lattice_inf4b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (metis empty_iff equals0I filterD1 filters_on_lattice_inf02)

lemma pfilter_on_lattice_inf4b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (simp add: filter_on_lattice_inf4b is_pfilterD1)

lemma filters_on_lattice_inf5b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_filter R X (F1 \<inter> F2)"
  by (meson filterD2 filterI1 filter_on_lattice_inf4b filters_on_lattice_inf2b filters_upcl inf.coboundedI2) 

lemma pfilters_on_lattice_inf5b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> is_pfilter R X (F1 \<inter> F2)"
  by (metis Int_left_absorb filters_on_lattice_inf5b inf.orderE is_pfilterD3 is_pfilter_def)

lemma filters_on_lattice_inf6b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd (pwr X) (filters_on R X) {F1, F2})"
  by (simp add: filterD2 filters_on_iff filters_on_lattice_inf5b pwr_memI ubd_mem_double)

lemma pfilters_on_lattice_inf6b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd (pwr X) (pfilters_on R X) {F1, F2})"
  by (simp add: is_pfilterD3 pfilters_memI pfilters_on_lattice_inf5b pwr_mem_iff ubd_mem_double)

lemma filters_on_lattice_inf7b:
  "\<lbrakk>is_filter R X F1; is_filter R X F2; G \<in> (lbd (pwr X) (filters_on R X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: pwr_mem_iff ubd_mem_iff2)

lemma pfilters_on_lattice_inf7b:
  "\<lbrakk>is_pfilter R X F1; is_pfilter R X F2; G \<in> (lbd (pwr X) (pfilters_on R X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (metis Int_subset_iff converse_iff pwr_mem_iff ubd_mem_doubleE1 ubd_mem_doubleE2)

lemma filters_on_lattice_inf8b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;  is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow> is_inf (pwr X) (filters_on R X) {F1, F2} (F1 \<inter> F2)"
  by (smt (verit, ccfv_threshold) converseI filterD2 filters_on_lattice_inf6b filters_on_lattice_inf7b inf.absorb_iff2 inf.bounded_iff is_supI5 pwr_mem_iff)

lemma pfilters_on_lattice_inf8b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk>\<Longrightarrow> is_inf (pwr X) (pfilters_on R X) {F1, F2} (F1 \<inter> F2)"
  by (metis converseI is_pfilterD3 is_supI5 pfilters_on_lattice_inf5b pfilters_on_lattice_inf6b pfilters_on_lattice_inf7b pwr_mem_iff)
  

lemma filters_on_lattice_inf_semilattice1:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X\<rbrakk> \<Longrightarrow> is_inf_semilattice (pwr X) (filters_on R X)"
  by (metis empty_iff filters_is_clr1b filters_on_iff filters_on_lattice_inf8b lattD41)
  

lemma filters_on_lattice_sup1b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure R X (\<Union>EF)) R"
  by (metis Sup_least all_not_in_conv empty_Union_conv filterD1 filterD2 lattD41 ne_filter_cl1)

lemma filters_on_lattice_sup2a:
  assumes A01:"antisym R X" and A02:"trans R X" and A03:"refl R X" and 
          A0:"is_lattice R X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)" and A2:"EF \<noteq> {}" and
          A3: "a \<in> (filter_closure R X (\<Union>EF))" and  A4:"b \<in> (filter_closure R X (\<Union>EF))"
  shows "(\<exists>c \<in> (filter_closure R X (\<Union>EF)).  (c,a)\<in>R \<and>  (c, b)\<in>R)"
proof-
  let ?A="(\<Union>EF)"
    obtain Fa Fb where B01:"Fa \<subseteq> ?A" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R" and 
                       B05:"Fb \<subseteq> ?A" and B06:"finite Fb" and B07:"Fb \<noteq> {}" and B08:"(Inf R X Fb, b)\<in>R"
      by (metis A1 A2 A3 A4 Pow_empty filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD) 
    then obtain B01b:"Fa \<subseteq> X" and B015b:"Fb \<subseteq> X"  by (meson A1 Sup_least dual_order.trans filterD21 subsetI)
    let ?Fab="Fa \<union> Fb"
    obtain B09:"?Fab \<subseteq> ?A" and B10:"finite ?Fab" and B11:"?Fab \<noteq> {}"   by (simp add: B01 B02 B03 B05 B06)
    then have B12:"?Fab \<subseteq> X"   by (simp add: B015b B01b) 
    also have B13:"Inf R X (?Fab) \<in>  (filter_closure R X ?A)"       by (metis A0 A01 A02 A03 B09 B10 B11 calculation filter_closure_memI1 filter_finf_closed3 filters_max0 latt_iff reflD1) 
    obtain B14:"Fa \<subseteq> ?Fab" and B15:"Fb \<subseteq> ?Fab" by simp
    have B16:"is_inf R X Fa (Inf R X Fa)"
      by (metis A0 A01 A02 B01b B02 B03 Sup_def antisym_on_converse bsup_finite2 is_sup_semilattice_def latt_iff trans_on_converse)
    have B17:"is_inf R X Fb (Inf R X Fb)"
      by (metis A0 A01 A02 B015b B06 B07 Sup_def antisym_on_converse bsup_finite2 is_sup_semilattice_def latt_iff trans_on_converse)
    have B18:"(Inf R X ?Fab, Inf R X Fa)\<in>R"
      by (metis A0 A01 A02 B10 B11 B14 B16 Sup_def antisym_on_converse bsup_finite2 calculation converseD is_sup_iso1 is_sup_semilattice_def latt_iff trans_on_converse)
     have B19:"(Inf R X ?Fab, Inf R X Fb)\<in>R"
       by (metis A0 A01 A02 B10 B11 B15 B17 Sup_def antisym_on_converse bsup_finite2 calculation converseD is_sup_iso1 is_sup_semilattice_def latt_iff trans_on_converse)
    have B20:"Inf R X ?Fab \<in> X"
      by (metis B09 B11 B13 empty_subsetI equalityI filter_closure_iff)  
    then obtain B21:"(Inf R X ?Fab, a) \<in> R" and B22:"(Inf R X ?Fab, b)\<in>R"
      by (smt (verit, del_insts) A02 A3 A4 B01 B03 B04 B08 B16 B17 B18 B19 filter_closure_iff is_supE1 ne_subset_ne trans_onD)
  show ?thesis using B13 B21 B22 by blast 
qed


lemma filters_on_inf_lattice_sup2b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;is_greatest R X top;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X (\<Union>EF)) (converse R)"
  by (metis is_filter_def Sup_le_iff filter_cl2a filter_cl_emptyb)

lemma filters_on_inf_lattice_sup2c:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X (\<Union>EF)) (converse R)"
  by (simp add: is_filter_def cSup_least filter_cl2a)


lemma filters_on_lattice_sup2b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X (\<Union>EF)) (converse R)"
  by (simp add: filters_on_lattice_sup2a is_dirI1)

lemma filters_on_lattice_sup3b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> filter_closure R X (\<Union>EF) \<noteq> {}"
  by (metis filterD1 filter_closure_of_filters2_ne filters_on_iff latt_iff subsetI)

lemma filters_on_inf_lattice_sup3b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;is_greatest R X top; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)\<rbrakk> \<Longrightarrow> filter_closure R X (\<Union>EF) \<noteq> {}"
  by (meson Sup_le_iff filterD21 filter_closure_ne subset_iff)
  
lemma filters_on_lattice_sup4b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X (\<Union>EF))"
  by (simp add: is_filter_def filter_closure_iff filters_on_lattice_sup1b filters_on_lattice_sup2b filters_on_lattice_sup3b subset_iff)

lemma filters_on_inf_lattice_sup4b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;is_greatest R X top; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X (\<Union>EF))"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1b subsetI)

lemma filters_on_lattice_sup5b:
  "\<lbrakk>antisym R X;trans R X; refl R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}; F \<in> EF\<rbrakk> \<Longrightarrow>  F \<subseteq> (filter_closure R X (\<Union>EF))"
  by (meson Sup_le_iff filterD2 filter_cl0)

lemma filters_on_lattice_sup6b:
  assumes A01:"antisym R X" and A02:"trans R X" and A03:"refl R X" and 
          A0:"is_lattice R X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)" and A2:"EF \<noteq> {}" and
          A3:"is_filter R X G"  and A4:"(\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> G)"
  shows "filter_closure R X (\<Union>EF) \<subseteq> G"
proof
  fix x assume A5:"x \<in> filter_closure R X (\<Union>EF)"
  obtain Fx where  B1:"Fx \<subseteq>  (\<Union>EF) \<and> finite Fx \<and> Fx \<noteq> {} \<and> (Inf R X Fx,x)\<in>R"
    by (metis A5 Pow_empty A1 A2 filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD)
  have B2:"Fx \<subseteq> G"
    using B1(1) A4  by blast
  have B3:"Fx \<subseteq> X"
    using A3 B2 filterD2 by blast
  show "x \<in> G"
    by (metis A0 A01 A02 A03 A3 A5 B1 B2 filter_cl_least1b filter_closure_iff latt_iff ne_subset_ne subset_refl)
qed


lemma filters_on_lattice_sup7b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
  by (smt (verit, ccfv_SIG) Posets17.is_filter_def filter_closure_of_filters3_ne filters_on_iff filters_on_lattice_sup6b is_supI5 latt_iff pwr_mem_iff subsetI ubd_mem_iff2)

(*On a lattice filters form a complete sup semilattice*)

lemma filters_on_lattice_csup:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X\<rbrakk> \<Longrightarrow> is_csup_semilattice (pwr X) (filters_on R X)"
  by (metis empty_not_insert filters_is_clr1b filters_on_iff filters_on_lattice_sup7b insert_absorb insert_subset is_csup_semilattice_def lattD41)

lemma filters_on_lattice_sup_semilattice1b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) {F1, F2} (filter_closure R X (F1 \<union> F2))"
  by (metis Union_insert ccpo_Sup_singleton empty_not_insert filters_on_lattice_sup7b insertE singleton_iff)


lemma filters_on_top_inf_lattice_clattice:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (filters_on R X)"
  by (metis empty_iff filter_closure_of_filters5 filters_is_clr1b is_clattice_def)

lemma filters_clattice1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X; EF \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> is_sup  (pwr X) (filters_on R X) EF (Sup (pwr X) (filters_on R X) EF)"
  by (metis clatD21 filters_is_clr1 filters_on_top_inf_lattice_clattice powrel6 powrel7 sup_equality)

lemma filters_clattice2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X; EF \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> is_inf (pwr X) (filters_on R X) EF (Inf (pwr X) (filters_on R X) EF)"
  by (metis Sup_def antisym_on_converse antisym_on_subset clatD22 filters_is_clr1 filters_on_top_inf_lattice_clattice powrel1 powrel7 sup_equality)


lemma lattice_filter_memI:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F; x \<in> F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F"
  by (simp add: filter_bsup_memI1 lattD42)

lemma lattice_filter_dunion1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> \<Union>D \<noteq> {} "
  by (simp add: is_filter_def filters_on_iff subset_iff)

lemma lattice_filter_dunion2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_ord_cl X (\<Union>D) (R)"
  by (metis Pow_iff filterD2 filterD4 filters_on_iff is_ord_cl_un subset_iff)

lemma lattice_filter_dunion3:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> 
     \<Longrightarrow> (\<exists>Dx \<in> D. \<exists>Dy \<in> D. \<exists>Dxy \<in> D. x \<in> Dx \<and> y \<in> Dy \<and>(Dx,Dxy)\<in>pwr X \<and> (Dy, Dxy)\<in>pwr X)"
  by (simp add: is_dirE1) 


lemma lattice_filter_dunion4:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. x\<in> Dxy \<and> y \<in> Dxy)"
  proof-
    assume A0:"antisym R X" and A1:"trans R X" and A2:"refl R X" and A3:"is_lattice R X" and A4:"D \<noteq> {}" and 
          A5:"D \<subseteq> filters_on R X" and A6:" is_dir D (pwr X)" and A7:"x \<in> (\<Union>D) "and A8:"y \<in> (\<Union>D) "
    obtain Dx Dy Dxy where B0:"Dx \<in> D" and B1:"Dy \<in> D" and B2:"Dxy \<in> D" and B3:"x \<in> Dx" and B4:"y \<in> Dy" and B5:" (Dx, Dxy)\<in>pwr X" and B6: "(Dy, Dxy)\<in>pwr X"
      by (metis A6 A7 A8 UnionE is_dirE1) 
    then obtain B7:"Dx \<subseteq> Dxy" and B8:"Dy \<subseteq> Dxy"   by (simp add: pwr_mem_iff)
    then obtain B9:"Dxy \<in> D" and B10:"x \<in> Dxy" and B11:"y \<in> Dxy"  using B2 B3 B4 by blast
    then show "(\<exists>Dxy \<in> D. x\<in> Dxy \<and> y \<in> Dxy)"
      by auto
qed

lemma lattice_filter_dunion5:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. Inf R X {x, y} \<in> Dxy)"
  proof-
    assume A0:"antisym R X" and A1:"trans R X" and A2:"refl R X" and A3:"is_lattice R X" and A4:"D \<noteq> {}" and 
          A5:"D \<subseteq> filters_on R X" and A6:" is_dir D (pwr X)" and A7:"x \<in> (\<Union>D) "and A8:"y \<in> (\<Union>D) "
    obtain Dxy where B0:"Dxy \<in>D" and B1:"x \<in> Dxy" and B2:"y \<in> Dxy"    by (meson A0 A1 A2 A3 A4 A5 A6 A7 A8 lattice_filter_dunion4) 
    have B3:"is_filter R X Dxy"  using A5 B0 filters_on_iff by blast
    have B4:"Inf R X {x, y} \<in> Dxy"   using A0 A3 B1 B2 B3 filter_finf_closed1 latt_iff by fastforce
    then show ?thesis
      using B0 by blast
qed

lemma lattice_filter_dunion6:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in>  (\<Union>D)"
  by (simp add: lattice_filter_dunion5)

lemma lattice_filter_dunion7:
  "\<lbrakk>D \<noteq> {}; D \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> \<Union>D \<subseteq> X"
  by(auto simp add:filters_on_def is_filter_def)

lemma lattice_filter_dunion8:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_dir (\<Union>D) (converse R)"
  apply(rule_tac ?X="X" in  is_dirI4)
  apply simp
  apply (simp add: refl_def)
  apply simp
  apply (simp add: is_sup_semilattice_def latt_iff)
  apply (simp add: lattice_filter_dunion7)
  by (metis Sup_def lattice_filter_dunion6)

lemma lattice_filter_dunion9:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_filter R X (\<Union>D)"
  by (metis Posets17.is_filter_def lattice_filter_dunion1 lattice_filter_dunion2 lattice_filter_dunion7 lattice_filter_dunion8) 


lemma lattice_filters_complete:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X;  is_greatest R X top\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (filters_on R X)"
  by (simp add: filters_on_top_inf_lattice_clattice latt_iff)


lemma lorcI1:
  "y \<in> X \<Longrightarrow> (a, y)\<in>R \<Longrightarrow> y \<in> lorc R X a" 
  by (simp add:lorc_def)

lemma lorcD1:
  "y \<in> lorc R X a \<Longrightarrow> y \<in> X \<and> (a, y)\<in>R"
   by (simp add:lorc_def)

lemma lorcD11:
  "y \<in> lorc R X a \<Longrightarrow> y \<in> X "
   by (simp add:lorc_def)

lemma lorcD12:
  "y \<in> lorc R X a \<Longrightarrow> (a, y)\<in>R" 
  by (simp add:lorc_def)

lemma lorcD2:"trans R X \<Longrightarrow> a \<in> X \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in> lorc R X a \<Longrightarrow>  (y, x)\<in>R \<Longrightarrow> x \<in> lorc R X a"
  by (meson lorcD11 lorcD12 lorcI1 trans_onD)

lemma lorcD3:
  "a \<in> X \<Longrightarrow> trans R X \<Longrightarrow> (\<exists>b. (b,x)\<in>R \<and> b \<in> lorc R X a) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> lorc R X a"
  by (metis lorcD2)

lemma lorc_mem_iff1:
  "y \<in> (lorc R X a) \<longleftrightarrow> (y \<in> X \<and> (a, y)\<in>R)" 
  by (simp add:lorc_def)

lemma lorc_mem_iff2:
  "y \<in> (lorc R X a) \<longleftrightarrow> (y \<in> X \<and> ub R {a} y)" 
  by (simp add:lorc_def ub_def)

lemma lorc_eq_upbd:
  "(lorc R X a) = (ubd R  X {a})"
  by(simp add: set_eq_iff ubd_mem_iff lorc_mem_iff2)

lemma lorc_eq_upbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. lorc R X a) = ubd R  X A"
  by(auto simp add:ubd_mem_iff2 lorc_mem_iff1)

lemma lorc_memI1:
  "refl R X \<Longrightarrow> a \<in> X \<Longrightarrow> a \<in> lorc R X a "
  by (simp add: lorcI1 reflD1)

lemma lorc_subset1:
  "(lorc R X a) \<subseteq> X"
  by (simp add: ubd_sub lorc_eq_upbd)

lemma lorc_top:
  "is_greatest R X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> lorc R X a"
  by (simp add: greatestD11 greatestD2 lorcI1)

lemma lorc_sup_latticeD1:
  "\<lbrakk>antisym R X;trans R X;refl R X;is_sup_semilattice R X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, y} \<in> (lorc R X x)"
  by (simp add: binary_supD31 lorcI1 ssupD3 ssupD4)

lemma lorc_inf_latticeD1:
  "\<lbrakk>trans R X; refl R X; antisym R X;is_least R X bot\<rbrakk> \<Longrightarrow> (lorc R X bot) = X"
  by(auto simp add: lorc_mem_iff1 greatest_iff)

lemma lorc_dual_iso:
  "\<lbrakk>a \<in> X; b \<in> X;trans R X; refl R X; antisym R X\<rbrakk> \<Longrightarrow> (lorc R X a) \<subseteq> (lorc R X b)  \<longleftrightarrow> (b, a)\<in>R"
  by (smt (verit) in_mono lorcD11 lorcD12 lorcI1 lorc_memI1 subsetI trans_onD)

lemma lorc_upclI:
  "\<lbrakk>trans R X; refl R X; antisym R X;a \<in> X\<rbrakk> \<Longrightarrow> is_ord_cl X (lorc R X a) R"
  by (simp add: is_ord_clI1 lorcD2)

lemma lorc_upclD:
  "\<lbrakk>U \<subseteq> X; is_ord_cl X U R; is_least R U x\<rbrakk> \<Longrightarrow> U = lorc R X x"
  apply (auto simp add: in_mono greatestD2 lorcI1)
  apply (meson converse_iff greatestD2 in_mono lorcI1)
  by (meson is_ord_clE1 greatestD11 lorcD1)

lemma lorc_upcl1:
  "\<lbrakk>is_greatest R X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. lorc R X a)"
  by (simp add: greatestD11 greatestD2 in_mono lorcI1)

lemma lorc_upcl3:
  "\<lbrakk>trans R X; refl R X; antisym R X; is_greatest R X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. lorc R X a) R"
  apply(rule is_ord_cl_in)
  apply (simp add: image_subset_iff lorc_subset1)
  using lorc_upclI by fastforce

lemma compactI:
  "\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R))\<rbrakk> \<Longrightarrow> is_compact R X c"  
  by(simp add:is_compact_def)

lemma compactD:
  "\<lbrakk>is_compact R X c; A \<in> Pow_ne X; (c, Sup R X A) \<in> R\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R)"
   by(simp add:is_compact_def)

lemma compact_element_memD1:
  "x \<in> compact_elements R X  \<Longrightarrow> is_compact R X x" 
  by (simp add: compact_elements_def)
lemma compactD2:
  "is_compact R X x \<Longrightarrow> x \<in> X" 
  by (simp add: is_compact_def)
lemma compact_element_memD2:
  "x \<in> compact_elements R X  \<Longrightarrow> x \<in> X" 
  by (meson compactD2 compact_element_memD1) 
lemma compact_elements_sub:
  "compact_elements R X \<subseteq> X"  
  by (simp add: compact_element_memD2 subsetI) 
lemma compact_elements_mem_iff1:
   "x \<in> compact_elements R X \<longleftrightarrow> is_compact R X x" 
  by (simp add: compact_elements_def)
lemma compactly_generatedD1: 
  "compactly_generated R X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x)" 
   by(simp add:compactly_generated_def)

lemma compactly_generatedI1: 
  "(\<And>x. x \<in> X \<Longrightarrow>  (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x)) \<Longrightarrow> compactly_generated R X"  
  by(simp add:compactly_generated_def)


lemma join_denseD1:
  "\<lbrakk>join_dense R X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_sup R X Dx x)" 
  by (simp add:join_dense_def)
lemma meet_denseD1:"
  \<lbrakk>meet_dense R X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_inf R X Dx x)" by (simp add:join_dense_def)

lemma cjoin_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice R X; antisym R X\<rbrakk> \<Longrightarrow> (join_dense R X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Sup R X Dx))"
  by (metis Pow_mono is_clattice_def join_dense_def powsimp1 sup_equality) 

lemma cmeet_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice R X; antisym R X\<rbrakk> \<Longrightarrow> (meet_dense R X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Inf R X Dx))"
  by (metis Pow_mono Sup_def antisym_on_converse inf_if_sup_lb is_clattice_def join_dense_def powsimp1 sup_equality ubd_sub)

lemma join_denseD2:"\<lbrakk>antisym R X; join_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Sup R X (rolc R D x))"
proof-
  assume P:"antisym R X" "join_dense R X D" "D \<subseteq> X" 
  show "(\<And>x. x \<in> X \<Longrightarrow> x = Sup R X (rolc R D x))"
  proof- 
    fix x assume P1:"x \<in> X" 
    obtain Dx where P2:"Dx \<in> Pow D" "is_sup R X Dx x" by (meson P(2) P1 join_denseD1) 
    have B0:"\<forall>d. d \<in> Dx \<longrightarrow> (d, x) \<in> R"  by (meson P2(2) is_supD1121) 
    have B1:"Dx \<subseteq> X" using P(3) P2(1) by auto 
    have B2:"Dx \<subseteq> (rolc R D x)"  using B0 P2(1) lorc_def by fastforce 
    have B3:"is_sup R X (rolc R D x) x" 
      proof(rule is_supI5)
        show "\<And>a. a \<in> ubd R X (rolc R D x) \<Longrightarrow> (x, a) \<in> R"  by (meson B2 P2(2) is_supE3 ubd_ant1b)
        show " x \<in> ubd R X (rolc R D x)" by (metis (no_types, lifting) P1 converse.cases lorc_def mem_Collect_eq ubdI) 
      qed
    show "x= Sup R X (rolc R D x)"     by (metis B3 P(1) sup_equality) 
  qed
qed

lemma join_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X (rolc R D x) x) \<rbrakk> \<Longrightarrow> join_dense R X D"  
  by (metis (no_types, lifting) Pow_iff join_dense_def lorc_def mem_Collect_eq subset_eq) 

lemma meet_denseD2:
  "\<lbrakk>antisym R X; meet_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf R X (lorc R D x))"
  by (metis Sup_def antisym_on_converse converse_converse join_denseD2) 

lemma meet_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf R X (lorc R D x) x) \<rbrakk> \<Longrightarrow> meet_dense R X D"
  by (simp add: join_denseI2) 
lemma compactly_generated_iff:
  "compactly_generated R X \<longleftrightarrow> join_dense R X (compact_elements R X)" 
  by(auto simp add:compactly_generated_def join_dense_def)


lemma compactD1: "\<lbrakk>antisym R X; refl R X; trans R X;is_compact R X c; A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>A0. \<exists>a. a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"
proof-
  assume A0:"antisym R X" "refl R X" "trans R X" "is_compact R X c" "A \<in> Pow_ne X" "(c, Sup R X A) \<in> R" "is_dir A R"
  obtain A0 where B0:"A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"  by (meson A0(4) A0(5) A0(6) compactD) 
  have B1:"A \<subseteq> X"
    by (simp add: A0(5) pow_neD1) 
  obtain a where B4:"a \<in> A \<and> ub R A0 a"
    by (meson A0(3) A0(7) B0 B1 trans_on_subset updir_finite_obtain)  
  show "(\<exists>A0. \<exists>a. a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"
    using B0 B4 by blast
qed

lemma ccompact0:
  assumes A0:"is_sup_semilattice R X" and
          A1:"is_compact R X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"(c, Sup R X A) \<in> R" and
          A4:"is_dir A R" and 
          A5:"antisym R X" and
          A6:"refl R X" and
          A7:"trans R X"
  shows "\<exists>a \<in> A. (c, a) \<in> R"
proof-
  obtain A0 a where A8:"a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"  by (meson A1 A2 A3 A4 A5 A6 A7 compactD1) 
  obtain B0:"A \<subseteq> X" and B1:"A \<noteq> {}" and B2:"a \<in> X"   by (metis A2 A8 empty_iff in_mono pow_neD1)
  obtain B3:"A0 \<subseteq> X" and B4:"finite A0" and B5:"A0 \<noteq> {}"  by (metis A8 B0 dual_order.trans fpow_ne_iff2)
  have B6:"a \<in> ubd R X A0"  by(rule ubdI, meson A8 ubE, simp add: B2)
  have B7:"(Sup R X A0, a) \<in> R" by (simp add: A0 A5 A7 B3 B4 B5 B6 fsup_lub)
  have B8:"(c, a) \<in> R"   by (meson A0 A1 A5 A7 A8 B2 B3 B4 B5 B7 bsup_finite2 compactD2 is_supE1 trans_onD) 
  show ?thesis   using A8 B8 by blast
qed


definition fne_sup_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow>  'a set" where
  "fne_sup_cl R X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x}"


lemma fne_sup_cl_imp1: "x \<in> fne_sup_cl R X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x)" by (simp add: fne_sup_cl_def)
lemma fne_sup_cl_obtains:  assumes "x \<in> fne_sup_cl R X A"  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup R X F x"  by (meson assms fne_sup_cl_imp1)

lemma fne_sup_cl_extensive:"\<lbrakk>A \<subseteq> X; antisym R X;  refl R X;  trans R X\<rbrakk> \<Longrightarrow> A \<subseteq> fne_sup_cl R X A"
proof-
  assume A0:"A \<subseteq> X" "antisym R X" "refl R X" "trans R X"
  show "A \<subseteq> fne_sup_cl R X A"
  proof
  fix a assume A1: "a \<in> A"
  have B0: "is_sup R X {a} a"    by (meson A0(1) A0(3) A1 reflD1 subsetD sup_singleton) 
  have B2: "{a} \<in> Fpow A"  by (simp add: A1 Fpow_def)
  show "a \<in> fne_sup_cl R X A"
    apply(auto simp add:fne_sup_cl_def)
    using A0(1) A1 apply blast
    using B0 B2 by blast
  qed
qed


lemma fne_sup_cl_ext:
  "\<lbrakk>antisym R X;  refl R X;  trans R X\<rbrakk>  \<Longrightarrow> extensive (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
  apply(auto simp add:extensive_def pwr_def)
  apply (meson fne_sup_cl_imp1 is_supE1)
  using fne_sup_cl_extensive by blast

lemma fne_sup_cl_isotone:
  "\<lbrakk>antisym R X;  refl R X;  trans R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X B"
  apply(auto simp add:fne_sup_cl_def) by (metis Fpow_mono empty_iff subsetD)
           

lemma fne_sup_cl_iso:
  "\<lbrakk>antisym R X;  refl R X;  trans R X\<rbrakk> \<Longrightarrow> isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. fne_sup_cl R X A)"
  apply(auto simp add:isotone_def pwr_def)
  apply (meson fne_sup_cl_imp1 is_supE1)
  apply (meson fne_sup_cl_imp1 is_supE1)
  using fne_sup_cl_isotone by blast

lemma fne_sup_cl_if1:"\<lbrakk>antisym R X;  refl R X;  trans R X; x \<in> X; (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_sup R X F x)\<rbrakk> \<Longrightarrow> x \<in> fne_sup_cl R X A" by (simp add: fne_sup_cl_def)



lemma fne_sup_cl_idempotent0: 
  "\<lbrakk>antisym R X; refl R X; trans R X; s \<in> fne_sup_cl R X (fne_sup_cl R X A)\<rbrakk> \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_sup_cl R X A) \<and> E \<noteq> {} \<and> is_sup R X E s)"
    by (meson fne_sup_cl_imp1)
lemma fne_sup_cl_idempotent1:
   "\<lbrakk>antisym R X; refl R X; trans R X ; E \<in> Pow (fne_sup_cl R X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_sup R X Ex x)"
   by (meson PowD in_mono fne_sup_cl_imp1)
lemma fne_sup_cl_idempotent2: 
  "\<lbrakk>antisym R X; refl R X; trans R X\<rbrakk>  \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X (fne_sup_cl R X A)"
  by (metis (no_types, lifting) fne_sup_cl_def fne_sup_cl_extensive mem_Collect_eq subsetI)  


lemma fne_sup_cl_idempotent:
  assumes A0:"antisym R X" and A1:"refl R X" and A2:"trans R X" and  A4:"A \<subseteq> X"
  shows "fne_sup_cl R X (fne_sup_cl R X A) = fne_sup_cl R X A"
proof-
  have ref:"refl_on X R"by (meson A1 A3 refl_def refl_onI)
  let ?L1="fne_sup_cl R X A" let ?L2="fne_sup_cl R X ?L1"
  show "?L2 = ?L1"
  proof
    show "?L1 \<subseteq>?L2"    by (simp add: assms fne_sup_cl_idempotent2)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup R X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow ?L1 \<and> E \<noteq> {} \<and> is_sup R X E s"    by (meson P0 fne_sup_cl_imp1)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"    by (meson Fpow_subset_Pow P1 assms fne_sup_cl_idempotent1 in_mono)
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup R X Ai}"
      have B00:"((\<lambda>Ai. Sup R X Ai)`?fE) = ?S" by(auto,metis (mono_tags, lifting) B0 A0 is_supE1 someI_ex sup_equality)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"   by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"  have B60:"\<exists>Ai \<in> ?fE. s = Sup R X Ai" using B6A0 by blast
            show "s \<in> E" using B1 B60 assms sup_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E" show "s \<in> ?S"  by (metis (no_types, lifting) B00 B1 B6A1 A0 image_eqI sup_equality)
        qed
      qed
      obtain se where B11A0:"is_sup R X E se"   using P1 by blast
      obtain ss where B11A1:"is_sup R X ?S ss"   using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup R X Ai si)"  using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup R X Ai ti)"   using B1 by blast
      have B12:" (\<And>Ai. Ai \<in>?fE\<Longrightarrow> Ai \<subseteq> X)"
      proof-  
        fix Ai assume B12A:"Ai \<in> ?fE"
        then have B121:"Ai \<in> Fpow A"   using B1 by blast
        then show "Ai \<subseteq> X"   using A4 Fpow_subset_Pow by auto
      qed
      have B13:"is_sup R X ((\<lambda>Ai. Sup R X Ai)`?fE) ss"     using B00 B11A1 by presburger
      have B14:"is_sup R X (\<Union>?fE) ss"
        by (metis (no_types, lifting) A0 A2 B11 B12 B13 P1 image_is_empty sup_families) 
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (smt (verit, best) B0 B11A1 B14 B15 B2 Collect_cong P1 assms empty_Union_conv empty_def fne_sup_cl_if1 is_supE1 mem_Collect_eq sup_equality)
      qed
    qed
  qed
qed

lemma fne_sup_cl_ide:
  "\<lbrakk>antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> idempotent (Pow X) (\<lambda>A. fne_sup_cl R X A)"
  by (simp add: fne_sup_cl_idempotent idempotent_def)
lemma fne_sup_cl_range: 
  "(\<lambda>A. fne_sup_cl R X A)`(Pow X) \<subseteq> Pow X"  
  by (simp add: fne_sup_cl_def image_subset_iff)

lemma fne_sup_cl_is_cl: 
   "\<lbrakk>antisym R X; refl R X; trans R X\<rbrakk>  \<Longrightarrow> closure (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
    by (simp add: fne_sup_cl_ext fne_sup_cl_ide fne_sup_cl_iso fne_sup_cl_range closure_def)

lemma fne_sup_cl_dir:
  assumes A0:"is_sup_semilattice R X" and A1:"A \<subseteq> X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows  "is_dir (fne_sup_cl R X A) R"
proof-
  have B0:"\<And>a b. a \<in> fne_sup_cl R X A \<and> b \<in> fne_sup_cl R X A \<longrightarrow> (\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"
  proof
    fix a b assume A2:"a \<in> fne_sup_cl R X A \<and> b \<in> fne_sup_cl R X A "
    obtain Ea where A3:"Ea \<in> Fpow A \<and> Ea \<noteq> {} \<and> is_sup R X Ea a"by (meson A2 fne_sup_cl_imp1)
    obtain Eb where A4:"Eb \<in> Fpow A \<and> Eb \<noteq> {} \<and> is_sup R X Eb b" by (meson A2 fne_sup_cl_imp1)
    have B1:"Ea \<union> Eb \<in> Fpow A \<and> Ea \<union> Eb \<noteq> {}"      by (metis A3 A4 Fpow_Pow_finite Int_Collect Pow_iff Un_empty Un_subset_iff finite_UnI)
    have B2:"(Ea \<union> Eb) \<subseteq> X"   by (metis A1 A3 A4 Fpow_Pow_finite Int_Collect Pow_iff dual_order.trans sup.boundedI)
    have B2b:"finite (Ea \<union> Eb)"   by (metis B1 Fpow_Pow_finite Int_Collect)
    obtain c where A5:"is_sup R X (Ea \<union> Eb) c" using A0 B1 B2 B2b assms(3) assms(5) bsup_finite2 by blast 
    have B3:"c \<in> fne_sup_cl R X A \<and> (a, c) \<in> R \<and> (b, c) \<in> R"   by (smt (verit, best) A3 A4 A5 B1 fne_sup_cl_def is_supE1 is_sup_iso1 mem_Collect_eq semilattice_sup_class.sup_ge1 sup.cobounded2) 
    show "(\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"   using B3 by blast
  qed
  show ?thesis   by (simp add: B0 is_dirI1)
qed
  

lemma ccompact1:
  assumes A0:"is_csup_semilattice R X" and
          A1:"c \<in> X" and
          A2:"(\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>a \<in> A. (c, a) \<in> R))" and 
          A3:"antisym R X" and 
          A4:"refl R X" and 
          A5:"trans R X"
  shows "is_compact R X c"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R))"
  proof
    fix A assume A6:"A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R"
    let ?C="fne_sup_cl R X A"
    have B0:"is_dir ?C R"   by (simp add: A0 A3 A4 A5 A6 csup_fsup fne_sup_cl_dir pow_neD1)
    have B1:"A \<subseteq> ?C"   by (simp add: A3 A4 A5 A6 fne_sup_cl_extensive pow_neD1) 
    have B2:"A \<subseteq> X \<and> ?C \<subseteq> X"  by (simp add: A6 fne_sup_cl_def pow_neD1)  
    have B3:"(Sup R X A, Sup R X ?C) \<in> R"  by (metis A0 A3 A5 A6 B1 B2 pow_ne_iff2 sup_iso1b)
    have B4:"(c, Sup R X ?C) \<in> R"  by (metis A0 A1 A3 A5 A6 B1 B2 B3 csupD50 ne_subset_ne pow_ne_iff2 trans_onD) 
    obtain d where B4:"d \<in> ?C \<and> (c, d) \<in> R"  by (metis A2 A6 B0 B1 B2 B4 ne_subset_ne pow_ne_iff2) 
    obtain Fd where B5:"Fd \<in> Fpow_ne A \<and> Sup R X Fd = d" by (smt (verit) A3 B4 fne_sup_cl_def fpow_ne_iff1 mem_Collect_eq sup_equality) 
    have B6:"Fd \<in> Fpow_ne A \<and> (c, Sup R X Fd) \<in> R" using B4 B5 by fastforce
    show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"   using B6 by blast
  qed
  show ?thesis by (metis A1 P0 compactI)
qed


lemma bot_compact:
  assumes A0:"antisym R X" and 
          A1:"refl R X" and 
          A2:"trans R X" and
          A3:"bot \<in> X" and
          A4:"(\<And>x. x \<in> X \<Longrightarrow> (bot, x) \<in> R)"
  shows "is_compact R X bot"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> (bot, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (bot, Sup R X A0) \<in> R))" 
    proof
      fix A assume A5:"A \<in> Pow_ne X \<and> (bot, Sup R X A) \<in> R" obtain a where A6:"a \<in> A"   using A5 pow_ne_iff2 by fastforce 
      then obtain B0:"A \<subseteq> X" and B1:"A \<noteq> {}"   using A5 pow_neD1 by blast
      have B2:"{a} \<in> Fpow_ne A \<and> (bot, Sup R X {a}) \<in> R"   using A0 A1 A4 A6 B0 finite_insert fpow_ne_iff2 ge_sup2 reflD1 by fastforce 
      show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> (bot, Sup R X A0) \<in> R)"   using B2 by blast 
    qed
  show ?thesis by (simp add: A3 P0 compactI)
qed

lemma dir_set_closure_subset:
  assumes A0:"clr (pwr X) (Pow X) C" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"(cl_from_clr (pwr X) C) {x} \<subseteq> Sup  (pwr X) C A" and 
          A6:"is_dir A (pwr X)"
  shows "\<exists>a \<in> A. (cl_from_clr (pwr X) C) {x} \<subseteq> a"
proof-
  let ?R="pwr X" let ?P="Pow X"
  obtain B0:"antisym ?R ?P" and B1:"refl ?R ?P" and B2:"trans ?R ?P"   by (meson powrel1 powrel2 powrel3 reflI1 refl_onD)
  let ?f="cl_from_clr ?R C"
  have B3:"C \<subseteq> Pow X"   using A0 clrD2 by blast
  have B4:"A \<subseteq> C"  by (simp add: A4 pow_neD1)   
  have B5:"\<Union>A \<in> C"   using A2 A4 A6 B4 pow_ne_bot by blast
  have B6:"is_sup ?R C A (\<Union>A)"  by (meson B3 B4 B5 powrel9 sup_in_subset) 
  have B7:"Sup ?R C A = \<Union>A"  by (simp add: B3 B6 powrel6 powrel7 sup_equality)
  have B8:"?f {x} \<in> C"  using A0 A3 cl_range1 powrel1 by fastforce
  have B9:"({x}, ?f {x}) \<in> ?R"  by (metis A0 A3 B3 PowI bot.extremum cl_ext1 insert_absorb insert_mono powrel1 powsimp1 pwr_mem_iff refl_def subset_refl)
  have B10:"{x} \<subseteq> ?f {x}"  using B9 powrel8 by blast 
  have B11:"... \<subseteq> \<Union>A"   using A5 B7 by auto 
  have B12:"{x} \<subseteq> \<Union>A"  using B10 B11 by blast
  obtain a where B13:"a \<in> A \<and> x \<in> a"   using B12 by auto  
  have B14:"({x}, a) \<in> ?R" by (meson B13 B3 B4 empty_subsetI in_mono insert_subsetI powsimp1 pwr_memI)
  have B15:"a \<in> ubd ?R C {{x}}"  by (meson B13 B14 B4 in_mono ubd_singleton_iff)
  have B16:"?f a = a"  by (meson A0 B0 B1 B13 B4 cl_range31 in_mono)
  have B17:"(?f {x}, ?f a) \<in> ?R" by (smt (verit, ccfv_SIG) A0 B0 B15 B16 B9 Pow_iff closure_range_def clr_equality converseD greatestD2 order.trans pwr_memD)
  have B18:"(?f {x}, a)\<in>?R" using B16 B17 by force
  have B19:"?f {x} \<subseteq> a"  using B18 powrel8 by blast 
  show "(\<exists>a\<in>A. ?f {x} \<subseteq> a)"  using B13 B19 by blast 
qed

      
lemma dir_set_closure_subset2:
  assumes A0:"clr (pwr X) (Pow X) C" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"((cl_from_clr  (pwr X) C) {x}, Sup  (pwr X) C A) \<in> pwr X" and 
          A6:"is_dir A (pwr X)"
  shows "\<exists>a \<in> A. ((cl_from_clr (pwr X) C) {x}, a) \<in> pwr X"
proof-
  from A5 have B0:"(cl_from_clr  (pwr X) C) {x} \<subseteq> Sup  (pwr X) C A"   by (simp add: powrel8)
  obtain a where B1:"a \<in> A \<and> (cl_from_clr (pwr X) C) {x} \<subseteq> a" using dir_set_closure_subset  by (metis A0 A2 A3 A4 A6 B0) 
  have B2:"a \<subseteq> X"   by (meson A0 A4 B1 Pow_iff clrD2 in_mono pow_neD1)  
  then have "((cl_from_clr (pwr X) C) {x}, a) \<in> pwr X "   by (metis B1 PowI Pow_mono Union_Pow_eq is_supD1121 powrel5)
  then show ?thesis  using B1 by blast
qed

lemma singleton_closure_compact:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk>\<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X"
  shows "is_compact (pwr X) C (cl_from_clr (pwr X) C {x})"
  apply(rule ccompact1) 
  using A0 clatD1 clr_is_clattice apply (metis pow_is_clattice powrel1 powrel2 powrel3 refl_def refl_onD)
  apply (meson A0 A3 Pow_iff cl_range1 empty_subsetI insert_subset powrel1)
  apply (simp add: A0 A2 A3 dir_set_closure_subset2)
  apply (meson A0 clrD2 powrel6)
  apply (meson A0 clrD2b powrel3 refl_def refl_onD)
  by (meson A0 clrD2 powrel7)

lemma closed_compgen:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"E \<in> C"
  shows "(\<exists>A \<in> Pow (compact_elements (pwr X) C). is_sup (pwr X) C A E)"
proof-
   let ?R="pwr X"  let ?f="cl_from_clr ?R C"
   let ?A="{y. (\<exists>x \<in> E. y= ?f {x})}"
  have B0:"is_clattice (pwr X) C"  by (meson A0 clr_is_clattice pow_is_clattice powrel1 powrel2 powrel3 refl_def refl_onD)
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact (pwr X) C (?f {x})" by (metis A0 A1 A2 singleton_closure_compact)
  have P1:"E \<in> Pow X" using A0 A3 clrD2 by blast
  have P2:"\<forall>x. x \<in> E \<longrightarrow> {x} \<in> Pow X"  using P1 by blast 
  have P3:"?A \<subseteq> C"
  proof 
    fix y assume A9:"y \<in> ?A" 
    obtain x where P30:"x \<in> E \<and> y = ?f {x}" using A9 by blast
    show "y \<in> C"   by (metis A0 P2 P30 cl_range1 powrel1)
  qed
  have B9:"\<forall>x. x \<in> E \<longrightarrow> {x} \<subseteq> ?f {x}"  using cl_ext1[of "pwr X" C "Pow X"]  by (meson A0 P2 clrD2 powrel1 powrel8 powsimp1 pwr_memI reflI1 set_eq_subset)
  have B10:"?f E = E"  by (meson A0 A3 cl_range31 powrel1 powrel3 refl_def refl_onD)
  have B11:"\<And>x. x \<in> E \<longrightarrow> ?f {x} \<subseteq> ?f E"
    by (smt (verit, ccfv_SIG) A0 A3 B10 P2 PowD Pow_bottom Pow_iff cl_lt_ub2 clrD2 insert_subset powrel1 powrel3 pwr_mem_iff refl_def refl_on_def subset_iff)
  have B11b:"ub ?R ?A E" by (smt (verit) B10 B11 P1 Pow_iff mem_Collect_eq pwr_memI ub_def)
  have B11c:"E \<in> ubd ?R C ?A"  by (simp add: A3 B11b ubd_mem_iff)
  have B12:"E = (\<Union>x \<in> E. {x})"    by simp
  have B13:"... \<subseteq> (\<Union>x \<in> E. ?f {x})"  using B9 by blast
  have B14:"... = (\<Union>?A)"  by blast
  have B15:"... = Sup  ?R (Pow X) ?A" by (metis (no_types, lifting) A0 P3 clrD2 powrel1 powrel9 sup_equality)
  have B16:"... \<subseteq> Sup ?R C ?A" using sup_iso2  by (metis (no_types, lifting) A0 B0 P3 closure_range_def pow_is_clattice powrel1 powrel2 powrel8)
  have B17:"... \<subseteq> E"  by (smt (verit) A0 A3 B11b B12 B13 B14 P1 P3 clrD2 is_supE4 powrel6 powrel9 pwr_mem_iff set_eq_subset sup_equality sup_in_subset)
  have B18:"\<forall>x. x \<in> ?A \<longrightarrow> x \<in> compact_elements ?R C" using B1 P1 compact_elements_mem_iff1 by fastforce
  have B19:"?A \<in> Pow (compact_elements ?R C)"  using B18 by blast
  have B20:"E = Sup ?R C ?A" using B13 B15 B16 B17 by auto
  have B21:"is_sup ?R C ?A E"
    by (metis (no_types, lifting) A0 A3 B12 B13 B14 B15 B16 B20 P3 clrD2 powrel9 subset_antisym sup_in_subset)
  show "\<exists>A \<in> Pow (compact_elements ?R C). is_sup ?R C A E"   using B19 B21 by blast
qed


lemma clr_compgen1:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)"
  shows "compactly_generated (pwr X) C \<and> (\<forall>x. x \<in> X \<longrightarrow> is_compact (pwr X) C ((cl_from_clr (pwr X) C) {x}))"
  by (simp add: A0 A1 A2 closed_compgen compactly_generated_def singleton_closure_compact)



lemma clr_compgen2:
 "\<lbrakk>clr (pwr X) (Pow X) C; (\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C);(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)\<rbrakk> \<Longrightarrow> compactly_generated (pwr X) C"
  by (simp add: clr_compgen1)

lemma filters_on_lattice_compactgen:
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> compactly_generated (pwr X) (filters_on R X)" 
  apply(rule_tac ?X="X" in clr_compgen2)
  apply (simp add: filter_is_clr lattD41)
  apply (simp add: filter_inter_closed2 lattD41)
  by (simp add: filters_on_iff lattice_filter_dunion9)


lemma pfilters_metofprimes2:
  assumes A0:"distributive_lattice R X" and A1:"greatest R X top" and A2:"F \<in> pfilters R X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on R X \<and> sup_prime R X Fm " and "F = Inf (powrel X) (filters_on R X) M"
proof-
  let ?FX="(filters_on R X)"
  have B0:"compactly_generated (powrel X) ?FX"   using A0 A1 distr_latticeD5 filters_on_lattice_compactgen lattD1 by auto
  have B1:"is_clattice (powrel X) ?FX"  using A0 A1 distr_latticeD5 lattice_filters_complete by auto
  have B2:"F \<in> ?FX" by (simp add: A2 filters_on_iff pfilters_memD1)
  have B3:"F = Inf (powrel X) ?FX {Fm \<in> ?FX. meet_irr (powrel X) ?FX Fm \<and> (F, Fm) \<in> (powrel X)}"   by (simp add: B0 B1 B2 mirred_temp3)
  have B4:"\<And>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm} \<Longrightarrow> Fm \<in> ?FX \<and> sup_prime X Fm " 
  proof-
    fix Fm assume A3:"Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}" 
    have B40:"Fm \<in> ?FX \<and> meet_irr ?FX Fm"  using A3 by blast
    have B41:"fin_inf_irr ?FX Fm"  using A0 B40 distr_lattice_filters meet_irr_imp_fmeet_irr by blast
    have B43:"is_greatest ?FX X"   by (meson A0 distr_latticeD5 filterD2 filters_is_clr1b filters_on_iff greatest_iff lattD41)
    have B44:"sup_prime X Fm"
    proof(cases "pfilter X Fm")
      case True then show ?thesis   using A0 B40 B41 filters_on_iff prime_filter_irr3_converse sup_prime_def by blast
    next
      case False obtain B45:"Fm = X"  using B40 False filters_on_iff by blast
      then show ?thesis using sup_primeI1 by blast
    qed
    show "Fm \<in> ?FX \<and> sup_prime X Fm"  by (simp add: B40 B44)
  qed
  then show ?thesis  using B3 that by blast
qed

(*     

lemma filter_closure_of_filters1:
  "\<lbrakk>is_inf_semilattice R X;A \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> F \<in> A \<Longrightarrow> F \<subseteq> (filter_closure X (\<Union>A))"
  by (metis Union_Pow_eq Union_mono Union_upper filter_cl0 filters_is_clr1 order.trans)

lemma filter_closure_of_filters2_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>filters_on X"
  by (metis all_not_in_conv cSup_least empty_Union_conv filterD1 filterD2 filter_cl3a filters_on_iff in_mono)

lemma filter_closure_of_filters2:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X;is_greatest X top\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>filters_on X"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1)

lemma filter_closure_of_filters3_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>ubd R  (filters_on X) A"
  by (simp add: filter_closure_of_filters1 filter_closure_of_filters2_ne ubdI)

lemma filter_closure_of_filters3:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>ubd R  (filters_on X) A"
  by (simp add: filter_closure_of_filters1 filter_closure_of_filters2 ubdI)

lemma filter_closure_of_filters4_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}; G \<in> ubd R  (filters_on X) A\<rbrakk> \<Longrightarrow> (filter_closure X (\<Union>A)) \<subseteq> G"
  by (metis UnionI Union_least basic_trans_rules(31) ex_in_conv filterD1 filter_cl_least2a filters_on_iff ubd_mem_iff2)

lemma filter_closure_of_filters4:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X;is_greatest X top; G \<in> ubd R  (filters_on X) A\<rbrakk> \<Longrightarrow> (filter_closure X (\<Union>A)) \<subseteq> G"
  by (simp add: Union_least filter_cl_least2 filters_on_iff ubd_mem_iff2)

lemma filter_closure_of_filters5_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (filters_on X) A  (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters3_ne filter_closure_of_filters4_ne is_supI5)

lemma filter_closure_of_filters5:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> is_sup (filters_on X) A  (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters3 filter_closure_of_filters4 is_supI5)


lemma filters_on_lattice_inf01:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2}"
  by (metis IntE bsup_idem1 filterD21)

lemma pfilters_on_lattice_inf01:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2}"
  by (metis IntD2 bsup_idem1 inf.order_iff inf_commute is_pfilterD3)

lemma filters_on_lattice_inf02:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  using filterD4[of "X" "F1"] is_ord_clE1[of "X" "F1" "f1" "z"] filterD4[of "X" "F2"] is_ord_clE1[of "X" "F2" "f2" "z"]
  by (metis Int_iff bsup_geI1 bsup_geI2 dual_order.refl filterD21 lattD42 ssupD4)

lemma pfilters_on_lattice_inf02:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  by (meson filters_on_lattice_inf02 is_pfilterD1)

lemma filters_on_lattice_inf03:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup X {f1, f2} \<in> F1 \<inter> F2 "
  using filters_on_lattice_inf02 by blast

lemma pfilters_on_lattice_inf03:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup X {f1, f2} \<in> F1 \<inter> F2 "
  using pfilters_on_lattice_inf02 by blast

lemma filter_on_lattice_sup01: "\<lbrakk>is_lattice X; is_filter X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F"  by (simp add: filter_bsup_memI2 lattD42)
lemma ideal_on_lattice_inf01: "\<lbrakk>is_lattice X; is_ideal X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> F"  by (simp add: ideal_binf_memI2 lattD41)


lemma pfilter_on_lattice_sup01: "\<lbrakk>is_lattice X; is_pfilter X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F "by (simp add: filter_on_lattice_sup01 is_pfilterD1)
lemma pideal_on_lattice_inf01: "\<lbrakk>is_lattice X; is_pideal X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> F "by (simp add: ideal_on_lattice_inf01 is_pidealD1)


lemma filter_on_lattice_top0:
  "is_lattice X \<Longrightarrow> is_filter X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> (a, x) \<in> R"
  by (meson is_filter_def bsup_iff filter_on_lattice_sup01 insertI1 latt_iff subsetD ubd R  ub_singleton)

lemma pfilter_on_lattice_top0:
  "is_lattice X \<Longrightarrow> is_pfilter X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> (a, x) \<in> R"
  by (simp add: filter_on_lattice_top0 is_pfilterD1)

lemma filter_on_lattice_top:
  "\<lbrakk>is_lattice X;  is_filter X {x}\<rbrakk> \<Longrightarrow>  is_greatest X x"
  by(rule greatestI1, rule ubdI, simp add: filter_on_lattice_top0, simp add:filterD21)

lemma pfilter_on_lattice_top:
  "\<lbrakk>is_lattice X;  is_pfilter X {x}\<rbrakk> \<Longrightarrow>  is_greatest X x"
  by (simp add: filter_on_lattice_top is_pfilterD1)

lemma filter_on_lattice_eq:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup X {f1, f2})}"
  apply(auto simp add:set_eq_iff)  apply (metis bsup_idem1 filterD21) 
  using filters_on_lattice_inf03[of "X" "F1" "F2"]  by blast+

lemma pfilter_on_lattice_eq:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup X {f1, f2})}"
  by (simp add: filter_on_lattice_eq is_pfilterD1)

lemma filters_on_lattice_inf2b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (\<ge>)"
  using filter_inter_dir3 lattD41 by blast

lemma pfilters_on_lattice_inf2b:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (\<ge>)"
  by (simp add: filters_on_lattice_inf2b is_pfilterD1)

lemma filters_upcl:"\<lbrakk>is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (\<le>)" apply(auto simp add:is_ord_cl_def) using filterD4 is_ord_clE1 by blast+
lemma ideals_dwcl:"\<lbrakk>is_ideal X F1; is_ideal X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (\<ge>)" apply(auto simp add:is_ord_cl_def) using idealD4 ord_cl_memI1 by blast+

lemma pfilters_upcl:"\<lbrakk>is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (\<le>)" by (simp add: filters_upcl is_pfilterD1)
lemma pideals_dwcl:"\<lbrakk>is_pideal X F1; is_pideal X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (\<ge>)" by (simp add: ideals_dwcl is_pidealD1)

lemma filter_on_lattice_inf4b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (metis empty_iff equals0I filterD1 filters_on_lattice_inf02)

lemma pfilter_on_lattice_inf4b:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (simp add: filter_on_lattice_inf4b is_pfilterD1)

lemma filters_on_lattice_inf5b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_filter X (F1 \<inter> F2)"
  by (meson filterD2 filterI1 filter_on_lattice_inf4b filters_on_lattice_inf2b filters_upcl inf.coboundedI2) 

lemma pfilters_on_lattice_inf5b:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> is_pfilter X (F1 \<inter> F2)"
  by (metis Int_left_absorb filters_on_lattice_inf5b inf.orderE is_pfilterD3 is_pfilter_def)

lemma filters_on_lattice_inf6b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd R (filters_on X) {F1, F2})"
  by (simp add: lbd_mem_iff filters_on_iff filters_on_lattice_inf5b lb_double_iff1)

lemma pfilters_on_lattice_inf6b:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd R (pfilters X) {F1, F2})"
  by (simp add: lbd_mem_insert lbd_singleton_iff pfilters_memI pfilters_on_lattice_inf5b)

lemma filters_on_lattice_inf7b:
  "\<lbrakk>is_filter X F1; is_filter X F2; G \<in> (lbd R (filters_on X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: lbd_mem_iff lb_double_iff1)

lemma pfilters_on_lattice_inf7b:
  "\<lbrakk>is_pfilter X F1; is_pfilter X F2; G \<in> (lbd R (pfilters X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: lbd_mem_iff lb_double_iff1)

lemma filters_on_lattice_inf8b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk>\<Longrightarrow> is_inf (filters_on X) {F1, F2} (F1 \<inter> F2)"
  by (meson filters_on_lattice_inf6b filters_on_lattice_inf7b is_infI5)

lemma pfilters_on_lattice_inf8b:
  "\<lbrakk>is_lattice X; is_pfilter X F1; is_pfilter X F2\<rbrakk>\<Longrightarrow> is_inf (pfilters X) {F1, F2} (F1 \<inter> F2)"
  by (meson is_infI5 pfilters_on_lattice_inf6b pfilters_on_lattice_inf7b)

(*
  On a lattice filters form an inf semilattice
*)

lemma filters_on_lattice_inf_semilattice1:
  "is_lattice X \<Longrightarrow> is_inf_semilattice (filters_on X)"
  by (metis empty_iff filters_is_clr1b filters_on_iff filters_on_lattice_inf8b lattD41 sinfI1)

lemma filters_on_lattice_sup1b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X (\<Union>EF)) (\<le>)"
  by (metis Sup_least all_not_in_conv empty_Union_conv filterD1 filterD2 lattD41 ne_filter_cl1)

lemma filters_on_lattice_sup2a:
  assumes A0:"is_lattice X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)" and A2:"EF \<noteq> {}" and
          A3: "a \<in> (filter_closure X (\<Union>EF))" and  A4:"b \<in> (filter_closure X (\<Union>EF))"
  shows "(\<exists>c \<in> (filter_closure X (\<Union>EF)).  a \<ge> c \<and>  (c, b)\<in>R)"
proof-
  obtain Fa Fb where B1:"Fa \<subseteq> (\<Union>EF)" "finite Fa" "Fa \<noteq> {}" "Inf X Fa \<le> a" and 
                     B2:"Fb \<subseteq> (\<Union>EF)" "finite Fb" "Fb \<noteq> {}" "Inf X Fb \<le> b"
   by (metis A3 A4 Pow_empty A1 A2  filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD)
  have B3:"Fa \<union> Fb \<subseteq> \<Union>EF \<and> finite (Fa \<union> Fb) \<and> (Fa \<union> Fb) \<noteq> {}"
    by (simp add: B1(1) B1(2) B2(1) B2(2) B2(3))
  have B4:"Fa \<union> Fb \<subseteq> X"
    by (meson A1 B3 Sup_le_iff filterD2 subsetD subsetI)
  have B5:"Inf X (Fa \<union> Fb) \<in>  (filter_closure X (\<Union>EF))"
    by (meson A0 B3 B4 binf_finite2 dual_order.refl filter_closure_memI1 is_infE1 lattD41)
  have B6:"Inf X (Fa \<union> Fb) \<le> a \<and> Inf X (Fa \<union> Fb) \<le> b"
    by (meson A0 B1 B2 B3 B4 Un_upper1 binf_finite2 dual_order.trans is_inf_ant1 lattD41 sup.cobounded2)
  show ?thesis
    using B5 B6 by blast
qed


lemma filters_on_inf_lattice_sup2b:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top;(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)\<rbrakk> \<Longrightarrow> is_dir (filter_closure X (\<Union>EF)) (\<ge>)"
  by (simp add: Sup_least filterD2 filter_cl2)

lemma filters_on_inf_lattice_sup2c:
  "\<lbrakk>is_inf_semilattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure X (\<Union>EF)) (\<ge>)"
  by (simp add: Posets16.is_filter_def cSup_least filter_cl2a)


lemma filters_on_lattice_sup2b:
  "\<lbrakk>is_lattice X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure X (\<Union>EF)) (\<ge>)"
  by (simp add: filters_on_lattice_sup2a is_dwdirI1)

lemma filters_on_lattice_sup3b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> filter_closure X (\<Union>EF) \<noteq> {}"
  by (simp add: Union_least filterD2 filter_closure_ne lattD1)

lemma filters_on_inf_lattice_sup3b:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)\<rbrakk> \<Longrightarrow> filter_closure X (\<Union>EF) \<noteq> {}"
  by (simp add: Union_least filterD2 filter_closure_ne is_inf_semilattice_def)
  
lemma filters_on_lattice_sup4b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter X (filter_closure X (\<Union>EF))"
  by (simp add: is_filter_def filter_closure_iff filters_on_lattice_sup1b filters_on_lattice_sup2b filters_on_lattice_sup3b subset_iff)

lemma filters_on_inf_lattice_sup4b:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)\<rbrakk> \<Longrightarrow> is_filter X (filter_closure X (\<Union>EF))"
  by (simp add: Sup_le_iff filterD2 filter_cl3)

lemma filters_on_lattice_sup5b:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}; F \<in> EF\<rbrakk> \<Longrightarrow>  F \<subseteq> (filter_closure X (\<Union>EF))"
  by (meson UnionI Union_least filterD2 filter_closure_singleton subsetI)

lemma filters_on_lattice_sup6b:
  assumes A0:"is_lattice X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)" and A2:"EF \<noteq> {}" and
          A3:"is_filter X G"  and A4:"(\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> G)"
  shows "filter_closure X (\<Union>EF) \<subseteq> G"
proof
  fix x assume A5:"x \<in> filter_closure X (\<Union>EF)"
  obtain Fx where  B1:"Fx \<subseteq>  (\<Union>EF) \<and> finite Fx \<and> Fx \<noteq> {} \<and> Inf X Fx \<le>x"
    by (metis A5 Pow_empty A1 A2 filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD)
  have B2:"Fx \<subseteq> G"
    using B1(1) A4  by blast
  have B3:"Fx \<subseteq> X"
    using B2 is_filter_def A3 by auto
  show "x \<in> G"
    by (metis A0 A3 A5 B1 B2 bot.extremum_uniqueI filterD4 filter_closure_iff filter_finf_closed3 is_ord_clE1 lattD41)
qed


lemma filters_on_lattice_sup7b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (filters_on X) EF (filter_closure X (\<Union>EF))"
  by(simp add:is_sup_def filters_on_lattice_sup4b filters_on_iff  ubd_mem_iff2  filters_on_lattice_sup5b filters_on_lattice_sup6b least_iff)

(*On a lattice filters form a complete sup semilattice*)

lemma filters_on_lattice_csup:
  "is_lattice X \<Longrightarrow> is_csup_semilattice (filters_on X)"
  by (metis empty_not_insert filters_is_clr1b filters_on_iff filters_on_lattice_sup7b insert_absorb insert_subset is_csup_semilattice_def lattD41)

lemma filters_on_lattice_sup_semilattice1b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_sup (filters_on X) {F1, F2} (filter_closure X (F1 \<union> F2))"
  by (metis Union_insert ccpo_Sup_singleton empty_not_insert filters_on_lattice_sup7b insertE singleton_iff)

lemma filters_on_lattice_sup_semilattice2b:
  "is_lattice X \<Longrightarrow> is_sup_semilattice (filters_on X)"
  by (metis filters_on_iff filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice1b is_inf_semilattice_def is_sup_semilattice_def)

lemma filters_on_lattice_sup_semilattice3b:
  "is_lattice X \<Longrightarrow> EF \<subseteq> (filters_on X) \<Longrightarrow> finite EF \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> (Sup (filters_on X) EF) \<in> filters_on X"
  by (meson bsup_finite2 filters_on_lattice_sup_semilattice2b is_supE1)

lemma filters_on_lattice_csup2:
  "is_lattice X \<Longrightarrow> EF \<subseteq> (filters_on X) \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> (Sup (filters_on X) EF) \<in> filters_on X"
  using csupD50 filters_on_lattice_csup by blast

definition binary_filter_sup::"'a::order set \<Rightarrow>'a::order set\<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "binary_filter_sup X A B = {x \<in> X. \<exists>a \<in> A. \<exists>b \<in> B. Inf X {a, b} \<le> x}"

lemma filter_bsup_memD1:
  "x \<in> binary_filter_sup X A B \<Longrightarrow> x \<in> X" by (simp add:binary_filter_sup_def)

lemma filter_bsup_mem_iff:
  "x \<in> binary_filter_sup X A B \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. \<exists>b \<in> B. Inf X {a, b} \<le> x))"
  by (simp add:binary_filter_sup_def)

lemma binary_filter_sup_obtains:
  assumes A0:"a \<in>  (binary_filter_sup X F1 F2)"
  obtains a1 a2 where "a1 \<in> F1 \<and> a2 \<in> F2 \<and> Inf X {a1, a2} \<le> a"
  by (meson assms filter_bsup_mem_iff)

lemma filters_on_lattice_bsup01:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"a \<in> F1"
  shows "a \<in> binary_filter_sup X F1 F2"
proof-
  obtain y where A4:"y \<in> F2"
    using A2 filterD1 by auto
  have B0:"Inf X {a, y} \<le> a"
    by (meson A0 A1 A2 A3 A4 binf_leI1 dual_order.refl filterD21 lattD41)
  show "a \<in> binary_filter_sup X F1 F2"
    by (meson A1 A3 A4 B0 filterD21 filter_bsup_mem_iff)
qed

lemma filters_on_lattice_bsup02:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"b \<in> F2"
  shows "b \<in> binary_filter_sup X F1 F2"
proof-
  obtain x where A4:"x \<in> F1"
    using A1 filterD1 by auto
  have B0:"Inf X {x, b} \<le> b"
    by (meson A0 A1 A2 A3 A4 binf_leI2 dual_order.refl filterD21 lattD41)
  show "b \<in> binary_filter_sup X F1 F2"
    by (meson A2 A3 A4 B0 filterD21 filter_bsup_mem_iff)
qed

lemma filters_on_lattice_bsup03:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<subseteq> (binary_filter_sup X F1 F2)"
  by (simp add: filters_on_lattice_bsup01 subsetI)

lemma filters_on_lattice_bsup04:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F2 \<subseteq> (binary_filter_sup X F1 F2)"
  by (simp add: filters_on_lattice_bsup02 subsetI)

lemma filters_on_lattice_bsup1b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow>  is_ord_cl X (binary_filter_sup X F1 F2) (\<le>)"
  apply(auto simp add:binary_filter_sup_def is_ord_cl_def) using dual_order.trans by blast

lemma tmp_inf_lemma:
  assumes "is_lattice X"  "a \<in> X" "a1 \<in> X" "a2 \<in> X" "b1 \<in> X" "b2 \<in> X" "Inf X {a1, a2} \<le> a" 
  shows " Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<le> a"
proof-
  have B0:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} = Inf X {a1, b1, a2, b2}"
    by (simp add: assms(1) assms(3-6) inf_semilattice_finf_props4 lattD41)
  have B1:"... \<le> Inf X {a1, a2}"
    using inf_semilattice_finf_anti[of X "{a1, a2}" "{a1, b1, a2, b2}"]
    by (simp add: assms(1) assms(3-6) fpow_ne_iff2 lattD41)
  have B2:"... \<le> a" by (simp add: assms(7)) 
  show ?thesis
    using B0 B1 B2 by auto
qed 
  

lemma filters_on_lattice_bsup2a:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and
          A3: "a \<in>  (binary_filter_sup X F1 F2)" and  A4:"b \<in>  (binary_filter_sup X F1 F2)"
  shows "(\<exists>c \<in> (binary_filter_sup X F1 F2).  a \<ge> c \<and>  (c, b)\<in>R)"
proof-
  obtain a1 a2 where B0:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> Inf X {a1, a2} \<le> a"
    using A3 binary_filter_sup_obtains by blast
  obtain b1 b2 where B1:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> Inf X {b1, b2} \<le> b"
    using A4 binary_filter_sup_obtains by blast
  have B0b:"a \<in> X \<and> b \<in> X \<and> a1 \<in> X \<and> a2 \<in> X \<and> b1 \<in> X \<and> b2 \<in> X"
    using A1 A2 A3 A4 B0 B1 filterD21 filter_bsup_memD1 by blast
  have B2:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<le> a"
    using tmp_inf_lemma[of X a a1 a2 b1 b2]  using A0 B0 B0b by fastforce
  have B3:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<le> b"
    using tmp_inf_lemma[of X b b1 b2 a1 a2] by (simp add: A0 B0b B1 insert_commute)
  obtain ab1 where P1A3:"ab1 \<in> F1 \<and> ab1 \<le> a1 \<and> ab1 \<le> b1"
    by (meson A1 B0 B1 is_filter_def is_dwdirE1)
  obtain ab2 where P1A4:"ab2 \<in> F2 \<and> ab2 \<le> a2 \<and> ab2 \<le> b2"
    by (meson A2 B0 B1 is_filter_def is_dwdirE1)
  have P1B1:"ab1 \<le> Inf X {a1, b1} \<and> ab2 \<le> Inf X {a2, b2}"
    by (meson A0 A1 A2 B0 B1 P1A3 P1A4 binf_leI3 filterD21 lattD41)
  have P1B2:"Inf X {a1, b1} \<in> F1 \<and> Inf X {a2, b2} \<in> F2"
    using A0 A1 A2 B0 B1 filter_finf_closed1 lattD41 by blast
  have P1B3:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<in> (binary_filter_sup X F1 F2)"
    by (meson A0 A1 A2 P1B2 filterD21 filter_bsup_mem_iff lattD41 order_refl sinfD4)
  show "(\<exists>c \<in> (binary_filter_sup X F1 F2).  a \<ge> c \<and>  (c, b)\<in>R)"
    using B2 B3 P1B3 by blast
qed
         
lemma filters_on_lattice_bsup2b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (binary_filter_sup X F1 F2) (\<ge>)"
  by (simp add: filters_on_lattice_bsup2a is_dwdirI1)

lemma filters_on_lattice_bsup3:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<noteq> {}"
  by (metis is_filter_def filters_on_lattice_bsup04 ne_subset_ne)

lemma filters_on_lattice_bsup4:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<in> filters_on X"
  by (metis is_filter_def filter_bsup_mem_iff filters_on_iff filters_on_lattice_bsup1b filters_on_lattice_bsup2b filters_on_lattice_bsup3 subsetI)

lemma filters_on_lattice_bsup5:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<in> ubd R  (filters_on X) {F1, F2}"
  by (simp add: filters_on_lattice_bsup03 filters_on_lattice_bsup04 filters_on_lattice_bsup4 ubd_mem_doubleI)

lemma filters_on_lattice_bsup6:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"G \<in> (ubd R  (filters_on X) {F1, F2})"
  shows "(binary_filter_sup X F1 F2) \<subseteq> G" (is "?L \<subseteq> ?R")
proof
  fix x assume A4:"x \<in> ?L"
  obtain a1 a2  where B0:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> Inf X {a1, a2} \<le> x"
    using A4 binary_filter_sup_obtains by blast
  have B1:"a1 \<in> G \<and> a2 \<in> G"
    by (meson A3 B0 subsetD ubd_mem_doubleE1 ubd_mem_doubleE2)
  have B2:"Inf X {a1, a2} \<in> G"
    using A0 A3 B1 filter_finf_closed1 filters_on_iff lattD41 ubdD2 by blast
  have B3:"is_filter X G "
    using A3 filters_on_iff ubdD2 by blast
  show "x \<in> G"
    by (meson A4 B0 B2 B3 filterD4 filter_bsup_mem_iff ord_cl_memI1)
qed

lemma filters_on_lattice_bsup7:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_sup (filters_on X) {F1, F2} (binary_filter_sup X F1 F2) "
  by (simp add: filters_on_lattice_bsup5 filters_on_lattice_bsup6 is_supI5)

lemma filters_on_lattice_bsup8:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> Sup (filters_on X) {F1, F2} = (binary_filter_sup X F1 F2)"
  by (simp add: filters_on_lattice_bsup7 sup_equality)

lemma filters_on_lattice_bsup0:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (filter_closure X (F1 \<union> F2)) = Sup (filters_on X) {F1, F2}"
  using filters_on_lattice_sup_semilattice1b sup_equality by blast

lemma filters_on_lattice_bsup1:
  "\<lbrakk>is_lattice X;  is_filter X F1; is_filter X F2; z \<in> Sup (filters_on X) {F1, F2}\<rbrakk> \<Longrightarrow>(\<exists>Fx \<subseteq>(F1 \<union> F2). finite Fx \<and> Fx \<noteq> {} \<and> Inf X Fx \<le>z)"
  by (metis filterD1 filter_closure_obtains filters_on_lattice_bsup0 sup_bot.eq_neutr_iff)

lemma filters_on_lattice_bsup2:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and
          A3:"z \<in> Sup (filters_on X) {F1, F2}"
  shows "(\<exists>f1 \<in>F1. \<exists>f2 \<in> F2. Inf X {f1, f2} \<le>z)"
  by (metis A0 A1 A2 A3 filter_bsup_mem_iff filters_on_lattice_bsup8)


(*On a topped inf semilattice filters form a complete inf semilattice*)

lemma filters_on_top_inf_semilattice_is_cinf:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_cinf_semilattice (filters_on X)"
  apply(auto simp add:is_cinf_semilattice_def)
  using filters_is_clr1b apply auto[1]
  by (metis clatD22 clr_is_clattice filterD1 filter_is_clr filters_max0 pow_is_clattice)

(*On a topped inf semlattice filters form a complete complete lattice*)

lemma filters_on_top_inf_lattice_clattice:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_clattice (filters_on X)"
  by (metis clr_is_clattice empty_iff filter_is_clr greatestD11 pow_is_clattice)

lemma filters_clattice1:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X; EF \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> is_sup (filters_on X) EF (Sup (filters_on X) EF)"
  by (simp add: clatD21 filters_on_top_inf_lattice_clattice sup_exI)

lemma filters_clattice2:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X; EF \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> is_inf (filters_on X) EF (Inf (filters_on X) EF)"
  by (simp add: clatD22 filters_on_top_inf_lattice_clattice inf_exI)

(*
  "\<lbrakk>is_inf_semilattice X; is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_clr (filters_on X) (Pow X)"
  "\<lbrakk>is_inf_semilattice X; is_greatest X top\<rbrakk> \<Longrightarrow> is_cinf_semilattice (filters_on X)
  "\<lbrakk>is_lattice X\<rbrakk> \<Longrightarrow> is_csup_semilattice (filters_on X)"
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_clattice (filters_on X)"

*)

lemma lattice_filter_memI:
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F"
  by (simp add: filter_bsup_memI1 lattD42)

lemma lattice_filter_dunion1:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>)\<rbrakk> \<Longrightarrow> \<Union>D \<noteq> {} "
  by (simp add: is_filter_def filters_on_iff subset_iff)

lemma lattice_filter_dunion2:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>)\<rbrakk> \<Longrightarrow> is_ord_cl X (\<Union>D) (\<le>)"
  by (metis Pow_iff filterD2 filterD4 filters_on_iff is_ord_cl_un subset_iff)

lemma lattice_filter_dunion3:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk>
   \<Longrightarrow> (\<exists>Dx \<in> D. \<exists>Dy \<in> D. \<exists>Dxy \<in> D. x \<in> Dx \<and> y \<in> Dy \<and> Dx \<inter> Dy \<subseteq> Dxy)" by blast

lemma lattice_filter_dunion4:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. x\<in> Dxy \<and> y \<in> Dxy)"
  by (meson UnionE in_mono is_updirE1)

lemma lattice_filter_dunion5:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. Inf X {x, y} \<in> Dxy)"
  using lattice_filter_dunion4[of X D x y]  by (metis filter_finf_closed1 filters_on_iff in_mono lattD41)

lemma lattice_filter_dunion6:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in>  (\<Union>D)"
  by (simp add: lattice_filter_dunion5)

lemma lattice_filter_dunion7:
  "\<lbrakk>D \<noteq> {}; D \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> \<Union>D \<subseteq> X"
  by(auto simp add:filters_on_def is_filter_def)

lemma lattice_filter_dunion8:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>)\<rbrakk> \<Longrightarrow> is_dir (\<Union>D) (\<ge>)"
  by(rule is_dwdirI4, erule lattD41, erule lattice_filter_dunion7, simp, erule lattice_filter_dunion6, simp+)

lemma lattice_filter_dunion9:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>)\<rbrakk> \<Longrightarrow> is_filter X (\<Union>D)" 
  using  lattice_filter_dunion1[of X D] lattice_filter_dunion2[of X D] lattice_filter_dunion8[of X D]
  by (simp add: filterI1 lattice_filter_dunion7)

lemma lattice_filters_complete:
  "\<lbrakk>is_lattice X; is_greatest X top\<rbrakk> \<Longrightarrow> is_clattice (filters_on X)"
 by (simp add: filters_on_top_inf_lattice_clattice latt_iff)

lemma filters_inf_semilattice_inf:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); is_greatest X top\<rbrakk> \<Longrightarrow> is_inf (filters_on X) EF (\<Inter>EF)"
  by (metis filter_inter_closed2 filters_is_clr1 is_inf_semilattice_def pow_ne_iff2 uni_inf_fam)

lemma filters_lattice_inf:
  "\<lbrakk>is_lattice X; F1 \<in> filters_on X; F2 \<in> filters_on X\<rbrakk> \<Longrightarrow> is_inf (filters_on X) {F1 ,F2} (F1 \<inter> F2)"
  by (simp add: filters_on_iff filters_on_lattice_inf8b)

lemma filters_lattice_inf_op:
  "\<lbrakk>is_lattice X; F1 \<in> filters_on X; F2 \<in> filters_on X\<rbrakk> \<Longrightarrow>Inf (filters_on X) {F1, F2} = (F1 \<inter> F2)"
  by (simp add: filters_lattice_inf inf_equality)


definition lorc::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" ("(2[_')\<^sub>_)") where
  "lorc R X a \<equiv> {y \<in> X. a \<le> y} "

lemma lorcI1:
  "y \<in> X \<Longrightarrow> a \<le> y \<Longrightarrow> y \<in> lorc R X a" 
  by (simp add:lorc_def)

lemma lorcD1:
  "y \<in> lorc R X a \<Longrightarrow> y \<in> X \<and> a \<le> y"
   by (simp add:lorc_def)

lemma lorcD11:
  "y \<in> lorc R X a \<Longrightarrow> y \<in> X "
   by (simp add:lorc_def)

lemma lorcD12:
  "y \<in> lorc R X a \<Longrightarrow> a \<le> y" 
  by (simp add:lorc_def)

lemma lorcD2:"x \<in> X \<Longrightarrow> y \<in> lorc R X a \<Longrightarrow>  (y, x)\<in>R \<Longrightarrow> x \<in> lorc R X a"
  by(drule lorcD12, erule lorcI1, simp)

lemma lorcD3:
  "(\<exists>b. b \<le> x \<and> b \<in> lorc R X a) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> lorc R X a"
  using lorcD2 by blast

lemma lorc_mem_iff1:
  "y \<in> (lorc R X a) \<longleftrightarrow> (y \<in> X \<and> a \<le> y)" by (simp add:lorc_def)

lemma lorc_mem_iff2:
  "y \<in> (lorc R X a) \<longleftrightarrow> (y \<in> X \<and> y ub {a})" by (simp add:lorc_def ub_def)

lemma lorc_eq_upbd:
  "(lorc R X a) = (ubd R  X {a})"
  by(simp add: set_eq_iff ubd_mem_iff lorc_mem_iff2)

lemma lorc_eq_upbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. lorc R X a) = ubd R  X A"
  by(auto simp add:ubd_mem_iff2 lorc_mem_iff1)

lemma lorc_memI1:
  "a \<in> X \<Longrightarrow> a \<in> lorc R X a "
  by (simp add: lorcI1)

lemma lorc_mem_point1:
  "a \<in> X \<longleftrightarrow> a \<in> (lorc R X a)"
  by (simp add: lorc_def)

lemma lorc_subset1:
  "(lorc R X a) \<subseteq> X"
  by (simp add: ubd_sub lorc_eq_upbd)

lemma lorc_top:
  "is_greatest X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> lorc R X a"
  by (simp add: greatestD11 greatestD2 lorcI1)

lemma lorc_sup_latticeD1:
  "\<lbrakk>is_sup_semilattice R X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, y} \<in> ([x)\<^sub>X)"
  by (simp add: bsup_geI1 lorcI1 ssupD4)

lemma lorc_inf_latticeD1:
  "\<lbrakk>is_least X bot\<rbrakk> \<Longrightarrow> ([bot)\<^sub>X) = X"
  by(auto simp add: lorc_mem_iff1 least_iff)

lemma lorc_dual_iso:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (lorc R X a) \<subseteq> ([b)\<^sub>X)  \<longleftrightarrow> b \<le> a"
  by(auto simp add:lorc_mem_iff1) 

lemma lorc_upclI:
  "a \<in> X \<Longrightarrow> is_ord_cl X (lorc R X a) (\<le>)"
  by (simp add: is_ord_clI1 lorcD2)

lemma lorc_upclD:
  "U \<subseteq> X \<Longrightarrow> is_ord_cl X U (\<le>) \<Longrightarrow> is_least U x \<Longrightarrow> U = [x)\<^sub>X"
  apply (auto simp add: in_mono leastD2 lorcI1)
  by (meson is_ord_clE1 leastD11 lorcD1)

lemma lorc_upcl1:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. lorc R X a)"
  by (simp add: greatestD11 greatestD2 in_mono lorcI1)

lemma lorc_upcl3:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. lorc R X a) (\<le>)"
  by(rule is_ord_cl_in2, auto simp add: lorc_mem_iff1, simp add: in_mono lorc_upclI)
  
definition ord_cl_sets::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> 'a::order set set" where
  "ord_cl_sets X ord \<equiv> {A. A \<subseteq> X \<and> is_ord_cl X A (ord)}"

lemma lorc_upcl4:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> {m} \<in> ord_cl_sets X (\<le>)"
  by (simp add: filterD4 greatestD11 min_filter1 ord_cl_sets_def)

lemma lorc_moore:
  "\<lbrakk>is_greatest X m\<rbrakk> \<Longrightarrow> is_clr (ord_cl_sets X (\<le>)) (Pow X)"  
  apply(rule moore_clI3, auto simp add:ord_cl_sets_def is_ord_cl_space is_ord_cl_def)
   by blast

lemma lorc_is_clattice:
  "is_greatest X m \<Longrightarrow> is_clattice (ord_cl_sets X (\<le>))"
  using clr_is_clattice lorc_moore pow_is_clattice by blast

lemma lorc_filter:
  "x \<in> X \<Longrightarrow> is_filter X [x)\<^sub>X"
  apply(auto simp add:is_filter_def) using lorc_memI1 apply auto[1] 
  apply (simp add: lorc_mem_iff1) apply (metis is_dwdirI1 lorcD12 lorc_memI1)
  by (simp add: lorc_upclI)

lemma lorc_filter2:
  "x \<in> X \<Longrightarrow>  ([x)\<^sub>X) \<in> filters_on X"
  by (simp add: filters_on_iff lorc_filter)

lemma lorc_sup_superset:
  "\<lbrakk>is_lattice X; is_greatest X top; F \<subseteq> X\<rbrakk>  \<Longrightarrow> {y. \<exists>x \<in> F. y= ([x)\<^sub>X)} \<subseteq> filters_on X"
  by(auto simp add:subset_iff lorc_filter2)

lemma lorc_sup_superset2:
  "\<lbrakk>is_lattice X; is_greatest X top; F \<subseteq> X\<rbrakk> \<Longrightarrow> F \<subseteq> \<Union>{y. \<exists>x \<in> F. y= ([x)\<^sub>X)}"
   using lorc_memI1 by auto


lemma lorc_inter:
  "\<lbrakk>is_lattice X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (lorc R X a) \<inter> ([b)\<^sub>X) = [Sup R X {a, b})\<^sub>X"
  by(auto simp add: bsup_geI3 latt_iff lorc_mem_iff1 bsup_iff)
 

definition rolc::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" ("(2'(_]\<^sub>_)") where
  "(a]\<^sub>X \<equiv> {y \<in> X. y \<le> a} "

lemma rolcI1:
  "y \<in> X \<Longrightarrow> y \<le> a \<Longrightarrow> y \<in> (a]\<^sub>X" 
  by (simp add:rolc_def)

lemma rolcD1:
  "y \<in> (a]\<^sub>X \<Longrightarrow> y \<in> X \<and> y \<le> a"
   by (simp add:rolc_def)

lemma rolcD11:
  "y \<in> (a]\<^sub>X \<Longrightarrow> y \<in> X "
   by (simp add:rolc_def)

lemma rolcD12:
  "y \<in> (a]\<^sub>X \<Longrightarrow> y \<le> a" 
  by (simp add:rolc_def)

lemma rolcD2:"x \<in> X \<Longrightarrow> y \<in> (a]\<^sub>X \<Longrightarrow>  (x, y)\<in>R \<Longrightarrow> x \<in> (a]\<^sub>X"
  by(drule rolcD12, erule rolcI1, simp)

lemma rolcD3:
  "(\<exists>b. (x, b)\<in>R \<and> b \<in> (a]\<^sub>X) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> (a]\<^sub>X"
  using rolcD2 by blast

lemma rolc_mem_iff1:
  "y \<in> ((a]\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> y \<le> a)"
   by (simp add:rolc_def)

lemma rolc_mem_iff2:
  "y \<in> ((a]\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> y lb {a})" 
  by (simp add:rolc_def lb_def)

lemma rolc_memI1:
  "a \<in> X \<Longrightarrow> a \<in> (a]\<^sub>X "
  by (simp add: rolcI1)

lemma rolc_mem_point1:
  "a \<in> X \<longleftrightarrow> a \<in> ((a]\<^sub>X)"
  by (simp add: rolc_def)

lemma rolc_subset1:
  "((a]\<^sub>X) \<subseteq> X"
  by (simp add: rolc_def)

lemma rolc_dwclI:
  "a \<in> X \<Longrightarrow> is_ord_cl X ((a]\<^sub>X) (\<ge>)"
  by (simp add: is_ord_clI1 rolcD2)

lemma rolc_eq_lbd:
  "((a]\<^sub>X) = (lbd R X {a})"
  by(simp add: set_eq_iff lbd_mem_iff rolc_mem_iff2)

lemma rolc_eq_lbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. (a]\<^sub>X) = lbd R X A"
  by(auto simp add:lbd_mem_iff2 rolc_mem_iff1)

lemma rolc_top:
  "is_least X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> (a]\<^sub>X"
  by (simp add: leastD11 leastD2 rolcI1)

lemma rolc_inf_latticeD1:
  "\<lbrakk>is_inf_semilattice X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Inf X {x, y} \<in> ((x]\<^sub>X)"
  by (simp add: binf_leI1 rolcI1 sinfD4)

lemma rolc_sup_latticeD1:
  "\<lbrakk>is_greatest X top\<rbrakk> \<Longrightarrow> ((top]\<^sub>X) = X"
  by(auto simp add: rolc_mem_iff1 greatest_iff)

lemma rolc_iso:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ((a]\<^sub>X) \<subseteq> ((b]\<^sub>X)  \<longleftrightarrow> (a, b)\<in>R"
  by(auto simp add:rolc_mem_iff1) 

lemma rolc_dwclD:
  "U \<subseteq> X \<Longrightarrow> is_ord_cl X U (\<ge>) \<Longrightarrow> is_greatest U x \<Longrightarrow> U = (x]\<^sub>X"
  apply (auto simp add: greatestD2 in_mono rolcI1)
  using greatestD11 ord_cl_memI1 rolcD11 rolcD12 by blast

lemma rolc_dwcl1:
  "\<lbrakk>is_least X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. (a]\<^sub>X)"
  by (simp add: least_iff rolcI1 subset_iff)

lemma rolc_upcl3:
  "\<lbrakk>is_least X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. (a]\<^sub>X) (\<ge>)"
  by(rule is_ord_cl_in2, auto simp add:rolc_mem_iff1 in_mono rolc_dwclI)

subsection UpDwClosure
subsubsection UpClosure

definition up_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "up_cl X A = {x \<in> X. \<exists>a \<in> A. (a, x) \<in> R}"

lemma up_cl_mem_iff:
  "x \<in> up_cl X A \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. (a, x) \<in> R))"
  by (simp add: up_cl_def)

lemma up_cl_memD1:
  "x \<in> up_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: up_cl_def)

lemma up_cl_memD2:
  "x \<in> up_cl X A \<Longrightarrow> \<exists>a \<in> A. (a, x) \<in> R"
  by (simp add: up_cl_def)

lemma up_cl_memI1:
  "x \<in> X \<Longrightarrow> a \<in> A \<Longrightarrow> (a, x) \<in> R \<Longrightarrow> x \<in> up_cl X A"
   using up_cl_def by auto 

lemma up_cl_memI2:
  "x \<in> X \<Longrightarrow> (\<exists>a \<in> A. (a, x) \<in> R) \<Longrightarrow> x \<in> up_cl X A"
  by (simp add: up_cl_mem_iff)

lemma up_cl_sub1:
  "A \<subseteq> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> up_cl X A"
  by (simp add: subsetD up_cl_memI1)

lemma up_cl_sub2:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq>  up_cl X A"
  by (simp add: subsetI up_cl_sub1)

lemma up_cl_sub3:
  "up_cl X A \<subseteq> X"
  by (simp add: subsetI up_cl_memD1)

lemma up_cl_iso1:
  "A \<subseteq> B \<Longrightarrow> up_cl X A \<subseteq> up_cl X B"
  by (meson in_mono subsetI up_cl_memD1 up_cl_memD2 up_cl_memI1)

lemma up_cl_idem1:
  "x \<in> up_cl X (up_cl X A) \<Longrightarrow> x \<in> up_cl X A"
  by (meson dual_order.trans up_cl_mem_iff)

lemma up_cl_idem2:
  " up_cl X (up_cl X A) \<subseteq> up_cl X A"
  by (simp add: subsetI up_cl_idem1)

lemma up_cl_idem3:
  " up_cl X (up_cl X A) = up_cl X A"
  by (simp add: subset_antisym up_cl_idem2 up_cl_sub2 up_cl_sub3)

lemma up_cl_singleton:
  "x \<in> up_cl X {a}  \<longleftrightarrow> (x \<in> X \<and> (a, x) \<in> R)"
  by (simp add: up_cl_mem_iff)

lemma up_cl_lorc:
  "up_cl X {a} = lorc R X a"
  by (simp add: lorc_mem_iff1 set_eq_iff up_cl_singleton)

lemma up_cl_ext:
  "extensive (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_extensive_def up_cl_sub2)

lemma up_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_isotone_def up_cl_iso1)

lemma up_cl_idem:
  "idempotent (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: idempotent_def up_cl_idem3)

lemma up_cl_cl:
  "closure (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: image_subsetI closure_def up_cl_ext up_cl_idem up_cl_iso up_cl_sub3)

lemma up_cl_memI3:
  "\<And>a b. \<lbrakk>a \<in> (up_cl X A); b \<in> X; (a, b)\<in>R\<rbrakk> \<Longrightarrow> b \<in> (up_cl X A)"
  using up_cl_idem3 up_cl_memI1 by blast

lemma up_cl_is_up_cl:
  "is_ord_cl X (up_cl X A) (\<le>)"
  by (simp add: is_ord_clI1 up_cl_memI3)

lemma dwdir_upcl_is_dwdir:
  assumes A0:"is_dir A (\<ge>)" and A1:"A \<subseteq> X"
  shows "is_dir (up_cl X A) (\<ge>)"
proof-
  have B0:"\<And>a b.  a \<in> up_cl X A \<and> b \<in> up_cl X A \<longrightarrow> (\<exists>c\<in>up_cl X A. c \<le> a \<and> c \<le> b)"
  proof
    fix a b assume A2:"a \<in> up_cl X A \<and> b \<in> up_cl X A"
    obtain a1 b1 where B1:"a1 \<in> A \<and> b1 \<in> A \<and> a1 \<le> a \<and> b1 \<le> b"  by (meson A2 up_cl_memD2)
    obtain c where B2:"c \<in> A \<and> c \<le> a1 \<and> c \<le> b1" using A0 B1 is_dwdirE1 by blast
    have B3:"c \<in> up_cl X A \<and> c \<le> a \<and> c \<le> b" by (metis A1 B1 B2 dual_order.trans up_cl_sub1)
    show "\<exists>c\<in>up_cl X A. c \<le> a \<and> c \<le> b"
      using B3 by auto
  qed
  show ?thesis
    by (simp add: B0 is_dwdirI1)
qed

lemma upcl_dwdir_is_dwdir:
  assumes A0:"is_dir (up_cl X A) (\<ge>)" and A1:"A \<subseteq> X"
  shows "is_dir A (\<ge>)"
proof-
  have B0:" \<And>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>c\<in>A. c \<le> a \<and> c \<le> b)"
  proof
    fix a b assume A2:"a \<in> A \<and> b \<in> A"
    have B1:"a \<in> up_cl X A \<and> b \<in> up_cl X A" by (simp add: A1 A2 up_cl_sub1)
    obtain c where B2:"c \<in> up_cl X A \<and> c \<le> a \<and> c \<le> b"  using A0 B1 is_dwdirE1 by blast
    obtain d where B3:"d \<in> A \<and> d \<le> c" using B2 up_cl_memD2 by blast
    have B4:"d \<in> A \<and> d \<le> a \<and> d \<le> b" using B2 B3 order.trans by blast
    show "\<exists>c\<in>A. c \<le> a \<and> c \<le> b" using B4 by auto
  qed
  show ?thesis
    by (simp add: B0 is_dwdirI1)
qed


subsubsection DownClosure
definition dw_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "dw_cl X A = {x \<in> X. \<exists>a \<in> A. x \<le> a}"

lemma dw_cl_mem_iff:
  "x \<in> dw_cl X A \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. x \<le> a))"
  by (simp add: dw_cl_def)

lemma dw_cl_memD1:
  "x \<in> dw_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: dw_cl_def)

lemma dw_cl_memD2:
  "x \<in> dw_cl X A \<Longrightarrow> \<exists>a \<in> A. x \<le> a"
  by (simp add: dw_cl_def)

lemma dw_cl_memI1:
  "x \<in> X \<Longrightarrow> a \<in> A \<Longrightarrow> x \<le> a \<Longrightarrow> x \<in> dw_cl X A"
  using dw_cl_def by auto

lemma dw_cl_memI2:
  "x \<in> X \<Longrightarrow> (\<exists>a \<in> A. x \<le> a) \<Longrightarrow> x \<in> dw_cl X A"
  by (simp add: dw_cl_mem_iff)

lemma dw_cl_sub1:
  "A \<subseteq> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> dw_cl X A"
  by (simp add: subsetD dw_cl_memI1)

lemma dw_cl_sub2:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> dw_cl X A"
  by (simp add: subsetI dw_cl_sub1)

lemma dw_cl_sub3:
  "dw_cl X A \<subseteq> X"
  by (simp add: subsetI dw_cl_memD1)

lemma dw_cl_iso1:
  "A \<subseteq> B \<Longrightarrow> dw_cl X A \<subseteq> dw_cl X B"
  by (meson in_mono subsetI dw_cl_memD1 dw_cl_memD2 dw_cl_memI1)

lemma dw_cl_idem1:
  "x \<in> dw_cl X (dw_cl X A) \<Longrightarrow> x \<in> dw_cl X A"
  by (meson order.trans dw_cl_mem_iff)

lemma dw_cl_idem2:
  "dw_cl X (dw_cl X A) \<subseteq> dw_cl X A"
  by (simp add: subsetI dw_cl_idem1)

lemma dw_cl_idem3:
  "dw_cl X (dw_cl X A) = dw_cl X A"
  by (simp add: subset_antisym dw_cl_idem2 dw_cl_sub2 dw_cl_sub3)

lemma dw_cl_lorc:
  "dw_cl X {a} = (a]\<^sub>X"
  by (simp add: set_eq_iff rolc_mem_iff1 dw_cl_mem_iff)

lemma dw_cl_ext:
  "extensive (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_extensive_def dw_cl_sub2)

lemma dw_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_isotone_def dw_cl_iso1)

lemma dw_cl_idem:
  "idempotent (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: idempotent_def dw_cl_idem3)

lemma dw_cl_cl:
  "closure (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: image_subsetI closure_def dw_cl_ext dw_cl_idem dw_cl_iso dw_cl_sub3)

lemma dw_cl_memI3:
  "\<And>a b. \<lbrakk>a \<in> (dw_cl X A); b \<in> X; a \<ge> b\<rbrakk> \<Longrightarrow> b \<in> (dw_cl X A)"
  using dw_cl_idem3 dw_cl_memI1 by blast

lemma dw_cl_is_dw_cl:
  "is_ord_cl X (dw_cl X A) (\<ge>)"
  by (simp add: is_ord_clI1 dw_cl_memI3)


lemma updir_dwcl_is_updir:
  assumes A0:"is_dir A (\<le>)" and A1:"A \<subseteq> X"
  shows "is_dir (dw_cl X A) (\<le>)"
proof-
  have B0:"\<And>a b.  a \<in> dw_cl X A \<and> b \<in> dw_cl X A \<longrightarrow> (\<exists>c\<in>dw_cl X A. (a, c)\<in>R \<and> (b, c)\<in>R)"
  proof
    fix a b assume A2:"a \<in> dw_cl X A \<and> b \<in> dw_cl X A"
    obtain a1 b1 where B1:"a1 \<in> A \<and> b1 \<in> A \<and> a1 \<ge> a \<and> b1 \<ge> b"  by (meson A2 dw_cl_memD2)
    obtain c where B2:"c \<in> A \<and> c \<ge> a1 \<and> c \<ge> b1" using A0 B1 is_updirE1 by blast
    have B3:"c \<in> dw_cl X A \<and> (a, c)\<in>R \<and> (b, c)\<in>R" by (metis A1 B1 B2 dual_order.trans dw_cl_sub1)
    show "\<exists>c\<in>dw_cl X A. (a, c)\<in>R \<and> (b, c)\<in>R"
      using B3 by auto
  qed
  show ?thesis
    by (simp add: B0 is_updirI1)
qed

lemma dwcl_updir_is_updir:
  assumes A0:"is_dir (dw_cl X A) (\<le>)" and A1:"A \<subseteq> X"
  shows "is_dir A (\<le>)"
proof-
  have B0:" \<And>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>c\<in>A. (a, c)\<in>R \<and> (b, c)\<in>R)"
  proof
    fix a b assume A2:"a \<in> A \<and> b \<in> A"
    have B1:"a \<in> dw_cl X A \<and> b \<in> dw_cl X A" by (simp add: A1 A2 dw_cl_sub1)
    obtain c where B2:"c \<in> dw_cl X A \<and> (a, c)\<in>R \<and> (b, c)\<in>R"  using A0 B1 is_updirE1 by blast
    obtain d where B3:"d \<in> A \<and> d \<ge> c" using B2 dw_cl_memD2 by blast
    have B4:"d \<in> A \<and> d \<ge> a \<and> d \<ge> b" using B2 B3 order.trans by blast
    show "\<exists>c\<in>A. (a, c)\<in>R \<and> (b, c)\<in>R" using B4 by auto
  qed
  show ?thesis
    by (simp add: B0 is_updirI1)
qed



definition galois_conn::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "galois_conn f X g Y \<equiv> (f`X \<subseteq> Y) \<and> (g`Y \<subseteq> X) \<and> (\<forall>x \<in> X. \<forall>y \<in> Y.  (x \<le> g y \<longleftrightarrow> y \<le> f x))"

lemma galois_connD11:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<le>  g y \<Longrightarrow> y \<le> f x"
   by (simp add:galois_conn_def)

lemma galois_connD21:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> f x \<Longrightarrow> x \<le> g y" 
  by (simp add:galois_conn_def)

lemma galois_connD12:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y \<in> X" 
  by (simp add:galois_conn_def image_subset_iff)

lemma galois_connD22:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X  \<Longrightarrow> f x \<in> Y" 
  by (simp add:galois_conn_def image_subset_iff)

lemma galois_connD3:
  "galois_conn f X g Y \<Longrightarrow> A \<subseteq> X \<Longrightarrow> f`A \<subseteq> Y"
  using galois_connD22 by blast

lemma gc_cext1:
  "\<lbrakk>galois_conn f X g Y; x \<in> X\<rbrakk> \<Longrightarrow> x \<le> g (f x) "
  by(simp add: galois_connD22[of f X g Y x] galois_connD21[of f X g Y x "f x"])

lemma gc_cext2:
  "\<lbrakk>galois_conn f X g Y; y \<in> Y\<rbrakk> \<Longrightarrow> y \<le> f (g y) "
  by(simp add: galois_connD12[of f X g Y "y"] galois_connD11[of f X g Y "g y" y])

lemma gc_anti1:
  "\<lbrakk>galois_conn f X g Y; x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> f x2 \<le> f x1 "
  by(simp add:gc_cext1[of f X g Y x2]  galois_connD11[of f X g Y x1 "f x2"] galois_connD22[of f X g Y x2] order.trans)

lemma gc_anti2:
  "\<lbrakk>galois_conn f X g Y; y1 \<in> Y; y2 \<in> Y; y1 \<le> y2\<rbrakk> \<Longrightarrow> g y2 \<le> g y1 "
  by(simp add:gc_cext2[of f X g Y y2]  galois_connD21[of f X g Y "g y2" y1]  galois_connD12[of f X g Y y2] order.trans)

definition is_antitone::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "is_antitone X f \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. x1 \<le> x2 \<longrightarrow> f x2 \<le> f x1)"

lemma antitoneD:
  "\<lbrakk>is_antitone X f; x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> f x2 \<le> f x1"
  by (simp add:is_antitone_def)

lemma anti_ext_gc:
  "\<lbrakk>is_antitone Y g; extensive X (g \<circ> f); f x \<in> Y; g`Y \<subseteq> X; x \<in> X; y \<in> Y; y \<le> f x \<rbrakk> \<Longrightarrow> x \<le> g y"
  using antitoneD[of Y g y "f x"] extensiveD1[of X "(g \<circ> f)" x] order.trans by simp

lemma gcI:
  "\<lbrakk>is_antitone X f; extensive X (g \<circ> f);
      is_antitone Y g;  extensive Y (f \<circ> g); 
        f`X \<subseteq> Y; g`Y \<subseteq> X \<rbrakk> \<Longrightarrow>  galois_conn f X g Y"
  by(auto simp add:galois_conn_def anti_ext_gc)

lemma gcD:
  "galois_conn f X g Y \<Longrightarrow>is_antitone X f \<and> extensive X (g \<circ> f) \<and>
                           is_antitone Y g \<and>  extensive Y (f \<circ> g) \<and> f`X \<subseteq> Y \<and> g`Y \<subseteq> X"
  by (simp add: galois_conn_def gc_anti1 gc_anti2 gc_cext1 gc_cext2 is_antitone_def is_extensive_def)

lemma gc_triple1:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> f (g (f x)) = f x"
  by (simp add: dual_order.eq_iff galois_connD12 galois_connD22 gc_anti1 gc_cext1 gc_cext2)

lemma gc_triple2:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g (f (g y)) =g y"
  by (simp add: antisym galois_connD12 galois_connD22 gc_anti2 gc_cext1 gc_cext2)

lemma gc_idem1a:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> g (f ( g (f x) ) ) = g (f x)"
  by (simp add: gc_triple1)

lemma gc_idem1b:
  "galois_conn f X g Y \<Longrightarrow> idempotent X (g \<circ> f)"
  by (simp add: gc_idem1a idempotent_def)

lemma gc_idem2a:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> f (g ( f (g y) ) ) = f (g y)"
  by (simp add: gc_triple2)

lemma gc_idem2b:
  "galois_conn f X g Y \<Longrightarrow> idempotent Y (f \<circ> g)"
  by (simp add: gc_idem2a idempotent_def)

lemma gc_iso1a:
  "galois_conn f X g Y \<Longrightarrow> x1 \<in> X \<Longrightarrow>x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> g (f x1 ) \<le> g (f x2)"
  by (simp add: galois_connD22 gc_anti1 gc_anti2)

lemma gc_iso1b:
  "galois_conn f X g Y \<Longrightarrow> is_isotone X (g \<circ> f)"
  by (simp add: gc_iso1a  is_isotone_def)

lemma gc_iso2a:
  "galois_conn f X g Y \<Longrightarrow> y1 \<in> Y \<Longrightarrow>y2 \<in> Y \<Longrightarrow>y1 \<le> y2 \<Longrightarrow> f (g y1 ) \<le> f (g y2)"
  by (simp add: galois_connD12 gc_anti1 gc_anti2)

lemma gc_iso2b:
  "galois_conn f X g Y \<Longrightarrow> is_isotone Y (f \<circ> g)"
  by (simp add: gc_iso2a  is_isotone_def)
   
lemma gc_ext1:
  "galois_conn f X g Y \<Longrightarrow> extensive X (g \<circ> f)"
  by (simp add: gcD)

lemma gc_ext2:
  "galois_conn f X g Y \<Longrightarrow> extensive Y (f \<circ> g)"
  by (simp add: gcD)
    
lemma gc_sub1:
  "galois_conn f X g Y \<Longrightarrow>(\<lambda>x.  g (f x)) ` X \<subseteq> X"
  by (simp add: galois_connD12 galois_connD22 image_subset_iff)       
    
lemma gc_sub2:
  "galois_conn f X g Y \<Longrightarrow>(\<lambda>y. f (g y)) ` Y \<subseteq> Y"
  by (simp add: galois_connD12 galois_connD22 image_subset_iff)       

lemma gc_closure1:
  "galois_conn f X g Y \<Longrightarrow> closure X (g \<circ> f)"
  by (simp add: closure_def gc_sub1 gc_ext1 gc_iso1b gc_idem1b)

lemma gc_closure2:
  "galois_conn f X g Y \<Longrightarrow> closure Y (f \<circ> g)"
  by (simp add: closure_def gc_sub2 gc_ext2 gc_iso2b gc_idem2b)

lemma ul_galois:
  "galois_conn (\<lambda>A. ubd R  X A) (Pow X) (\<lambda>A. lbd R X A) (Pow X)"
  apply(rule gcI) 
  apply(simp add: ubd_ant1 is_antitone_def)
  apply(simp add: lubd_comp1 is_extensive_def)
  apply(simp add: lbd_ant1 is_antitone_def)
  apply(simp add: ulbd_comp1 is_extensive_def)
  apply (simp add: ubd_sub image_subset_iff)
  by (simp add: lbd_sub image_subset_iff)

lemma ul_closure:
  "closure (Pow X) ((\<lambda>A. ubd R  X A) \<circ> (\<lambda>A. lbd R X A))"
  using gc_closure2 ul_galois by blast

lemma lu_closure:
  "closure (Pow X) ((\<lambda>A. lbd R X A) \<circ> (\<lambda>A. ubd R  X A))"
  using gc_closure1 ul_galois by blast

subsection PolarPairs

definition lgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a set \<Rightarrow> 'b set)" where
  "lgc_from_rel R X Y \<equiv> (\<lambda>A. {y. y \<in> Y \<and> (\<forall>x. x \<in> A \<longrightarrow> (x, y) \<in> R)})"

definition rgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b set \<Rightarrow> 'a set)" where
  "rgc_from_rel R X Y \<equiv> (\<lambda>B. {x. x \<in> X \<and> (\<forall>y. y \<in> B \<longrightarrow> (x, y) \<in> R)})"

lemma lcgD1:
  "\<lbrakk>A \<subseteq> X; y \<in> (lgc_from_rel R X Y) A\<rbrakk> \<Longrightarrow> (\<forall>x \<in> A.  (x, y) \<in> R)"
  by (simp add: lgc_from_rel_def)

lemma rcgD1:
  "\<lbrakk>B \<subseteq> Y; x \<in> (rgc_from_rel R X Y) B\<rbrakk> \<Longrightarrow> (\<forall>y \<in> B.  (x, y) \<in> R)"
  by (simp add: rgc_from_rel_def)

lemma lcg_iff:
  "\<lbrakk>A \<subseteq> X\<rbrakk> \<Longrightarrow> y \<in> (lgc_from_rel R X Y) A \<longleftrightarrow> (y \<in> Y \<and> (\<forall>x \<in> A.  (x, y) \<in> R))"
   by (auto simp add: lgc_from_rel_def)

lemma rcg_iff:
  "\<lbrakk>B \<subseteq> Y\<rbrakk> \<Longrightarrow> x \<in> (rgc_from_rel R X Y) B \<longleftrightarrow> (x \<in> X \<and> (\<forall>y \<in> B.  (x, y) \<in> R))"
   by (auto simp add: rgc_from_rel_def)

lemma lcg_iff2:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y; y \<in> B\<rbrakk> \<Longrightarrow> y \<in> (lgc_from_rel R X Y) A \<longleftrightarrow> (\<forall>x \<in> A.  (x, y) \<in> R)"
   by (auto simp add: lgc_from_rel_def)

lemma rcg_iff2:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y; x \<in> A\<rbrakk> \<Longrightarrow> x \<in> (rgc_from_rel R X Y) B \<longleftrightarrow> (\<forall>y \<in> B.  (x, y) \<in> R)"
  by (simp add: in_mono rcg_iff)

lemma lcg_iff3:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y\<rbrakk>  \<Longrightarrow> (\<forall>b \<in> B. b \<in> lgc_from_rel R X Y A) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B.(a, b) \<in> R)"
  by (meson lcg_iff2)
  
lemma rcg_iff3:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y\<rbrakk>  \<Longrightarrow> (\<forall>a \<in> A. a \<in> rgc_from_rel R X Y B) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B.(a, b) \<in> R)"
  by (meson rcg_iff2)

lemma rcg_range1:
  "B \<subseteq> Y \<Longrightarrow>  rgc_from_rel R X Y B \<subseteq> X"
  by (meson rcg_iff subset_eq)
  
lemma rcg_range2:
  "(rgc_from_rel R X Y)`(Pow Y) \<subseteq> Pow X"
  by (simp add: image_subset_iff rcg_range1)
  
lemma lcg_range1:
  "A \<subseteq> X \<Longrightarrow>  lgc_from_rel R X Y A \<subseteq> Y"
  by (meson lcg_iff subset_eq)
  
lemma lcg_range2:
  "(lgc_from_rel R X Y)`(Pow X) \<subseteq> Pow Y"
  by (simp add: image_subset_iff lcg_range1)
  
subsection PolarPairToGalois


lemma gc1_to_gc2:
  assumes A0:"B \<subseteq> Y" and A1:"A \<subseteq> X" 
  shows "B \<subseteq> (lgc_from_rel R X Y) A  \<longleftrightarrow> A \<subseteq> (rgc_from_rel R X Y) B" (is "?L \<longleftrightarrow> ?R")
proof-
  let ?f="(lgc_from_rel R X Y)" and ?g="(rgc_from_rel R X Y)"
  have B0:"?L  \<longleftrightarrow> (\<forall>b. b \<in> B \<longrightarrow> b \<in> ?f A)" by auto
  have B1:"... \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B.(a, b) \<in> R)" by (meson A0 A1 in_mono lcg_iff)
  have B2:"... \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> a \<in> ?g B)" by (meson A0 A1 in_mono rcg_iff) 
  have B3:"... \<longleftrightarrow> ?R" by (simp add: subset_iff)
  show "?L \<longleftrightarrow> ?R"
    using B0 B1 B2 B3 by presburger
qed

lemma polar_pair_gc:
  "galois_conn (lgc_from_rel R X Y) (Pow X) (rgc_from_rel R X Y) (Pow Y)"
  by (simp add: galois_conn_def gc1_to_gc2 lcg_range2 rcg_range2)
  

subsubsection RecoveryOfOriginalRelation

definition rel_from_pair::"('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('b set \<Rightarrow> 'a set) \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
  "rel_from_pair f X g Y \<equiv> {(x, y). (x, y) \<in> (X \<times> Y) \<and> y \<in> f {x}}"

lemma gc_polar_pair:
  assumes A0:"(x, y) \<in> (X \<times> Y)"
  shows "(x, y) \<in> rel_from_pair (lgc_from_rel R X Y) X  (rgc_from_rel R X Y) Y \<longleftrightarrow>  (x, y) \<in> R" (is "?L \<longleftrightarrow> ?R")
proof-
  let ?f="(lgc_from_rel R X Y)" and ?g="(rgc_from_rel R X Y)" let ?GFR=" rel_from_pair ?f X  ?g Y"
  have B0:"?L \<longleftrightarrow> y \<in> ?f {x}"  using A0 by(auto simp add:lgc_from_rel_def rel_from_pair_def rgc_from_rel_def)
  have B1:"... \<longleftrightarrow> ?R"  using A0 by(auto simp add:lgc_from_rel_def)
  show ?thesis
    by (simp add: B0 B1)
qed
  
subsubsection GaloisToPolar

lemma gc_to_polar0:
  "galois_conn f (Pow X) g (Pow Y) \<Longrightarrow> a \<in> X \<Longrightarrow> y \<in> Y  \<Longrightarrow>  {y} \<subseteq> f {a} \<longleftrightarrow> {a} \<subseteq> g {y}"
  by (meson Pow_bottom Pow_iff galois_connD11 galois_connD21 insert_subsetI)

lemma gc_to_polar1:
  assumes A0:"galois_conn f (Pow X) g (Pow Y)" and A1:"A \<subseteq> X" and A2:"y \<in> Y"
  shows "y \<in> (lgc_from_rel (rel_from_pair f X g Y) X Y) A \<longleftrightarrow> y \<in> f A" (is "?LHS \<longleftrightarrow> ?RHS")
proof-
  have B0:"\<forall>a \<in> A.  {y} \<subseteq> f {a} \<longleftrightarrow> {a} \<subseteq> g {y}"
    by (meson A0 A1 A2 gc_to_polar0 in_mono)  
  let ?R="rel_from_pair f X g Y" let ?f="lgc_from_rel ?R X Y" let ?g="rgc_from_rel ?R X Y"
  have B0:"?LHS \<longleftrightarrow> (\<forall>a \<in> A. (a, y) \<in> ?R)" by (simp add: A1 A2 lcg_iff)
  have B1:"...  \<longleftrightarrow> (\<forall>a \<in> A.  y \<in> f {a})" using A1 A2 by(auto simp add:rel_from_pair_def)
  have B2:"...  \<longleftrightarrow> (\<forall>a \<in> A.  {y} \<subseteq> f {a})" by simp
  have B3:"...  \<longleftrightarrow> (\<forall>a \<in> A. {a} \<subseteq> g {y})" by (meson A0 A1 A2 gc_to_polar0 subsetD)
  have B4:"...  \<longleftrightarrow> (A \<subseteq> g {y})" by blast
  have B5:"...  \<longleftrightarrow> y \<in>  f A" by (meson A0 A1 A2 PowD PowI Pow_bottom galois_connD11 galois_connD21 insert_subset)
  show "?LHS \<longleftrightarrow> ?RHS"
    using B0 B1 B2 B3 B4 B5 by presburger
qed

subsubsection ThisIsAMess

lemma gc_sup_lb1:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> f s lb f`A"
  by (simp add: gc_anti1 is_supE1 is_supE7 lb_imageI subsetD)

lemma gc_sup_lb2:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_sup Y B s\<rbrakk> \<Longrightarrow> g s lb g`B"
  by (simp add: gc_anti2 is_supE1 is_supE7 lb_imageI subsetD)

lemma gc_reverse1:
  "\<lbrakk>galois_conn f X g Y;y \<in> Y; A \<subseteq> X; y lb f`A\<rbrakk> \<Longrightarrow> g ub R A y"
  by (simp add: galois_conn_def in_mono lbE ub_def)

lemma gc_reverse11:
  "\<lbrakk>galois_conn f X g Y; x \<in> X; B \<subseteq> Y; x lb g`B\<rbrakk> \<Longrightarrow> fub R B x"
  by (meson gcD gcI gc_reverse1)

lemma gc_reverse2:
  "\<lbrakk>galois_conn f X g Y;y \<in> Y; A \<subseteq> X; g ub R A y\<rbrakk> \<Longrightarrow> y lb f`A"
  by (simp add: galois_connD11 in_mono lb_imageI ubE)

lemma gc_reverse21:
  "\<lbrakk>galois_conn f X g Y; x \<in> X; B \<subseteq> Y; fub R B x\<rbrakk> \<Longrightarrow> x lb g`B"
  by (simp add: galois_connD21 in_mono lb_imageI ub_def)

lemma gc_sup_inf11:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; y \<in> Y; is_inf Y (f`A) i; is_sup R X A s;y \<le> i\<rbrakk> \<Longrightarrow> y \<le> f s"
  by (simp add: galois_connD11 galois_connD12 gc_reverse1 is_infE6 is_supE1 is_supE4)

lemma gc_sup_inf12:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; x \<in> X; is_inf X (g`B) i; is_sup Y B s; x \<le> i\<rbrakk> \<Longrightarrow> x \<le> g s"
  by (simp add: galois_connD21 galois_connD22 gc_reverse11 is_infE6 is_supE1 is_supE4)

lemma gc_sup_inf21:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; y \<in> Y; is_inf Y (f`A) i; is_sup R X A s; y \<le> f s\<rbrakk> \<Longrightarrow> y \<le> i"
  by (meson gc_sup_lb1 is_infD42 lb_iso1)

lemma gc_sup_inf22:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; x \<in> X; is_inf X (g`B) i; is_sup Y B s; x \<le> g s\<rbrakk> \<Longrightarrow> x \<le> i"
  by (meson gc_sup_lb2 is_infE4 lb_iso1)

lemma gc_sup_inf31:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_inf Y (f`A) i; is_sup R X A s\<rbrakk> \<Longrightarrow> (\<forall>y \<in> Y. y \<le> i \<longleftrightarrow> y \<le> f s)"
  by (meson gc_sup_inf11 gc_sup_inf21)

lemma gc_sup_inf32:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_inf X (g`B) i; is_sup Y B s\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. x \<le> i \<longleftrightarrow> x \<le> g s)"
  by (meson gc_sup_inf12 gc_sup_inf22)

lemma gc_sup_inf41:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_inf Y (f`A) i; is_sup R X A s\<rbrakk> \<Longrightarrow>f s = i"
  by(rule leq_iff_leq_eq, erule galois_connD22, erule is_supE1, erule is_infE1, simp add: gc_sup_inf31)

lemma gc_sup_inf42:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_inf X (g`B) i; is_sup Y B s\<rbrakk> \<Longrightarrow>g s = i"
  by(rule leq_iff_leq_eq, erule galois_connD12, erule is_supE1, erule is_infE1, simp add: gc_sup_inf32)

lemma gc_sup_inf:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; A \<subseteq> X\<rbrakk> \<Longrightarrow> Inf Y (f`A) = f (Sup X A)"
  using gc_sup_inf41[of f X g Y A "Inf Y (f`A)" "Sup X A"]  by (metis clatD21 clatD22 galois_connD3 inf_exI sup_equality)

lemma gc_inf_sup:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; B \<subseteq> Y\<rbrakk> \<Longrightarrow> Inf X (g`B) = g (Sup Y B)"
  using gc_sup_inf42[of f X g Y B "Inf X (g`B)" "Sup Y B"]
  by (metis (no_types, opaque_lifting) clatD21 clatD22 dual_order.trans galois_conn_def image_mono inf_exI sup_equality)

definition extrema_dual::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> 'b::order set  \<Rightarrow> bool" where
  "extrema_dual f X Y \<equiv>(\<forall>A. A \<subseteq> X \<longrightarrow> f (Sup X A) = Inf Y (f`A))"

definition dual_adj::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order)" where
  "dual_adj f X Y \<equiv> (\<lambda>y. Sup X {x \<in> X. y \<le> f x})"

lemma gc_extrema_dual:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; A \<subseteq> X\<rbrakk> \<Longrightarrow> extrema_dual f X Y"
  by (simp add: extrema_dual_def gc_sup_inf)

lemma gc_extrema_dual2:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; A \<subseteq> X\<rbrakk> \<Longrightarrow> extrema_dual g Y X"
  by (simp add: extrema_dual_def gc_inf_sup)


lemma extrema_dual_antitone1:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"x1 \<in> X \<and> x2 \<in> X" and A3:"x1 \<le> x2" and A4:"is_lattice X" "is_lattice Y"
  shows "f x2 \<le> f x1"
proof-
  have B0:"f x2 = f (Sup X {x1, x2})" by (simp add: A2 A3 ge_sup1)
  have B1:"...  = Inf Y (f`{x1, x2})" by (meson A0 A2 empty_subsetI extrema_dual_def insert_subsetI)
  have B2:"...  = Inf Y {f x1, f x2}" by simp
  have B3:"...  \<le> f x1"
    by (metis A1 A2 B0 B1 B2 assms(6) imageI in_mono lattD41 le_binf2)
  show ?thesis
    using B0 B1 B2 B3 by presburger
qed

lemma extrema_dual_antitone1b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_lattice X; is_lattice Y\<rbrakk> \<Longrightarrow> is_antitone X f"
  by (simp add: extrema_dual_antitone1 is_antitone_def)

lemma extrema_dual_antitone1c:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_antitone X f"
  by (simp add: clat_lattice extrema_dual_antitone1b)

lemma extrema_dual_adj_antitone2:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"y1 \<in> Y \<and> y2 \<in> Y" and A3:"y1 \<le> y2" and
          A4:"is_clattice X" "is_clattice Y"
  shows "(dual_adj f X Y) y2 \<le> (dual_adj f X Y) y1"
proof-
  have B0:"{x \<in> X. y2 \<le> f x} \<subseteq> {x \<in> X. y1 \<le> f x}"
    using A3 by force
  have B1:"(dual_adj f X Y) y2 = Sup X {x \<in> X. y2 \<le> f x}" by (simp add: dual_adj_def)
  have B2:"...                 \<le> Sup X {x \<in> X. y1 \<le> f x}" by (simp add: B0 assms(5) sup_iso1)
  have B3:"...                 = (dual_adj f X Y) y1"  by (simp add: dual_adj_def)
  show ?thesis
    by (simp add: B2 dual_adj_def)
qed

lemma extrema_dual_antitone2b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_antitone Y (dual_adj f X Y)"
  by (simp add: extrema_dual_adj_antitone2 is_antitone_def)

lemma extrema_dual_cext1:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"x \<in> X" and A4:"is_clattice X" "is_clattice Y"
  shows "x \<le> (dual_adj f X Y) (f x)"
  apply(auto simp add:dual_adj_def)
  by (metis (no_types, lifting) A2 assms(4) clatD21 dual_order.refl is_supD1121 mem_Collect_eq subsetI sup_equality)

lemma extrema_dual_cext1b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> extensive X ((dual_adj f X Y) \<circ> f)"
  by (simp add: extensiveI1 extrema_dual_cext1)

lemma im_le2:
  "f`X \<subseteq> Y \<Longrightarrow> y lb f`{x \<in> X. y \<le> f x}"
  by (metis (no_types, lifting) lb_imageI mem_Collect_eq)

lemma im_le3:
  "f`X \<subseteq> Y \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<in> lbd R Y (f`{x \<in> X. y \<le> f x})"
  by (simp add: im_le2 lbd_mem_iff)

lemma extrema_dual_cext2:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"y \<in> Y" and A4:"is_clattice X" "is_clattice Y"
  shows "y \<le> f ((dual_adj f X Y) y)"
proof-
  let ?g="dual_adj f X Y"
  have B0:"f (?g y) = f (Sup X {x \<in> X. y \<le> f x})"  by (simp add: dual_adj_def)
  have B1:"...      = Inf Y (f`{x \<in> X. y \<le> f x})" by (metis (no_types, lifting) A0 extrema_dual_def mem_Collect_eq subsetI)
  have B2:"...     \<ge> y " using im_le3[of f X Y y] by (metis (no_types, lifting) A1 A2 assms(5) binf_idem1 cinfD61 clatD2 image_Collect_subsetI image_subset_iff inf_anti1 insert_absorb insert_subsetI singletonI subset_insertI)
  show ?thesis by (simp add: B1 B2 dual_adj_def)
qed

lemma extrema_dual_cext2b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> extensive Y (f \<circ> (dual_adj f X Y))"
  by (simp add: extensiveI1 extrema_dual_cext2)

lemma adj_range: 
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> (dual_adj f X Y)`Y \<subseteq> X"
  apply(auto simp add:dual_adj_def)  by (metis (full_types) Collect_subset clatD21 is_supE1 sup_equality)

lemma extrema_dual_gc:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> galois_conn f X (dual_adj f X Y) Y"
  by(rule gcI; simp add:extrema_dual_antitone1c extrema_dual_cext1b extrema_dual_antitone2b extrema_dual_cext2b adj_range)


subsection SomeClosures

definition sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
 "sup_cl X A \<equiv> {x \<in> X. \<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup R X E x}"

definition inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "inf_cl X A \<equiv> {x \<in> X. \<exists>E \<in> Pow A. E \<noteq> {} \<and> is_inf X E x}"

definition fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_inf_cl X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_inf X F x}"

definition fne_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_sup_cl X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x}"

definition fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fin_inf_cl X A \<equiv> {x \<in> X. \<exists>F \<in> Fpow A. is_inf X F x}"


abbreviation sup_inv where  "sup_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup R X E y)"

abbreviation inf_inv where "inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E y)"

abbreviation fne_inf_inv where "fne_inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E y)"

abbreviation fne_sup_inv where "fne_sup_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup R X E y)"

abbreviation fin_inf_inv where "fin_inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and>  is_inf X E y)"


lemma sup_cl_imp0:
  "x \<in> sup_cl X A  \<Longrightarrow> x \<in> X "
  by (simp add: sup_cl_def)

lemma inf_cl_imp0:
  "x \<in> inf_cl X A \<Longrightarrow> x \<in> X "
  by (simp add: inf_cl_def)

lemma fin_inf_cl_imp0:
  "x \<in> fin_inf_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: fin_inf_cl_def)

lemma fne_sup_cl_imp0:
  "x \<in> fne_sup_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: fne_sup_cl_def)

lemma fne_inf_cl_imp0:
  "x \<in> fne_inf_cl X A\<Longrightarrow> x \<in> X"
  by (simp add: fne_inf_cl_def)

lemma sup_cl_imp1:
  "x \<in> sup_cl X A \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup R X E x)"
   by (simp add: sup_cl_def) 

lemma inf_cl_imp1:
  "x \<in> inf_cl X A \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and>  is_inf X E x)"
   by (simp add: inf_cl_def) 

lemma fin_inf_cl_imp1:
  "x \<in> fin_inf_cl X A \<Longrightarrow> ( \<exists>F \<in> Fpow A.  is_inf X F x)"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_imp1:
  "x \<in> fne_inf_cl X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_inf X F x)"
  by (simp add: fne_inf_cl_def)

lemma fne_sup_cl_imp1:
  "x \<in> fne_sup_cl X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x)"
  by (simp add: fne_sup_cl_def)

lemma sup_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup R X E x) \<Longrightarrow> x \<in> sup_cl X A"
   by (simp add: sup_cl_def) 

lemma inf_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and>  is_inf X E x) \<Longrightarrow> x \<in> inf_cl X A"
   by (simp add: inf_cl_def) 

lemma fin_inf_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. is_inf X F x) \<Longrightarrow> x \<in> fin_inf_cl X A"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_inf X F x) \<Longrightarrow> x \<in> fne_inf_cl X A"
  by (simp add: fne_inf_cl_def)

lemma fne_sup_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_sup R X F x) \<Longrightarrow> x \<in> fne_sup_cl X A"
  by (simp add: fne_sup_cl_def)

lemma sup_cl_obtains:
  assumes "x \<in> sup_cl X A"
  obtains Ex where "Ex \<in> Pow A \<and> Ex \<noteq> {}  \<and>is_sup R X Ex x"
  by (meson assms sup_cl_imp1)

lemma inf_cl_obtains:
  assumes "x \<in> inf_cl X A"
  obtains Ex where "Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_inf X Ex x"
  by (meson assms inf_cl_imp1)

lemma fin_inf_cl_obtains:
  assumes "x \<in> fin_inf_cl X A"
  obtains F where "F \<in> Fpow A \<and> is_inf X F x"
  by (meson assms fin_inf_cl_imp1)

lemma fne_inf_cl_obtains:
  assumes "x \<in> fne_inf_cl X A"
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_inf X F x"
  by (meson assms fne_inf_cl_imp1)

lemma fne_sup_cl_obtains:
  assumes "x \<in> fne_sup_cl X A"
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup R X F x"
  by (meson assms fne_sup_cl_imp1)

lemma sup_cl_vimage:
  "x \<in> sup_cl X A \<Longrightarrow> vimage (\<lambda>E. Sup X E) {x} \<noteq> {}"
  by (metis empty_iff sup_cl_imp0 sup_equality sup_singleton vimage_singleton_eq)

lemma sup_cl_inv:
  "x \<in> sup_cl X A \<Longrightarrow> Sup X (sup_inv X A x) =x"
  by(rule someI2_ex, meson sup_cl_obtains, simp add: sup_equality)

lemma sup_cl_inv2:
  "x \<in> sup_cl X A \<Longrightarrow> Sup X (sup_inv X A x)  \<in> sup_cl X A"
  using sup_cl_inv by force

definition is_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup_cl X A\<equiv> (\<forall>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup R X E x \<longrightarrow> x \<in> A)"

definition is_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E x \<longrightarrow> x \<in> A)"

definition is_fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fin_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Pow A \<and>  is_inf X E x \<longrightarrow> x \<in> A)"

definition is_fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fne_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E x \<longrightarrow> x \<in> A)"

lemma up_closed_supin_closed0:
  "is_ord_cl X A (\<le>) \<Longrightarrow> E \<in> Pow A \<Longrightarrow> E \<noteq> {} \<Longrightarrow> is_sup R X E x  \<Longrightarrow> x \<in> A"
  using is_supE1 is_supE7 ord_cl_memI1 by fastforce

lemma up_closed_supin_closed:
  "is_ord_cl X A (\<le>) \<Longrightarrow> is_sup_cl X A"
  using is_sup_cl_def up_closed_supin_closed0 by blast

lemma dw_closed_infin_closed0:
  "is_ord_cl X A (\<ge>) \<Longrightarrow> E \<in> Pow A \<Longrightarrow> E \<noteq> {} \<Longrightarrow> is_inf X E x  \<Longrightarrow> x \<in> A"
  using is_infE1 is_infD1121 ord_cl_memI1 by fastforce

lemma down_closed_infin_closed:
  "is_ord_cl X A (\<ge>) \<Longrightarrow> is_inf_cl X A"
  by (metis dw_closed_infin_closed0 is_inf_cl_def)

lemma sup_cl_extensive:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> sup_cl X A"
  apply(auto simp add:sup_cl_def) by (metis PowI empty_not_insert empty_subsetI insert_subsetI subsetD sup_singleton)

lemma inf_cl_extensive:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> inf_cl X A"
  apply(auto simp add:inf_cl_def)
  by (metis PowI empty_not_insert empty_subsetI insert_subsetI subsetD inf_singleton)

lemma fin_inf_cl_extensive:
  assumes A0:"A \<subseteq> X"
  shows "A \<subseteq> fin_inf_cl X A"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_inf X {a} a"
    using A1 assms inf_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fin_inf_cl X A" apply(simp add:fin_inf_cl_def) using B0 B2 is_infE1 by blast
qed

lemma fne_inf_cl_extensive:
  assumes A0: "A \<subseteq> X"
  shows "A \<subseteq> fne_inf_cl X A"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_inf X {a} a"
    using A1 assms inf_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fne_inf_cl X A"
    apply(simp add:fne_inf_cl_def)
    using A1 B0 B2 assms by blast
qed

lemma fne_sup_cl_extensive:
  assumes A0: "A \<subseteq> X"
  shows "A \<subseteq> fne_sup_cl X A"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_sup R X {a} a"
    using A1 assms sup_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fne_sup_cl X A"
    apply(simp add:fne_sup_cl_def)
    using A1 B0 B2 assms by blast
qed

lemma sup_cl_ext:
  "extensive (Pow X) (\<lambda>A. sup_cl X A)"
  by (meson PowD extensiveI1 sup_cl_extensive)

lemma inf_cl_ext:
  "extensive (Pow X) (\<lambda>A. inf_cl X A)"
  by (meson PowD extensiveI1 inf_cl_extensive)

lemma fin_inf_cl_ext:
  "extensive (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (meson PowD extensiveI1 fin_inf_cl_extensive)

lemma fne_inf_cl_ext:
  "extensive (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (meson PowD extensiveI1 fne_inf_cl_extensive)

lemma fne_sup_cl_ext:
  "extensive (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (meson PowD extensiveI1 fne_sup_cl_extensive)

lemma sup_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> sup_cl X A \<subseteq> sup_cl X B"
  by(auto simp add:sup_cl_def)

lemma inf_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> inf_cl X A \<subseteq> inf_cl X B"
  by(auto simp add:inf_cl_def)

lemma fin_inf_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fin_inf_cl X A \<subseteq> fin_inf_cl X B"
  apply(auto simp add:fin_inf_cl_def) using Fpow_mono by blast

lemma fne_inf_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_inf_cl X A \<subseteq> fne_inf_cl X B"
  apply(auto simp add:fne_inf_cl_def) by (metis Fpow_mono empty_iff subsetD)

lemma fne_sup_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl X A \<subseteq> fne_sup_cl X B"
  apply(auto simp add:fne_sup_cl_def) by (metis Fpow_mono empty_iff subsetD)
                                                
lemma sup_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. sup_cl X A)"
  by (meson PowD isotoneI1 sup_cl_isotone)

lemma inf_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. inf_cl X A)"
  by (meson PowD isotoneI1 inf_cl_isotone)

lemma fin_inf_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (meson PowD isotoneI1 fin_inf_cl_isotone)

lemma fne_inf_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (meson PowD isotoneI1 fne_inf_cl_isotone)

lemma fne_sup_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (meson PowD isotoneI1 fne_sup_cl_isotone)

lemma sup_cl_idempotent0:
  "s \<in> sup_cl X (sup_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Pow (sup_cl X A) \<and> E \<noteq> {} \<and> is_sup R X E s)"
  by (meson sup_cl_imp1)

lemma inf_cl_idempotent0:
  "s \<in> inf_cl X (inf_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Pow (inf_cl X A) \<and> E \<noteq> {} \<and> is_inf X E s)"
  by (meson inf_cl_imp1)

lemma fin_inf_cl_idempotent0:
  "s \<in> fin_inf_cl X (fin_inf_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fin_inf_cl X A) \<and> is_inf X E s)"
  by (meson fin_inf_cl_imp1)

lemma fne_inf_cl_idempotent0:
  "s \<in> fne_inf_cl X (fne_inf_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_inf_cl X A) \<and> E \<noteq> {} \<and> is_inf X E s)"
  by (meson fne_inf_cl_imp1)

lemma fne_sup_cl_idempotent0:
  "s \<in> fne_sup_cl X (fne_sup_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_sup_cl X A) \<and> E \<noteq> {} \<and> is_sup R X E s)"
  by (meson fne_sup_cl_imp1)

lemma sup_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (sup_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_sup R X Ex x)"
  by (meson PowD in_mono sup_cl_imp1)

lemma inf_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (inf_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_inf X Ex x)"
  by (meson PowD in_mono inf_cl_imp1)

lemma fin_inf_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (fin_inf_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A  \<and> is_inf X Ex x)"
  by (meson PowD in_mono fin_inf_cl_imp1)

lemma fne_inf_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (fne_inf_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_inf X Ex x)"
  by (meson PowD in_mono fne_inf_cl_imp1)

lemma fne_sup_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (fne_sup_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_sup R X Ex x)"
  by (meson PowD in_mono fne_sup_cl_imp1)


lemma sup_cl_idempotent2:
  "sup_cl X A \<subseteq> sup_cl X (sup_cl X A)"
  by (meson subsetI sup_cl_extensive sup_cl_imp0)

lemma inf_cl_idempotent2:
  "inf_cl X A \<subseteq> inf_cl X (inf_cl X A)"
  by (meson inf_cl_extensive inf_cl_imp0 subsetI)

lemma fin_inf_cl_idempotent2:
  "fin_inf_cl X A \<subseteq> fin_inf_cl X (fin_inf_cl X A)"
  by (meson fin_inf_cl_extensive fin_inf_cl_imp0 subsetI)

lemma fne_inf_cl_idempotent2:
  "fne_inf_cl X A \<subseteq> fne_inf_cl X (fne_inf_cl X A)"
  by (meson fne_inf_cl_extensive fne_inf_cl_imp0 subsetI)

lemma fne_sup_cl_idempotent2:
  "fne_sup_cl X A \<subseteq> fne_sup_cl X (fne_sup_cl X A)"
  by (meson fne_sup_cl_extensive fne_sup_cl_imp0 subsetI)

lemma sup_cl_idempotent:
   "sup_cl X (sup_cl X A) = sup_cl X A"
proof-
  let ?L1="sup_cl X A" let ?L2="sup_cl X ?L1"
  show "sup_cl X (sup_cl X A) = sup_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (meson subset_iff sup_cl_extensive sup_cl_imp0)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup R X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow (?L1) \<and> E \<noteq> {} \<and> is_sup R X E s"
        by (meson P0 sup_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 sup_cl_idempotent1 by auto
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup X Ai}"
      have B00:"((\<lambda>Ai. Sup X Ai)`?fE) = ?S" apply(auto) 
          by (metis (mono_tags, lifting) B0 PowD is_supE1 someI_ex sup_equality)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Sup X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 sup_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              using B1 B6A1 is_supE1 sup_equality by fastforce
        qed
      qed
      obtain se where B11A0:"is_sup R X E se"
        using P1 by blast
      obtain ss where B11A1:"is_sup R X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup R X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup R X Ai ti)"
        using B1 by blast
      have B12:"?fE \<noteq> {}"
        by (simp add: P1)
      have B13:"is_sup R X ((\<lambda>Ai. Sup X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_sup R X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B12 B13 B8 sup_families) 
      have B15:"(\<Union>?fE) \<in> Pow A"
        using B1 by blast
      have B16:"(\<Union>?fE) \<noteq> {}"
        using B1 P1 by auto
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B11A1 B14 B15 B16 B2 P1 sup_cl_if1 sup_iff2)
      qed
    qed
  qed
qed


lemma inf_cl_idempotent:
   "inf_cl X (inf_cl X A) = inf_cl X A"
proof-
  let ?L1="inf_cl X A" let ?L2="inf_cl X ?L1"
  show "inf_cl X (inf_cl X A) = inf_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (meson subset_iff inf_cl_extensive inf_cl_imp0)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow (?L1) \<and> E \<noteq> {} \<and> is_inf X E s"
        by (meson P0 inf_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 inf_cl_idempotent1 by auto
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf X Ai}"
      have B00:"((\<lambda>Ai. Inf X Ai)`?fE) = ?S" apply(auto) 
          by (metis (mono_tags, lifting) B0 PowD is_infE1 someI_ex inf_equality)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 inf_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              using B1 B6A1 is_infE1 inf_equality by fastforce
        qed
      qed
      obtain se where B11A0:"is_inf X E se"
        using P1 by blast
      obtain ss where B11A1:"is_inf X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_inf X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_inf X Ai ti)"
        using B1 by blast
      have B12:"?fE \<noteq> {}"
        by (simp add: P1)
      have B13:"is_inf X ((\<lambda>Ai. Inf X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_inf X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B12 B13 B8 inf_families) 
      have B15:"(\<Union>?fE) \<in> Pow A"
        using B1 by blast
      have B16:"(\<Union>?fE) \<noteq> {}"
        using B1 P1 by auto
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B11A1 B14 B15 B16 B2 P1 inf_cl_if1 inf_iff2)
      qed
    qed
  qed
qed


lemma fin_inf_cl_idempotent:
   "fin_inf_cl X (fin_inf_cl X A) = fin_inf_cl X A"
proof-
  let ?L1="fin_inf_cl X A" let ?L2="fin_inf_cl X ?L1"
  show "fin_inf_cl X (fin_inf_cl X A) = fin_inf_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (meson subset_iff fin_inf_cl_extensive fin_inf_cl_imp0)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> is_inf X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> is_inf X E s"
        by (meson P0 fin_inf_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using Fpow_subset_Pow P1 fin_inf_cl_idempotent1 by fastforce
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf X Ai}"
      have B00:"((\<lambda>Ai. Inf X Ai)`?fE) = ?S" apply(auto)
        by (metis (no_types, lifting) B0 inf_equality is_infE1 someI_ex) 
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 inf_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              by (metis (mono_tags, lifting) B00 B1 B6A1 image_iff inf_equality)
        qed
      qed
      obtain se where B11A0:"is_inf X E se"
        using P1 by blast
      obtain ss where B11A1:"is_inf X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_inf X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_inf X Ai ti)"
        using B1 by blast
      have B13:"is_inf X ((\<lambda>Ai. Inf X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_inf X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B11 B13 Sup_empty image_empty inf_families)
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B11A1 B14 B15 B2 P0 P1 fin_inf_cl_if1 fin_inf_cl_imp0 is_inf_unique)
      qed
    qed
  qed
qed


lemma fne_inf_cl_idempotent:
  "fne_inf_cl X (fne_inf_cl X A) = fne_inf_cl X A"
proof-
  let ?L1="fne_inf_cl X A" let ?L2="fne_inf_cl X ?L1"
  show "fne_inf_cl X (fne_inf_cl X A) = fne_inf_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (simp add: fne_inf_cl_idempotent2)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> E \<noteq> {} \<and> is_inf X E s"
        using P0 fne_inf_cl_imp1 by blast
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using Fpow_subset_Pow P1 fne_inf_cl_idempotent1 by blast
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf X Ai}"
      have B00:"((\<lambda>Ai. Inf X Ai)`?fE) = ?S" apply(auto)
        by (metis (mono_tags, lifting) B0 inf_equality is_infE1 someI_ex)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 inf_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              by (metis (mono_tags, lifting) B00 B1 B6A1 image_iff inf_equality)
        qed
      qed
      obtain se where B11A0:"is_inf X E se"
        using P1 by blast
      obtain ss where B11A1:"is_inf X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_inf X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_inf X Ai ti)"
        using B1 by blast
      have B13:"is_inf X ((\<lambda>Ai. Inf X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_inf X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B11 B13 Sup_empty image_empty inf_families)
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B1 B11A1 B14 B15 B2 P1 SUP_bot_conv(2) equals0I fne_inf_cl_if1 inf_equality is_infE1)
      qed
    qed
  qed
qed


lemma fne_sup_cl_idempotent:
  "fne_sup_cl X (fne_sup_cl X A) = fne_sup_cl X A"
proof-
  let ?L1="fne_sup_cl X A" let ?L2="fne_sup_cl X ?L1"
  show "fne_sup_cl X (fne_sup_cl X A) = fne_sup_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (simp add: fne_sup_cl_idempotent2)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup R X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> E \<noteq> {} \<and> is_sup R X E s"
        using P0 fne_sup_cl_imp1 by blast
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using Fpow_subset_Pow P1 fne_sup_cl_idempotent1 by blast
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup X Ai}"
      have B00:"((\<lambda>Ai. Sup X Ai)`?fE) = ?S" apply(auto)
        by (metis (mono_tags, lifting) B0 sup_equality is_supE1 someI_ex)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Sup X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 sup_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              by (metis (mono_tags, lifting) B00 B1 B6A1 image_iff sup_equality)
        qed
      qed
      obtain se where B11A0:"is_sup R X E se"
        using P1 by blast
      obtain ss where B11A1:"is_sup R X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup R X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup R X Ai ti)"
        using B1 by blast
      have B13:"is_sup R X ((\<lambda>Ai. Sup X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_sup R X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B11 B13 Sup_empty image_empty sup_families)
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B1 B11A1 B14 B15 B2 P1 SUP_bot_conv(2) equals0I fne_sup_cl_if1 sup_equality is_supE1)
      qed
    qed
  qed
qed


lemma sup_cl_ide:
  "idempotent (Pow X) (\<lambda>A. sup_cl X A)"
  by (simp add: idempotent_def sup_cl_idempotent)

lemma inf_cl_ide:
  "idempotent (Pow X) (\<lambda>A. inf_cl X A)"
  by (simp add: idempotent_def inf_cl_idempotent)

lemma fin_inf_cl_ide:
  "idempotent (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (simp add: idempotent_def fin_inf_cl_idempotent)

lemma fne_inf_cl_ide:
  "idempotent (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (simp add: idempotent_def fne_inf_cl_idempotent)

lemma fne_sup_cl_ide:
  "idempotent (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (simp add: idempotent_def fne_sup_cl_idempotent)

lemma sup_cl_range:
  "(\<lambda>A. sup_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI sup_cl_ide sup_cl_imp0)

lemma inf_cl_range:
  "(\<lambda>A. inf_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 inf_cl_ide inf_cl_imp0 subsetI)

lemma fin_inf_cl_range:
  "(\<lambda>A. fin_inf_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI fin_inf_cl_ide fin_inf_cl_imp0)

lemma fne_inf_cl_range:
  "(\<lambda>A. fne_inf_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI fne_inf_cl_ide fne_inf_cl_imp0)

lemma fne_sup_cl_range:
  "(\<lambda>A. fne_sup_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI fne_sup_cl_ide fne_sup_cl_imp0)

lemma sup_cl_is_cl:
  "closure (Pow X) (\<lambda>A. sup_cl X A)"
  by (simp add: closure_def sup_cl_ext sup_cl_ide sup_cl_iso sup_cl_range)

lemma inf_cl_is_cl:
  "closure (Pow X) (\<lambda>A. inf_cl X A)"
  by (simp add: inf_cl_ext inf_cl_ide inf_cl_iso inf_cl_range closure_def)

lemma fin_inf_cl_is_cl:
  "closure (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (simp add: fin_inf_cl_ext fin_inf_cl_ide fin_inf_cl_iso fin_inf_cl_range closure_def)

lemma fne_inf_cl_is_cl:
  "closure (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (simp add: fne_inf_cl_ext fne_inf_cl_ide fne_inf_cl_iso fne_inf_cl_range closure_def)

lemma fne_sup_cl_is_cl:
  "closure (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (simp add: fne_sup_cl_ext fne_sup_cl_ide fne_sup_cl_iso fne_sup_cl_range closure_def)

lemma fne_sup_cl_dir:
  assumes A0:"is_sup_semilattice R X" and A1:"A \<subseteq> X"
  shows  "is_dir (fne_sup_cl X A) (\<le>)"
proof-
  have B0:"\<And>a b. a \<in> fne_sup_cl X A \<and> b \<in> fne_sup_cl X A \<longrightarrow> (\<exists>c\<in>fne_sup_cl X A. (a, c)\<in>R \<and> (b, c)\<in>R)"
  proof
    fix a b assume A2:"a \<in> fne_sup_cl X A \<and> b \<in> fne_sup_cl X A "
    obtain Ea where A3:"Ea \<in> Fpow A \<and> Ea \<noteq> {} \<and> is_sup R X Ea a"
      using A2 fne_sup_cl_imp1 by blast
    obtain Eb where A4:"Eb \<in> Fpow A \<and> Eb \<noteq> {} \<and> is_sup R X Eb b"
      using A2 fne_sup_cl_imp1 by blast
    have B1:"Ea \<union> Eb \<in> Fpow A \<and> Ea \<union> Eb \<noteq> {}"
      by (metis A3 A4 Fpow_Pow_finite Int_Collect Pow_iff Un_empty Un_subset_iff finite_UnI)
    have B2:"(Ea \<union> Eb) \<subseteq> X"
      by (metis A1 A3 A4 Fpow_Pow_finite Int_Collect Pow_iff dual_order.trans sup.boundedI)
    obtain c where A5:"is_sup R X (Ea \<union> Eb) c"
      by (metis A0 B1 B2 Fpow_Pow_finite Int_Collect bsup_finite2)
    have B3:"c \<in> fne_sup_cl X A \<and> (a, c)\<in>R \<and> (b, c)\<in>R"
      by (meson A3 A4 A5 B1 Un_upper2 fne_sup_cl_if1 is_supE1 is_sup_iso1 sup.cobounded1)
    show "(\<exists>c\<in>fne_sup_cl X A. (a, c)\<in>R \<and> (b, c)\<in>R)"
      using B3 by blast
  qed
  show ?thesis
    by (simp add: B0 is_updirI1)
qed
  
lemma sup_density_test1:
  "\<lbrakk>sup_cl X A =X; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Ex \<in> Pow A. Sup X Ex = x)"
  using sup_cl_imp1 sup_equality by blast

section Compactness


definition is_compact::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_compact X c \<equiv> c \<in> X \<and> (\<forall>A. A \<in> Pow_ne X \<and> c \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))"

definition compact_elements::"'a::order set \<Rightarrow> 'a::order set" where
  "compact_elements X \<equiv> {c. is_compact X c}"

definition compactly_generated::"'a::order set \<Rightarrow> bool" where
  "compactly_generated X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow (compact_elements X). is_sup R X C x))"


lemma compactI:
  "\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))\<rbrakk> \<Longrightarrow> is_compact X c"
  by(simp add:is_compact_def)

lemma compactD:
  "\<lbrakk>is_compact X c; A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
  by(simp add:is_compact_def)

lemma compact_element_memD1:"x \<in> compact_elements X  \<Longrightarrow> is_compact X x" by (simp add: compact_elements_def)
lemma compactD2:"is_compact X x \<Longrightarrow> x \<in> X" by (simp add: is_compact_def)
lemma compact_element_memD2:"x \<in> compact_elements X  \<Longrightarrow> x \<in> X" using compactD2 compact_element_memD1 by blast 
lemma compact_elements_sub:"compact_elements X \<subseteq> X"  by (simp add: compact_element_memD2 subsetI) 

lemma compact_elements_mem_iff1: "x \<in> compact_elements X \<longleftrightarrow> is_compact X x" by (simp add: compact_elements_def)

lemma compactly_generatedD1:
  "compactly_generated X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>C \<in> Pow (compact_elements X). is_sup R X C x)"
  by(simp add:compactly_generated_def)

lemma compactly_generatedI1:
  "(\<And>x. x \<in> X \<Longrightarrow>  (\<exists>C \<in> Pow (compact_elements X). is_sup R X C x)) \<Longrightarrow> compactly_generated X"
  by(simp add:compactly_generated_def)


definition join_dense::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where "join_dense X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_sup R X Dx x)"
definition meet_dense::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where "meet_dense X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_inf X Dx x)"

lemma join_denseD1:"\<lbrakk>join_dense X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_sup R X Dx x)" by (simp add:join_dense_def)
lemma meet_denseD1:"\<lbrakk>meet_dense X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_inf X Dx x)" by (simp add:meet_dense_def)

lemma cjoin_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice X\<rbrakk> \<Longrightarrow> (join_dense X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Sup X Dx))"  apply(auto) using join_denseD1 sup_equality apply blast  by (metis (no_types, opaque_lifting) Pow_iff clatD21 dual_order.trans join_dense_def sup_equality)
lemma cmeet_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice X\<rbrakk> \<Longrightarrow> (meet_dense X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Inf X Dx))"  apply(auto) using meet_denseD1 inf_equality apply blast  by (metis (no_types, opaque_lifting) Pow_iff clatD22 dual_order.trans meet_dense_def inf_equality)

lemma join_denseD2:"\<lbrakk>join_dense X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Sup X (x]\<^sub>D)"
proof-
  assume P:"join_dense X D" "D \<subseteq> X" 
  show "(\<And>x. x \<in> X \<Longrightarrow> x = Sup X (x]\<^sub>D)"
  proof- 
    fix x assume P1:"x \<in> X" 
    obtain Dx where "Dx \<in> Pow D" "is_sup R X Dx x" by (meson P(1) P1 join_denseD1)
    have B0:"\<forall>d. d \<in> Dx \<longrightarrow> d \<le> x"     using \<open>is_sup (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_supD1121 by blast
    have B1:"Dx \<subseteq> X"  using P(2) \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> by blast
    have B2:"Dx \<subseteq> (x]\<^sub>D"    by (meson B0 PowD \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> rolcI1 subset_eq)
      have B3:"is_sup R X ((x]\<^sub>D) x" 
      proof(rule is_supI5)
        show "\<And>a. a \<in> ubd R  X (x]\<^sub>D \<Longrightarrow> x \<le> a" using B2 \<open>is_sup (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_supE3 ubd_ant1b by blast
        show " x \<in> ubd R  X (x]\<^sub>D"   by (meson P1 rolcD12 ubd_mem_iff3)
      qed
    show "x= Sup X (x]\<^sub>D" using B3 sup_equality by force
  qed
qed

lemma join_denseI2:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X ((x]\<^sub>D) x) \<rbrakk> \<Longrightarrow> join_dense X D" by (meson Pow_iff join_dense_def rolc_subset1)

lemma meet_denseD2:"\<lbrakk>meet_dense X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf X [x)\<^sub>D)"
proof-
  assume P:"meet_dense X D" "D \<subseteq> X" 
  show "(\<And>x. x \<in> X \<Longrightarrow> x = Inf X [x)\<^sub>D)"
  proof- 
    fix x assume P1:"x \<in> X" 
    obtain Dx where "Dx \<in> Pow D" "is_inf X Dx x" by (meson P(1) P1 meet_denseD1)
    have B0:"\<forall>d. d \<in> Dx \<longrightarrow> x \<le> d"     using \<open>is_inf (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_infD1121 by blast
    have B1:"Dx \<subseteq> X"  using P(2) \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> by blast
    have B2:"Dx \<subseteq> [x)\<^sub>D"    by (meson B0 PowD \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> lorcI1 subset_eq)
      have B3:"is_inf X ([x)\<^sub>D) x" 
      proof(rule is_infI5)
        show "\<And>a. a \<in> lbd R X [x)\<^sub>D \<Longrightarrow> (a, x) \<in> R" using B2 \<open>is_inf (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_infE3 lbd_ant1b by blast
        show " x \<in> lbd R X [x)\<^sub>D"   by (meson P1 lorcD12 lbd_mem_iff3)
      qed
    show "x= Inf X [x)\<^sub>D" using B3 inf_equality by force
  qed
qed

lemma meet_denseI2:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x) \<rbrakk> \<Longrightarrow> meet_dense X D" by (meson Pow_iff meet_dense_def lorc_subset1)
lemma join_denseD4:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X ((x]\<^sub>D) x)\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; b < a\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. x \<le> a \<and> \<not> ((x, b)\<in>R)))" by (metis is_sup_iso1 less_le_not_le rolc_mem_iff1 subsetI)
lemma meet_denseD4:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x)\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; a < b\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. (a, x) \<in> R \<and> \<not> (b \<le> x)))" by (metis is_inf_ant1 less_le_not_le lorc_mem_iff1 subsetI)

lemma join_denseD5:"\<lbrakk>D \<subseteq> X; is_clattice X;  (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; b < a\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. x \<le> a \<and> \<not> ((x, b)\<in>R)))\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> is_sup R X ((x]\<^sub>D) x)"
proof-
  assume A0:"D \<subseteq> X" "is_clattice X"  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; b <a \<rbrakk>\<Longrightarrow>(\<exists>x \<in> D. x \<le> a \<and> \<not> ((x, b)\<in>R)))"
  show "(\<And>x. x \<in> X \<Longrightarrow> is_sup R X ((x]\<^sub>D) x)"
  proof-
    fix a assume A1:"a \<in> X"
    obtain b where B0:"is_sup R X ((a]\<^sub>D) b"   by (meson A0 clatD21 order_trans rolc_subset1)
    have B1:"b \<le> a"  by (meson A1 B0 is_supD42 rolc_mem_iff1 ub_def)
    have "b=a"
    proof(rule ccontr)
      assume con1:"\<not> (b=a)" obtain con2:"b < a"     by (simp add: B1 con1 order_less_le)
      obtain x where  B2:"x \<in> D \<and> x \<le> a \<and> \<not>((x, b)\<in>R)"   using A0(3) A1 B0 con2 is_supE1 by blast
      have B3:"x \<in> (a]\<^sub>D"   using B2 rolcI1 by blast
      show False
        using B0 B2 B3 is_supD1121 by blast
    qed
    show "is_sup R X ((a]\<^sub>D) a"
      using B0 \<open>(b::'a::order) = (a::'a::order)\<close> by blast
  qed
qed
lemma meet_denseD5:"\<lbrakk>D \<subseteq> X; is_clattice X;  (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; a < b\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. (a, x) \<in> R \<and> \<not> (b \<le> x)))\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x)"
proof-
  assume A0:"D \<subseteq> X" "is_clattice X"  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; a < b \<rbrakk>\<Longrightarrow>(\<exists>x \<in> D. (a, x) \<in> R \<and> \<not> (b \<le> x)))"
  show "(\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x)"
  proof-
    fix a assume A1:"a \<in> X"
    obtain b where B0:"is_inf X ([a)\<^sub>D) b"   by (meson A0 clatD22 order_trans lorc_subset1)
    have B1:"(a, b)\<in>R"  by (meson A1 B0 is_infD42 lorc_mem_iff1 lb_def)
    have "b=a"
    proof(rule ccontr)
      assume con1:"\<not> (b=a)" obtain con2:"a < b"  using B1 con1 by auto 
      obtain x where  B2:"x \<in> D \<and> (a, x) \<in> R \<and> \<not>(b \<le> x)"   using A0(3) A1 B0 con2 is_infE1 by blast
      have B3:"x \<in> [a)\<^sub>D"   using B2 lorcI1 by blast
      show False using B0 B2 B3 is_infD1121 by blast
    qed
    show "is_inf X ([a)\<^sub>D) a"using B0 \<open>(b::'a::order) = (a::'a::order)\<close> by blast
  qed
qed

lemma compactly_generated_iff:"compactly_generated X \<longleftrightarrow> join_dense X (compact_elements X)" by(auto simp add:compactly_generated_def join_dense_def)

lemma compact_obtain:
  assumes "is_compact X c" and "A \<in> Pow_ne X" and "c \<le> Sup X A"
  obtains A0 where "A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0"
  using assms compactD[of X c A] by blast

(*
  in a csup semilattice an element is compact iff directed coverings contain an upper bound
*)


lemma compactD1:
  "\<lbrakk>is_compact X c; A \<in> Pow_ne X; c \<le> Sup X A; is_dir A (\<le>)\<rbrakk> \<Longrightarrow> (\<exists>A0. \<exists>a. a \<in> A \<and> a ub A0 \<and> A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
  by (meson compactD updir_finite_obtain)


lemma ccompact0:
  assumes A0:"is_sup_semilattice R X" and
          A1:"is_compact X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"c \<le> Sup X A" and
          A4:"is_dir A (\<le>)"
  shows "\<exists>a \<in> A. c \<le> a"
proof-
  obtain A0 a where A5:"a \<in> A \<and> a ub A0 \<and> A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0"
    using A1 A2 A3 A4 compactD1 by blast
  have A7:"a \<in> ubd R  X A0"
     using A2 A5 pow_neD1 ubdI2 by blast 
  have B0:"Sup X A0 \<le> a" 
    using fsup_lub3[of X A0 a] A0 A2 A5 A7 fpow_ne_iso2 by blast
  have B1:"c \<le> a"
    using A5 B0 by fastforce
  show ?thesis
    using A5 B1 by blast
qed

lemma ccompact1:
  assumes A0:"is_csup_semilattice X" and
          A1:"c \<in> X" and
          A2:"(\<And>A. \<lbrakk>A \<in> Pow_ne X; c \<le> Sup X A; is_dir A (\<le>)\<rbrakk> \<Longrightarrow> (\<exists>a \<in> A. c \<le> a))"
  shows "is_compact X c"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> c \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))"
  proof
    fix A assume A3:"A \<in> Pow_ne X \<and> c \<le> Sup X A"
    let ?C="fne_sup_cl X A"
    have B0:"is_dir ?C (\<le>)"
      by (simp add: A0 A3 csup_fsup fne_sup_cl_dir pow_neD1)
    have B1:"A \<subseteq> ?C"
      by (simp add: A3 fne_sup_cl_extensive pow_neD1)
    have B2:"A \<subseteq> X \<and> ?C \<subseteq> X"
      using B1 fne_sup_cl_imp0 by blast
    have B2:"Sup X A \<le> Sup X ?C"
      by (metis A0 A3 B1 B2 bot.extremum_uniqueI csupD2 is_sup_iso1 pow_ne_iff2 sup_equality)
    have B3:"c \<le> Sup X ?C"
      using A3 B2 dual_order.trans by blast
    obtain d where B4:"d \<in> ?C \<and> c \<le> d"
      by (metis A2 A3 B0 B1 B3 bot.extremum_uniqueI fne_sup_cl_range image_subset_iff pow_ne_iff1)
    obtain Fd where B5:"Fd \<in> Fpow_ne A \<and> Sup X Fd = d"
      by (meson B4 fne_sup_cl_imp1 fpow_ne_iff1 sup_equality)
    have B6:"Fd \<in> Fpow_ne A \<and> c \<le> Sup X Fd"
      by (simp add: B4 B5)
    show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
      using B6 by blast
  qed
  show ?thesis
    by (simp add: A1 P0 compactI)
qed

lemma bot_compact:
  assumes A1:"bot \<in> X" and A2:"(\<And>x. x \<in> X \<Longrightarrow> bot \<le> x)"
  shows "is_compact X bot"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> bot \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> bot \<le> Sup X A0))" 
    proof
      fix A assume A3:"A \<in> Pow_ne X \<and> bot \<le> Sup X A"
      obtain a where A4:"a \<in> A"
        using A3 pow_ne_bot by fastforce
      have B0:"{a} \<in> Fpow_ne A \<and> bot \<le> Sup X {a}"
        by (metis A2 A3 A4 bsup_idem1 empty_subsetI finite.emptyI finite.insertI fpow_neI in_mono insert_absorb2 insert_not_empty insert_subsetI pow_neD1)
      show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> bot \<le> Sup X A0)"
        using B0 by auto
    qed
  show ?thesis
    by (simp add: A1 P0 compactI)
qed

lemma dir_set_closure_subset:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"cl_from_clr C {x} \<subseteq> Sup C A" and 
          A6:"is_dir A (\<subseteq>)"
  shows "\<exists>a \<in> A. cl_from_clr C {x} \<subseteq> a"
proof-
  let ?f="cl_from_clr C"
  have B2:"Sup C A = \<Union>A"
    by (metis A0 A2 A4 A6 clrD2 pow_neD1 pow_ne_iff1 sup_equality uni_sup_fam)
  have B2:"{x} \<subseteq> ?f {x}"
    by (metis A0 A3 PowD PowI Pow_bottom cl_ext1 insert_subsetI)
  have B3:"... \<subseteq> \<Union>A"
    by (metis A0 A2 A4 A5 A6 clrD2 pow_neD1 pow_ne_iff1 sup_equality uni_sup_fam)
  have B4:"{x} \<subseteq> \<Union>A"
    using B2 B3 by blast
  obtain a where B5:"a \<in> A \<and> x \<in> a"
    using B4 by auto
  have B6:"a \<in> ubd R  C {{x}}"
    using A4 B5 pow_neD1 ubd_singleton_iff by fastforce
  have B7:"?f {x} \<subseteq> a"
    by (metis A0 A3 B6 Pow_iff cl_lt_ub1 empty_subsetI insert_subset)
  show "(\<exists>a\<in>A. cl_from_clr C {x} \<subseteq> a)"
   using B5 B7 by auto
qed

      

lemma singleton_closure_compact:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk>\<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X"
  shows "is_compact C (cl_from_clr C {x})"
  apply(rule ccompact1) 
   using A0 clatD1 clr_is_clattice pow_is_clattice apply blast
  using A0 A3 cl_range1 apply fastforce
  by (metis A0 A1 A2 A3 dir_set_closure_subset)

lemma closed_compgen:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"E \<in> C"
  shows "(\<exists>A \<in> Pow (compact_elements C). is_sup C A E)"
proof-
   let ?f="cl_from_clr C"
   let ?A="{y. (\<exists>x \<in> E. y= ?f {x})}"
  have B0:"is_clattice C"
    using A0 clr_is_clattice pow_is_clattice by blast
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact C (?f {x})"
    by (metis A0 A1 A2 singleton_closure_compact)
   have P1:"E \<in> Pow X"
      using A0 A3 clrD2b by blast
    have P2:"\<forall>x. x \<in> E \<longrightarrow> {x} \<in> Pow X"
      using P1 by blast 
    have P3:"?A \<subseteq> C"
    proof 
      fix y assume A9:"y \<in> ?A" 
      obtain x where P30:"x \<in> E \<and> y = ?f {x}" using A9 by blast
      show "y \<in> C" using A0 P2 P30 cl_range1 by fastforce
    qed
    have B9:"\<forall>x. x \<in> E \<longrightarrow> {x} \<subseteq> ?f {x}"
      by (meson A0 P2 cl_ext1)
    have B10:"?f E = E"
      by (simp add: A3 cl_from_clr_def ub_single_least2)
    have B11:"\<And>x. x \<in> E \<longrightarrow> ?f {x} \<subseteq> ?f E"
      by (metis A0 A3 B10 P2 cl_lt_ub2 empty_subsetI insert_subsetI)
    have B11b:"E ub ?A"
      using B10 B11 ub_def by force
    have B11c:"E \<in> ubd R  C ?A"
      by (simp add: A3 B11b ubd_mem_iff)
    have B12:"E = (\<Union>x \<in> E. {x})"
      by simp
    have B13:"... \<subseteq> (\<Union>x \<in> E. ?f {x})"
      using B9 by blast
    have B14:"... = (\<Union>?A)"
      by blast
    have B15:"... = Sup UNIV ?A"
      by (meson union_sup_univ)
    have B16:"... \<subseteq> Sup C ?A"
      using sup_iso2[of UNIV C ?A] univ_is_clattice using A3 B0 P3 by blast
    have B17:"... \<subseteq> E"
      by (metis (no_types, lifting) A3 B0 B11b P3 clatD21 is_supD5 sup_equality)
    have B18:"\<forall>x. x \<in> ?A \<longrightarrow> x \<in> compact_elements C"
      using A0 A3 B1 PowD clrD2 compact_elements_mem_iff1 mem_Collect_eq by fastforce
    have B19:"?A \<in> Pow (compact_elements C)"
      using B18 by blast
    have B20:"E = Sup C ?A"
      using B13 B15 B16 B17 by auto
    have B21:"is_sup C ?A E"
      by (metis (mono_tags, lifting) A3 B11b B12 B13 B14 Sup_le_iff is_supI7 subset_antisym ub_def)
    show "\<exists>A \<in> Pow (compact_elements C). is_sup C A E"
      using B19 B21 by blast
qed


lemma clr_compgen1:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)"
  shows "compactly_generated C \<and> (\<forall>x. x \<in> X \<longrightarrow> is_compact C ((cl_from_clr C) {x}))"
proof-
  have P0:"C \<subseteq> Pow X"
    by (simp add: A0 clrD2)
  let ?f="cl_from_clr C"
  have B0:"is_clattice C"
    using A0 clr_is_clattice pow_is_clattice by blast
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact C (?f {x})"
    by (metis A0 A1 A2 singleton_closure_compact)
  have B8:"\<And>E. E \<in> C \<longrightarrow>  (\<exists>A \<in> Pow (compact_elements C). is_sup C A E)"
    by (metis A0 A1 A2 closed_compgen)
  show ?thesis
    by (simp add: B1 B8 compactly_generatedI1)
qed


lemma clr_compgen2:
 "\<lbrakk>is_clr C (Pow X); (\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C);(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)\<rbrakk> \<Longrightarrow> compactly_generated C"
  by (simp add: clr_compgen1)

lemma filters_on_lattice_compactgen:
  "\<lbrakk>is_lattice X; is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> compactly_generated (filters_on X)" 
  apply(rule_tac ?X="X" in clr_compgen2)
  apply (simp add: filter_is_clr lattD41)
  apply (simp add: filter_inter_closed2 lattD41)
  by (simp add: filters_on_iff lattice_filter_dunion9)

lemma distr_lattice_filters:
  "distributive_lattice X \<Longrightarrow> is_lattice (filters_on X)"
  by (simp add: distributive_lattice_def filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice2b lattI2)
  
lemma lattice_filters_distr:
  assumes A0:"distributive_lattice X" 
  shows "distributive_lattice (filters_on X)"
proof-
  let ?F="filters_on X"
  have B01:"is_lattice X"  using assms distributive_lattice_def by blast
  have B02:"is_lattice ?F"
    by (simp add: assms distr_lattice_filters)
  have B1:" \<And>x y z. x \<in> ?F \<and>  y \<in>?F \<and> z \<in> ?F \<longrightarrow> Inf ?F {Sup ?F {x, y}, Sup ?F {x, z}} \<subseteq> Sup ?F {x, Inf ?F {y, z}}"
  proof
    fix f g h assume A1:" f \<in> ?F \<and>  g \<in>?F \<and> h \<in> ?F"
    let ?sfg="Sup ?F {f, g}" and ?sfh="Sup ?F {f, h}" and  ?igh="Inf ?F {g, h}"
    show "Inf ?F {?sfg, ?sfh} \<subseteq> Sup ?F {f, ?igh}"
    proof
      fix z assume A2:"z \<in> (Inf ?F {?sfg, ?sfh})"
      have B2:"Inf ?F {?sfg, ?sfh} =?sfg \<inter> ?sfh"
        by (meson A1 B01 filters_on_iff filters_on_lattice_inf8b filters_on_lattice_sup_semilattice2b inf_equality ssupD4)
      have B3:"z \<in> ?sfg \<and> z \<in> ?sfh"
        using A2 B2 by blast
      obtain x1 y where B4:"x1 \<in> f \<and> y \<in> g \<and> Inf X {x1, y} \<le> z"
        using A1 B01 B3 filters_on_iff filters_on_lattice_bsup2 by blast
      obtain x2 t where B5:"x2 \<in> f \<and> t \<in> h \<and> Inf X {x2, t} \<le> z"
        using A1 B01 B3 filters_on_iff filters_on_lattice_bsup2 by blast
      have B450:"x1 \<in> X \<and> y \<in> X \<and> x2 \<in> X \<and> t \<in> X"
        using A1 B4 B5 filterD2 filters_on_iff by blast
      have B6:"Sup X {x1, Inf X {x2, t}} \<in> f"
        by (meson A1 B01 B4 B450 filter_bsup_memI1 filters_on_iff lattD41 lattD42 sinfD4)
      have B7:"Sup X {y, x2} \<in> f"
        using A1 B01 B4 B5 filterD21 filter_on_lattice_sup01 filters_on_iff by blast
      have B8:"Sup X {y, t} \<in> g"
        by (metis A1 B01 B4 B5 filterD21 filter_on_lattice_sup01 filters_on_iff insert_commute)
      have B9:"Sup X {y, t} \<in> h"
        using A1 B01 B4 B5 filterD21 filter_on_lattice_sup01 filters_on_iff by blast
      have B10:"Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}} \<in> f"
        using A1 B01 B6 B7 filter_finf_closed1 filters_on_iff lattD41 by blast
      have B11:"Inf X {Sup X {y, x2}, Sup X {y, t}} = Sup X {y, Inf X {x2, t}}"
        by (simp add: B450 assms distr_latticeD1)
      have B12:"Inf X {Sup X {x1, Inf X {x2, t}}, Inf X {Sup X {y, x2}, Sup X {y, t}}} =
                Inf X {Sup X {x1, Inf X {x2, t}},  Sup X {y, Inf X {x2, t}}}"
        by (simp add: B11)
      have B13:"... = Sup X {Inf X {x2, t}, Inf X {x1, y}}"
        by (simp add: B01 B450 assms bsup_commute2 distr_latticeD2 lattD41 sinfD4)
      have B14:"... = Sup X {Inf X {x1, y}, Inf X {x2, t}}"
        by (simp add: insert_commute)
      have B15:"Sup X {Inf X {x1, y}, Inf X {x2, t}} = Inf X {Sup X {x1, Inf X {x2, t}}, Inf X {Sup X {y, x2}, Sup X {y, t}}} "
        using B11 B13 B14 by presburger
      have B16:"... =  Inf X {Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}}, Sup X {y, t}}"
        by (simp add: B01 B450 binf_assoc1 lattD41 lattD42 sinfD4 ssupD4)
      have B17:"z \<ge> Sup X {Inf X {x1, y}, Inf X {x2, t}}"
        by (metis A1 B01 B3 B4 B5 bsup_iff filterD21 filter_bsup_mem_iff filters_on_iff filters_on_lattice_bsup8 lattD41 lattD42 sinfD4)
      have B18:"z \<ge>  Inf X {Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}}, Sup X {y, t}}"
        using B11 B13 B14 B16 B17 by presburger
      have B19:"Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}} \<in> f"
        by (simp add: B10)
      have B20:"Sup X {y, t} \<in> Inf ?F {g, h}"
        by (metis A1 B01 B8 B9 IntI filters_on_iff filters_on_lattice_inf8b inf_equality)
      have B21:"z \<in> binary_filter_sup X f ?igh"
        by (metis A1 B01 B10 B18 B20 B3 filter_bsup_mem_iff filters_on_iff filters_on_lattice_bsup8)
      have B22:" binary_filter_sup X f ?igh = Sup ?F {f, ?igh}"
        by (metis A1 B01 B02 filters_on_iff filters_on_lattice_bsup8 lattD41 sinfD4)
      show "z \<in> Sup ?F {f, ?igh}"
        using B21 B22 by blast
    qed
  qed
  show ?thesis
    by (simp add: B02 B1 distr_latticeI1)
qed
(*
TODO:  the converse: first prove some lemmas about sublattices and inheritance then specify
       using the principal embedding.  Or just use the latter straight off the bat.
*)

(*
                   (y \<or> x2) \<and> (y \<or> t) = y \<or> (x2 \<and> t)

(x1 \<or> (x2 \<and> t)) \<and> (y \<or> x2) \<and> (y \<or> t) = (x1 \<or> (x2 \<and> t)) \<and> (y \<or> (x2 \<and> t))

= (x2 \<and> t) \<or> (x1 \<and> y)

*)



definition sup_prime::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "sup_prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup R X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

definition inf_prime::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "inf_prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Inf X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

lemma sup_primeD1:
  "\<lbrakk>sup_prime X A; a \<in> X; b \<in> X; Sup R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:sup_prime_def)

lemma inf_primeD1:
  "\<lbrakk>inf_prime X A; a \<in> X; b \<in> X; Inf X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:inf_prime_def)

lemma sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Sup R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> sup_prime X A"
  by (simp add:sup_prime_def)

lemma inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Inf X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> inf_prime X A"
  by (simp add:inf_prime_def)

definition elem_sup_prime::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "elem_sup_prime X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x \<le> Sup R X {a, b} \<longrightarrow> (x \<le> a \<or> (x, b)\<in>R))"

definition elem_inf_prime::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "elem_inf_prime X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x \<ge> Inf X {a, b} \<longrightarrow> (x \<ge> a \<or> x \<ge> b))"

lemma elem_sup_primeD1:
  "\<lbrakk>elem_sup_prime X x; a \<in> X; b \<in> X; x \<le> Sup R X {a, b}\<rbrakk> \<Longrightarrow> (x \<le> a \<or> (x, b)\<in>R)"
  by(simp add:elem_sup_prime_def)

lemma elem_inf_primeD1:
  "\<lbrakk>elem_inf_prime X x; a \<in> X; b \<in> X; x \<ge> Inf X {a, b}\<rbrakk> \<Longrightarrow> (x \<ge> a \<or> x \<ge> b)"
  by(simp add:elem_inf_prime_def)

lemma elem_sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x \<le> Sup R X {a, b}\<rbrakk> \<Longrightarrow> (x \<le> a \<or> (x, b)\<in>R)) \<Longrightarrow> elem_sup_prime X x"
  by (simp add:elem_sup_prime_def)

lemma elem_inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x \<ge> Inf X {a, b}\<rbrakk> \<Longrightarrow> (x \<ge> a \<or> x \<ge> b)) \<Longrightarrow> elem_inf_prime X x"
  by (simp add:elem_inf_prime_def)

lemma elem_sup_primeE1:
  "\<lbrakk>x \<in> X; elem_sup_prime X x\<rbrakk> \<Longrightarrow> sup_prime X ([x)\<^sub>X)"
  by (metis elem_sup_prime_def lorcD12 lorcI1 sup_prime_def)       

lemma elem_inf_primeE1:
  "\<lbrakk>x \<in> X; elem_inf_prime X x\<rbrakk> \<Longrightarrow> inf_prime X ((x]\<^sub>X)"
  by (metis elem_inf_prime_def rolcD12 rolcI1 inf_prime_def)

lemma elem_sup_primeI2:
  "\<lbrakk>x \<in> X;sup_prime X ([x)\<^sub>X); is_sup_semilattice R X\<rbrakk> \<Longrightarrow> elem_sup_prime X x"
  by (metis elem_sup_prime_def lorcD12 lorcI1 ssupD4 sup_prime_def)

lemma elem_inf_primeI2:
  "\<lbrakk>x \<in> X; inf_prime X ((x]\<^sub>X); is_inf_semilattice X\<rbrakk> \<Longrightarrow> elem_inf_prime X x"
  by (metis elem_inf_prime_def rolcD12 rolcI1 sinfD4 inf_prime_def)


definition fin_sup_irr::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "fin_sup_irr X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Sup R X {a, b} \<longrightarrow> (x = a \<or> x = b))" 

definition fin_inf_irr::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where 
  "fin_inf_irr X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Inf X {a, b} \<longrightarrow> x = a \<or> x =b)"

lemma fin_sup_irrD1:
  "\<lbrakk>fin_sup_irr X x; a \<in> X; b \<in> X; x=Sup R X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_sup_irr_def)

lemma fin_inf_irrD1:
  "\<lbrakk>fin_inf_irr X x; a \<in> X; b \<in> X; x=Inf X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_inf_irr_def)

lemma fin_sup_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Sup R X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_sup_irr X x"
  by (simp add: fin_sup_irr_def)

lemma fin_inf_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Inf X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_inf_irr X x"
  by (simp add: fin_inf_irr_def)

lemma fin_sup_irrE1:
  "\<lbrakk>distributive_lattice X; x \<in> X; elem_sup_prime X x\<rbrakk> \<Longrightarrow> fin_sup_irr X x"
  by (simp add: bsup_iff distributive_lattice_def elem_sup_primeD1 fin_sup_irr_def lattD42 order_class.order_eq_iff)

lemma fin_inf_irrE1:
  "\<lbrakk>distributive_lattice X; x \<in> X; elem_inf_prime X x\<rbrakk> \<Longrightarrow> fin_inf_irr X x"
  by (simp add: binf_iff distributive_lattice_def elem_inf_primeD1 fin_inf_irr_def lattD41 order_class.order_eq_iff)
(*(\<forall>a \<in> X. \<forall>b \<in> X. x \<le> Sup R X {a, b} \<longrightarrow> (x \<le> a \<or> (x, b)\<in>R))*)
(*(\<forall>a \<in> X. \<forall>b \<in> X. x = Sup R X {a, b} \<longrightarrow> (x = a \<or> x = b)*)

(*
  x \<le> a \<or> b \<longleftrightarrow> x \<and> (a \<or> b) = x \<longleftrightarrow> (x \<and> a) \<or> (x \<and> b) = x \<longleftrightarrow> (x \<and> a) = a \<or> (x \<and> b) = x \<longleftrightarrow> x \<le> a \<or> (x, b)\<in>R
*)

lemma elem_sup_primeI3:
  assumes A0:"distributive_lattice X" and A1:"x \<in> X" and A2: "fin_sup_irr X x"
  shows "elem_sup_prime X x"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> x \<le> Sup R X {a, b} \<longrightarrow> (x \<le> a \<or> (x, b)\<in>R)"
  proof
    fix a b assume P:"a \<in> X \<and>b \<in> X \<and> x \<le> Sup R X {a, b}"
    have B1:"x = Inf X {x, Sup R X {a, b}}"
      using A0 A1 P distributive_lattice_def lattD42 le_inf1 ssupD4 by fastforce
    have B2:"... = Sup X {Inf X {x, a}, Inf X {x, b}}"
      by (simp add: A0 A1 P distr_latticeD3)
    have B3:"x = Inf X {x, a} \<or> x = Inf X {x, b}"
      by (metis A0 A1 A2 B1 B2 P distributive_lattice_def fin_sup_irr_def lattD41 sinfD4)
    show "x \<le>a \<or> (x, b)\<in>R"
      by (metis A0 A1 B3 P distributive_lattice_def latt_le_iff1)
  qed
  show ?thesis
    by (simp add: B0 elem_sup_primeI1)
qed
  
  
lemma elem_inf_primeI3:
  assumes A0:"distributive_lattice X" and A1:"x \<in> X" and A2: "fin_inf_irr X x"
  shows "elem_inf_prime X x"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> x \<ge> Inf X {a, b} \<longrightarrow> (x \<ge> a \<or> x \<ge> b)"
  proof
    fix a b assume P:"a \<in> X \<and>b \<in> X \<and> x \<ge> Inf X {a, b}"
    have B1:"x = Sup X {x, Inf X {a, b}}"
      using A0 A1 P distributive_lattice_def ge_sup2 lattD41 sinfD4 by fastforce
    have B2:"... = Inf X {Sup X {x, a}, Sup X {x, b}}"
      by (simp add: A0 A1 P distr_latticeD1)
    have B3:"x = Sup X {x, a} \<or> x = Sup X {x, b}"
      by (metis A0 A1 A2 B1 P distributive_lattice_def fin_inf_irr_def lattD42 ssupD4)
    show "x \<ge>a \<or> x \<ge> b"
      by (metis A0 A1 B3 P distributive_lattice_def latt_ge_iff2)
  qed
  show ?thesis
    by (simp add: B0 elem_inf_primeI1)
qed


lemma sup_prime_iff:
  "\<lbrakk>distributive_lattice X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_sup_prime X x \<longleftrightarrow> fin_sup_irr X x)"
  using elem_sup_primeI3 fin_sup_irrE1 by auto

lemma inf_prime_iff:
  "\<lbrakk>distributive_lattice X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_inf_prime X x \<longleftrightarrow> fin_inf_irr X x)"
  using elem_inf_primeI3 fin_inf_irrE1 by auto

lemma fin_sup_irrI2:
  "\<lbrakk>distributive_lattice X; x \<in> X;  sup_prime X ([x)\<^sub>X)\<rbrakk> \<Longrightarrow> fin_sup_irr X x"
  by (simp add: distributive_lattice_def elem_sup_primeI2 fin_sup_irrE1 lattD42)
  
lemma fin_inf_irrI2:
  "\<lbrakk>distributive_lattice X; x \<in> X; inf_prime X ((x]\<^sub>X)\<rbrakk> \<Longrightarrow> fin_inf_irr X x"
  by (simp add: distributive_lattice_def elem_inf_primeI2 fin_inf_irrE1 lattD41)
  
lemma sup_primeI4:
  "\<lbrakk>distributive_lattice X; x \<in> X; fin_sup_irr X x\<rbrakk> \<Longrightarrow> sup_prime X ([x)\<^sub>X)"
  by (simp add: elem_sup_primeE1 elem_sup_primeI3)

lemma inf_primeI4:
  "\<lbrakk>distributive_lattice X; x \<in> X; fin_inf_irr X x\<rbrakk> \<Longrightarrow> inf_prime X ((x]\<^sub>X)"
  by (simp add: elem_inf_primeE1 elem_inf_primeI3)

lemma sup_prime_pfilterD1:
  "\<lbrakk>sup_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup R X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma sup_prime_pfilterD2:
  "\<lbrakk>is_lattice X; sup_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup R X {a, b}) \<in> A)"
  using filter_on_lattice_sup01 is_pfilterD1 lattice_filter_memI by blast

lemma sup_prime_pfilterD3:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  apply(auto simp add:sup_prime_def)  by (meson filterD21 filters_on_lattice_inf02 in_mono)

lemma sup_prime_pfilterD4:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F; is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F"
  using sup_prime_pfilterD3 by blast

lemma lorc_sup_filter_subset:
  "\<lbrakk>is_lattice X; (\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F); is_filter X F\<rbrakk> \<Longrightarrow>(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup R X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F))"
proof-
  assume A0:"is_lattice X" "(\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)" "is_filter X F"
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> (Sup R X {a, b}) \<in> F \<longrightarrow> (a \<in> F \<or> b \<in> F)" 
  proof 
    fix a b assume A1:"a \<in> X \<and> b \<in> X \<and> (Sup R X {a, b}) \<in> F"
    let ?F1="(lorc R X a)" let ?F2="([b)\<^sub>X)"
    have B1:"?F1 \<inter> ?F2 \<subseteq> F" using lorc_inter[of X a b] A0(1,3) A1 filter_memI is_pfilterD1 lorcD12 lorc_subset1 by blast
    have B2:"is_filter X ?F1 \<and> is_filter X ?F2"  by (simp add: A1 lorc_filter)
    have B3:"?F1 \<subseteq> F \<or> ?F2 \<subseteq> F"  by (simp add: A0(2) B1 B2)
    show "a \<in> F \<or> b \<in> F"
      by (meson A1 B3 in_mono lorc_memI1)
  qed
  show "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup R X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F))"
    by (simp add: B0)
qed

lemma sup_prime_pfilterI2:
  "\<lbrakk>is_lattice X; (\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F); is_pfilter X F\<rbrakk> \<Longrightarrow> sup_prime X F"
  by (simp add: is_pfilterD1 lorc_sup_filter_subset sup_primeI1)


lemma not_prime_obtain:
  assumes A0:"is_lattice X" and A1:"is_pfilter X F" and A2:"\<not>(sup_prime X F)"
  obtains x y where "x \<in> X \<and> y \<in> X \<and> Sup R X {x, y} \<in> F \<and> x \<notin> F \<and> y \<notin> F"
  using A2 sup_prime_def by blast


abbreviation pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "pfilter X A \<equiv> (is_filter X A) \<and> X \<noteq> A"

abbreviation pideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "pideal X A \<equiv> (is_ideal X A) \<and> X \<noteq> A"


abbreviation pfilters_on::"'a::order set \<Rightarrow> 'a::order set set" where
  "pfilters_on X \<equiv> {F. pfilter X F}"

lemma maximal_pfilterD1:
  "is_maximal (pfilters_on X) F \<Longrightarrow> H \<in>pfilters_on X \<Longrightarrow> F \<subseteq> H \<Longrightarrow> F=H  "
  using maximalD2 by blast
     
lemma maximal_pfilterI1:
  "\<lbrakk>F \<in> pfilters_on X; (\<And>H. \<lbrakk>H  \<in> pfilters_on X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F =H)\<rbrakk> \<Longrightarrow>  is_maximal (pfilters_on X) F "
  using maximalI1[of F "pfilters_on X"]  by auto

lemma maximal_pfilterI2:
  "\<lbrakk>F \<in> pfilters_on X; (\<And>H. \<lbrakk>H  \<in> pfilters_on X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F \<supseteq> H)\<rbrakk> \<Longrightarrow>  is_maximal (pfilters_on X) F "
  by (simp add: is_maximal_def)

lemma primefilterD1:
  "\<lbrakk>sup_prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup R X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma primeidealD1:
  "\<lbrakk>inf_prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Inf X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: inf_prime_def)

lemma primefilterD2:
  "\<lbrakk>is_lattice X; sup_prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup R X {a, b}) \<in> A)"
  by (metis doubleton_eq_iff filter_on_lattice_sup01)

lemma primefilterD3:
  "\<lbrakk>is_lattice X; sup_prime X F; pfilter X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  apply(auto simp add:sup_prime_def) apply (meson filterD2 filters_on_lattice_inf02 in_mono) using filterD21 by blast

lemma notprimeobtain:
  assumes A0:"is_lattice X" and A1:"pfilter X F" and A2:"\<not>(sup_prime X F)"
  obtains x y where "x \<in> X \<and> y \<in> X \<and> Sup R X {x, y} \<in> F \<and> x \<notin> F \<and> y \<notin> F"
  using A2 sup_prime_def by blast

(*
need more robust intro and dest lemmas for filters and more generally  ord closure and directedness
 
*)

lemma element_filter:
  assumes A0:"is_lattice X" and A1:"is_filter X F" and A2:"a \<in> X"
  defines "G \<equiv> {x \<in> X. \<exists>y \<in> F. Inf X {a, y} \<le> x}"
  shows "is_filter X G"
proof-
  have B0:"G \<subseteq> X"
    by (simp add: G_def)
  have B1:"\<And>x1 x2. x1 \<in> G \<and> x2 \<in> G \<longrightarrow> Inf X {x1, x2} \<in> G"
  proof
    fix x1 x2 assume A3:"x1 \<in> G \<and> x2 \<in> G"
    obtain y1 y2 where B2:"y1 \<in> F \<and> y2 \<in> F \<and> Inf X {a, y1} \<le> x1 \<and> Inf X {a, y2} \<le> x2"
      using A3 G_def by blast
    have B3:"Inf X {y1, y2} \<in> F"
      by (simp add: A0 A1 B2 filter_finf_closed1 lattD41)
    have B30:"Inf X {y1, y2} \<in> X \<and> a \<in> X \<and> x1 \<in> X \<and> x2 \<in> X \<and> y1 \<in> X \<and> y2 \<in> X"
      using A1 A2 A3 B0 B2 B3 filterD21 by blast
    have B4:"Inf X {x1, x2} \<ge> Inf X {Inf X {a, y1}, Inf X {a, y2}}"
      by (simp add: A0 B2 B30 binf_leI5 lattD41 sinfD4)
    have B5:" Inf X {Inf X {a, y1}, Inf X {a, y2}}  = Inf X {a, Inf X {y1, y2}}"
      using inf_semilattice_finf_props5[of X a y1 y2] A0 B30 lattD41[of X] by fastforce
    have B6:"Inf X {Inf X {y1, y2}, a} \<le> Inf X {x1, x2}"
      by (metis B4 B5 insert_commute)
    have B7:"\<exists>y \<in> F. Inf X {a, y} \<le> Inf X {x1, x2}"
      using B3 B4 B5 by auto
    show "Inf X {x1, x2} \<in> G"
      using A0 B3 B30 B4 B5 G_def lattD41 sinfD4 by auto
  qed
  have B6:"\<And>x g. g \<in> G \<and> x \<in> X \<and> g \<le> x \<longrightarrow> x \<in> G"
    using G_def order.trans by auto
  have B7:"G \<noteq> {}"
    by (metis (no_types, lifting) A0 A1 A2 G_def empty_iff equals0I filterD1 filterD21 latt_iff mem_Collect_eq order_refl sinfD4)
  have B8:"\<And>a b. a \<in> G \<and> b \<in> G \<longrightarrow> (\<exists>c\<in>G. c \<le> a \<and> c \<le> b)"
  proof
    fix a b assume A4:" a \<in> G \<and> b \<in>G"
    have B9:"Inf X {a, b} \<in> G \<and> Inf X {a, b} \<le> a \<and> Inf X {a, b} \<le> b"
      by (meson A0 A4 B0 B1 binf_leI1 binf_leI2 dual_order.refl in_mono lattD41) 
    show "\<exists>c\<in>G. c \<le> a \<and> c \<le> b"
      using B9 by auto
  qed
  have B10:"is_dir G (\<ge>)"
    by (simp add: B8 is_dwdirI1)
  have B11:"is_ord_cl X F (\<le>)"
    by (simp add: A1 filterD4)
  show ?thesis
    by (simp add: B0 B10 B6 B7 filterI1 is_ord_clI1)
qed  

lemma primefilterI2:
  assumes A0:"is_lattice X" and A1:"pfilter X F" and 
          A2:"(\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)"
  shows "sup_prime X F"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> (Sup R X {a, b}) \<in> F \<longrightarrow> (a \<in> F \<or> b \<in> F)"
  proof
    fix a b assume A3:" a \<in> X \<and> b \<in> X \<and> (Sup R X {a, b}) \<in> F"
    have B1:"((lorc R X a) \<inter> ([b)\<^sub>X)) \<subseteq> F"
      apply(auto simp add:lorc_def)  by (meson A0 A1 A3 binary_supD4 filterD4 is_ord_clE1 lattD32 latt_iff ssupD4)
    have B2:"(lorc R X a) \<subseteq> F \<or> ([b)\<^sub>X) \<subseteq> F"
      by (simp add: A2 A3 B1 lorc_filter)
    show "(a \<in> F \<or> b \<in> F)"
      using A3 B2 lorc_memI1 by blast
  qed
  show ?thesis
    by (simp add: B0 sup_prime_def)
qed


lemma primefilterI1:
  "\<lbrakk>is_lattice X;  pfilter X A; (\<forall>a b. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup R X {a, b}) \<in> A)) \<rbrakk> \<Longrightarrow> sup_prime X A"
  by (simp add: sup_prime_def)

lemma primefilter_iff1:
  "is_lattice X \<Longrightarrow> ( sup_prime X A \<and> pfilter X A) \<longleftrightarrow> (pfilter X A \<and>  (\<forall>a \<in> X. \<forall>b \<in> X. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup R X {a, b}) \<in> A)))"
  by (metis sup_prime_def primefilterD2)

lemma prime_filter_iff2:
  "is_lattice X \<Longrightarrow>  (sup_prime X F \<and> pfilter X F)  \<longleftrightarrow>  (pfilter X F \<and> (\<forall>F1 F2. is_filter X F1 \<and> is_filter X F2 \<and> F1 \<inter> F2 \<subseteq> F \<longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F))"
  by (metis primefilterD3 primefilterI2)

lemma prime_filter_fin_irr1:
  "\<lbrakk>is_lattice X; sup_prime X F; pfilter X F; G \<in> filters_on X; H \<in> filters_on X; G \<inter> H = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (meson filters_on_iff inf.cobounded1 inf.cobounded2 primefilterD3 subset_antisym)

lemma prime_filter_fin_irr2:
  "\<lbrakk>is_lattice X; sup_prime X F; pfilter X F; G \<in> filters_on X; H \<in> filters_on X; Inf (filters_on X) {G, H} = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (simp add: filters_lattice_inf_op prime_filter_fin_irr1)

lemma prime_filter_irr3:
  "\<lbrakk>is_lattice X; sup_prime X F; pfilter X F\<rbrakk> \<Longrightarrow> fin_inf_irr (filters_on X) F"
  by (metis fin_inf_irr_def prime_filter_fin_irr2)

lemma proper_principal_prime:
  "\<lbrakk>pfilter X lorc R X a; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup R X {x, y}\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> a \<le> y)\<rbrakk> \<Longrightarrow> sup_prime X lorc R X a"
  by (metis lorcD12 lorcI1 sup_prime_def)

lemma proper_principal_prime2:
  "\<lbrakk>is_lattice X; pfilter X lorc R X a; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup R X {x, y}\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> a \<le> y)\<rbrakk> \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a = Sup R X {x, y}\<rbrakk> \<Longrightarrow> a =x \<or> a=y)"
  by (metis binary_supD31 binary_supD32 is_supE1 lattD32 order_class.order_eq_iff)

lemma proper_principal_fin_irr:
  "\<lbrakk>is_lattice X; pfilter X lorc R X a; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup R X {x, y}\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> a \<le> y)\<rbrakk> \<Longrightarrow>fin_inf_irr (filters_on X) lorc R X a"
  by (simp add: prime_filter_irr3 proper_principal_prime)


lemma fin_irr_filter_prime:
  "\<lbrakk>distributive_lattice X;pfilter X F;fin_inf_irr (filters_on X) F\<rbrakk> \<Longrightarrow> inf_prime X F"
  by (meson distributive_lattice_def filterD4 inf_primeI1 is_ord_clE1 lattD41 rolcD1 rolc_inf_latticeD1)
(*on lattice prime filters are finite inf irr
  prime_filter_irr3 
    \<lbrakk>is_lattice X; sup_prime X F; pfilter X F\<rbrakk> \<Longrightarrow> fin_inf_irr (filters_on X) F"
  while if the lattice is distributive the conver
*)

lemma distr_lattice_maximal_prime:
  assumes A0:"distributive_lattice X" and A1:"is_maximal (pfilters_on X) F" 
  shows "sup_prime X F"
proof-
  have B00:"is_lattice X"
    using A0 distributive_lattice_def by blast
  have B0:"pfilter X F"
    using A1 maximalD1 by auto
  have P:"\<And>a b. a \<in> X \<and> b \<in> X \<and> Sup R X {a, b} \<in> F \<and>  a \<notin> F \<longrightarrow> b \<in> F"
  proof
    fix a b assume A2:"a \<in> X \<and> b \<in> X \<and> Sup R X {a, b} \<in> F \<and> a \<notin> F"
    let ?Fa="binary_filter_sup X F lorc R X a"
    have B1:"a \<in> ?Fa - F"
      by (metis A0 A2 B0 DiffI distributive_lattice_def filters_on_lattice_bsup02 lorc_filter lorc_memI1)
    have B2:"F \<subset> ?Fa"
      by (metis A0 A2 B0 B1 DiffD1 distributive_lattice_def filters_on_lattice_bsup03 lorc_filter order_neq_le_trans)
    have B3:"?Fa \<notin> pfilters_on X"
      using A1 B2 maximalD4 by auto
    have B4:"?Fa \<in> filters_on X"
      by (metis A0 A2 B0 distributive_lattice_def filters_on_lattice_bsup4 lorc_filter)
    have B5:"?Fa = X"
      using B3 B4 filters_on_def by blast
    have B6:"b \<in> ?Fa"
      by (simp add: A2 B5)
    obtain f c where B7:"f \<in> F \<and> c \<in> (lorc R X a) \<and> b \<ge> Inf X {f, c}"
      using B6 binary_filter_sup_obtains by blast
    have B8:"b = Sup X {b, Inf X {f, c}}"
      by (metis A0 A2 B0 B7 distributive_lattice_def filterD2 ge_sup2 lattD41 lorc_filter sinfD4 subset_iff)
    have B9:"... = Inf X {Sup X {b, f}, Sup X {b, c}}"
      by (meson A0 A2 B0 B7 distr_latticeD1 filterD21 lorcD11)
    have B10:"Sup X {b, f} \<in> F \<and> Sup X {b, c} \<in> (lorc R X a) \<and> b = Inf X {Sup X {b, f}, Sup X {b, c}}"
      by (metis A0 A2 B0 B7 B8 B9 distributive_lattice_def filter_on_lattice_sup01 lorc_filter)
    let ?f="Sup X {b, f}" and ?c="Sup X {b, c}"
    have B11:"?c \<ge> a"
      using B10 lorcD12 by blast
    have B110:"b \<in> X \<and> ?f \<in> X \<and> ?c \<in> X \<and> c \<in> X \<and> a \<in> X"
      using A2 B0 B10 B7 filterD21 lorcD11 by blast
    have B111:"Sup X {b, ?f} \<ge> ?f"
      by (meson A0 B110 bsup_geI2 distributive_lattice_def dual_order.refl lattD42)
    have B112:"Sup X {b, ?c} \<ge> Sup X {b, a}"
      by (simp add: B00 B11 B110 bsup_geI5 lattD42)
    have B12:"b = Sup X {b, Inf X {?f, ?c}}"
      using A2 B10 bsup_idem1 by force
    have B13:"... = Inf X {Sup X {b, ?f}, Sup X {b, ?c}}"
      by (meson A0 A2 B0 B10 distr_latticeD1 filterD21 lorcD11)
    have B14:"... \<ge> Inf X {?f, Sup X {b, a}}"
      by (simp add: B00 B110 B111 B112 binf_leI5 lattD41 lattD42 ssupD4)
    have B15:"... \<in> F"
      by (metis (full_types) A2 B0 B00 B10 B110 B112 filter_finf_closed1 filter_memI insert_commute lattD41 lattice_absorb1)
    show "b \<in> F"
      using B12 B13 B15 by presburger
  qed
  show ?thesis
    by (meson P sup_primeI1)
qed



lemma tmp0:"\<lbrakk>a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Inf X {b, a}|a. a \<in> {a1}} = {Inf X {b, a1}}" by auto
lemma tmp1:"\<lbrakk>a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Inf X {b, a}|a. a \<in> {a1, a2}} = {Inf X {b, a1}, Inf X {b, a2}}" by auto
lemma tmp2:"\<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}; b \<in> X\<rbrakk> \<Longrightarrow>{Inf X {b, a}|a. a \<in>A} = (\<lambda>a. Inf X {b, a})`A" by auto


lemma tmp3:"\<lbrakk>a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Sup X {b, a}|a. a \<in> {a1}} = {Sup X{b, a1}}" by auto
lemma tmp4:"\<lbrakk>a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Sup  X {b, a}|a. a \<in> {a1, a2}} = {Sup X {b, a1}, Sup X {b, a2}}" by auto
lemma tmp5:"\<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}; b \<in> X\<rbrakk> \<Longrightarrow>{Sup X {b, a}|a. a \<in>A} = (\<lambda>a. Sup X {b, a})`A" by auto



lemma distr_eq_tmp0:"\<lbrakk>is_lattice X; a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf X {b, (Sup X {a1})} = Sup X {Inf X {b, a}|a. a \<in> {a1}}" by (simp add: lattD41 sinfD4 sup_singleton2) 
lemma distr_eq_tmp1:"\<lbrakk>distributive_lattice X; a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf X {b, Sup X {a1, a2}} = Sup X {Inf X {b, a}|a. a \<in> {a1, a2}}" using distr_latticeD3 tmp1 by fastforce


lemma distr_eq_tmp2:"\<lbrakk>is_lattice X; a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup X{b, (Inf X {a1})} = Inf X {Sup X {b, a}|a. a \<in> {a1}}"  by (simp add: inf_singleton2 lattD42 ssupD4)
lemma distr_eq_tmp3:"\<lbrakk>distributive_lattice X; a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup X {b, (Inf X {a1, a2})} = Inf X {Sup X {b, a}|a. a \<in> {a1, a2}}" using distr_latticeD1 tmp4 by fastforce


lemma l_inf_closed:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> X" by (simp add: lattD41 sinfD4)
lemma l_finsup:"\<lbrakk>is_lattice X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s"  using bsup_finite2 lattD42 by blast 
lemma s_fininf:"\<lbrakk>is_inf_semilattice X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf X A s" using binf_finite2 by auto 
lemma s_finsup:"\<lbrakk>is_sup_semilattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s" using bsup_finite2 by auto 

lemma l_sup_closed:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> X" by (simp add: lattD42 ssupD4)
lemma l_fininf:"\<lbrakk>is_lattice X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf X A s"  using binf_finite2 lattD41 by blast 


lemma sup_insert9: "\<lbrakk>is_sup Y A s1; is_sup Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (ubd R  Y (insert x A))" by (simp add: is_supD1121 sup_insert62 ubd_mem_insert)
lemma inf_insert9: "\<lbrakk>is_inf Y A s1; is_inf Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (lbd R Y (insert x A))" by (simp add: is_infD1121 inf_insert62 lbd_mem_insert)



lemma sup_ubd: "\<lbrakk>is_sup Y F s; is_sup Y {x, s} t\<rbrakk> \<Longrightarrow> is_sup Y (insert x F) t"  by(rule is_supI1, simp add: insert_commute leastI3 sup_insert7 sup_insert9)
lemma sup_ex:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {x, y} (Sup R X {x, y})" by (simp add: lattD32)
lemma ssup_ex:"\<lbrakk>is_sup_semilattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {x, y} (Sup R X {x, y})" by (simp add: ssupD3)

lemma inf_lbd: "\<lbrakk>is_inf Y F s; is_inf Y {x, s} t\<rbrakk> \<Longrightarrow> is_inf Y (insert x F) t" by (rule is_infI1, simp add: insert_commute greatestI3 inf_insert7 inf_insert9)
lemma inf_ex:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_inf X {x, y} (Inf X {x, y})" by (simp add: lattD31)

lemma sinf_ex:"\<lbrakk>is_inf_semilattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_inf X {x, y} (Inf X {x, y})" by (simp add: sinfD3)



lemma fsup_insert:"\<lbrakk>is_lattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, (Sup X F)} = Sup X (insert x F)"  by (metis l_finsup is_supE1 sup_equality sup_ex sup_ubd)
lemma finf_insert:"\<lbrakk>is_lattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, (Inf X F)} = Inf X (insert x F)"  by (metis l_fininf is_infE1 inf_equality inf_ex inf_lbd)

             
lemma sfsup_insert:"\<lbrakk>is_sup_semilattice R X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, (Sup X F)} = Sup X (insert x F)"  by (metis bsup_finite2 is_supE1 ssupD3 sup_equality sup_ubd) 
lemma sfinf_insert:"\<lbrakk>is_inf_semilattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, (Inf X F)} = Inf X (insert x F)"  by (metis binf_finite2 is_infE1 sinfD3 inf_equality inf_lbd)




lemma distr_finite2:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf X {b, (Sup X {a1, a2})} = Sup X {Inf X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice X"
  shows "Inf X {b, (Sup X A)} = Sup X {Inf X {b, a}|a. a \<in> A}"
  using A2 A3 A4 A1 A0
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A5 by fastforce 
next
  case (insert x F)
  obtain P0:"x \<in> X" and P1:"F \<subseteq> X" and P2:"finite F" and P3:"F \<noteq> {}"
    using insert.hyps(1,2) insert.prems(1) by blast
  have L:"is_lattice X"  by (simp add: A5 distr_latticeD5) 
  let ?ba="{Inf X {b, a} |a::'a. a \<in> F}" and ?xba="{Inf X {b, a}|a. a \<in> (insert x F)}"
  let ?s="Sup X F" and ?sba="Sup X ?ba" and ?sxba="Sup X ?xba"
  have P4:"?ba \<subseteq> X" using L A0 P1 l_inf_closed by blast 
  have P5:"?xba \<subseteq> X" using L A0 P0 P1 l_inf_closed by blast
  have P6:"finite ?ba" using P2 by force
  have P7:"finite ?xba"  by (simp add: insert.hyps(1))
  have P8:"?xba = {Inf X {b, x}} \<union> ?ba" by (auto)
  have P9:"Inf X {b, x} \<in> X" by (simp add: L A0 P0 l_inf_closed) 
  have P10:"?ba \<noteq> {}"  using P3 by blast
  have P11:"?xba \<noteq> {}" using P3 by blast
  have P12:"?sba \<in> X" using L P10 P4 P6 bsup_finite2 is_supE1 latt_iff by blast 
  have P13:"?sxba \<in> X" using L P11 P5 P7 bsup_finite2 is_supE1 latt_iff by blast 
  have P14:"(Sup X {?sba, (Inf X {b, x})}) \<in> X" using  P12 P9  L l_sup_closed by blast 
  have B0:"Inf X {b, ?s} = ?sba"  using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Inf X {b, (Sup X {?s, x})} = Sup X {(Inf X {b, ?s}), (Inf X {b, x})}" by (meson A0 A5 L P0 P1 P2 P3 bsup_finite2 distr_latticeD3 is_supE1 lattD42)
  have B2:"... = Sup X {(?sba), (Inf X {b, x})}"  using B0 by fastforce
  have B3:"... = Sup X {Inf X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" by blast
    have B5:"is_sup R X ?ba ?sba" by (simp add: P3 P4 P6 L l_finsup sup_exI)
    have B6:"is_sup R X {Inf X {b, x},?sba} (Sup X {(Inf X {b, x}), (?sba)} )" by (simp add: L P12 P9 lattD32) 
    have B7:"is_sup R X {Inf X {b, x},?sba} (Sup X {(?sba), (Inf X {b, x})})" by (metis B6 insert_commute) 
    have B8:"is_sup R X (insert (Inf X {b, x}) ?ba) (Sup X {(?sba), (Inf X {b, x})})"  using B5 B7 sup_ubd by blast 
    have B9:"insert (Inf X {b, x}) ?ba =  {Inf X {b, a}|a. a \<in> (insert x F)}"  using B5 B7 sup_ubd by blast
    show "(Sup X {(?sba), (Inf X {b, x})}) =  Sup X {Inf X {b, a}|a. a \<in> (insert x F)}"
      using B8 B9 sup_equality by force
  qed
  have B10:"Inf X {b, (Sup X {?s, x})} = Sup X {Inf X {b, a}|a. a \<in> (insert x F)}" using B0 B1 B3 by presburger
  have B11:"Inf X {b, (Sup X {?s, x})} = Inf X {b, (Sup X (insert x F))}"
  proof-
    have B12:"Sup X {Sup X F, x} = Sup X (insert x F)"
      by (simp add: L P0 P1 P2 P3 fsup_insert insert_commute)
    show " Inf X {b, Sup X {Sup X F, x}} = Inf X {b, Sup X (insert x F)}"
      by (simp add: B12)
  qed
  have B13:"Inf X {b, (Sup X (insert x F))} =  Sup X {Inf X {b, a}|a. a \<in> (insert x F)}" using B10 B11 by presburger
  then show ?case
    by auto
qed



lemma distr_finite1:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Sup X {b, (Inf X {a1, a2})} = Inf X {Sup X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice X"
  shows "Sup X {b, (Inf X A)} = Inf X {Sup X {b, a}|a. a \<in> A}"
  using A2 A3 A4 A1 A0
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A5 by fastforce 
next
  case (insert x F)
  obtain P0:"x \<in> X" and P1:"F \<subseteq> X" and P2:"finite F" and P3:"F \<noteq> {}"
    using insert.hyps(1,2) insert.prems(1) by blast
  have L:"is_lattice X"  by (simp add: A5 distr_latticeD5) 
  let ?ba="{Sup X {b, a} |a::'a. a \<in> F}" and ?xba="{Sup X {b, a}|a. a \<in> (insert x F)}"
  let ?s="Inf X F" and ?sba="Inf X ?ba" and ?sxba="Inf X ?xba"
  have P4:"?ba \<subseteq> X" using L A0 P1 l_sup_closed by blast 
  have P5:"?xba \<subseteq> X" using L A0 P0 P1 l_sup_closed by blast
  have P6:"finite ?ba" using P2 by force
  have P7:"finite ?xba"  by (simp add: insert.hyps(1))
  have P8:"?xba = {Sup X {b, x}} \<union> ?ba" by (auto)
  have P9:"Inf X {b, x} \<in> X" by (simp add: L A0 P0 l_inf_closed) 
  have P10:"?ba \<noteq> {}"  using P3 by blast
  have P11:"?xba \<noteq> {}" using P3 by blast
  have P12:"?sba \<in> X" using L P10 P4 P6 binf_finite2 is_infE1 latt_iff by blast 
  have P13:"?sxba \<in> X" using L P11 P5 P7 binf_finite2 is_infE1 latt_iff by blast 
  have P14:"(Inf X {?sba, (Sup X {b, x})}) \<in> X" by (simp add: A0 L P0 P12 l_inf_closed l_sup_closed)
  have B0:"Sup X {b, ?s} = ?sba"  using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Sup X {b, (Inf X {?s, x})} = Inf X {(Sup X {b, ?s}), (Sup X {b, x})}" by (meson A0 A5 L P0 P1 P2 P3 binf_finite2 distr_latticeD1 is_infE1 lattD41)
  have B2:"... = Inf X {(?sba), (Sup X {b, x})}"  using B0 by fastforce
  have B3:"... = Inf X {Sup X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" by blast
    have B5:"is_inf X ?ba ?sba" by (simp add: P3 P4 P6 L l_fininf inf_exI)
    have B6:"is_inf X {Sup X {b, x},?sba} (Inf X {(Sup X {b, x}), (?sba)} )" by (simp add: A0 L P0 P12 l_sup_closed lattD31)
    have B7:"is_inf X {Sup X {b, x},?sba} (Inf X {(?sba), (Sup X {b, x})})" by (metis B6 insert_commute) 
    have B8:"is_inf X (insert (Sup X {b, x}) ?ba) (Inf X {(?sba), (Sup X {b, x})})"  using B5 B7 inf_lbd by blast 
    have B9:"insert (Sup X {b, x}) ?ba =  {Sup X {b, a}|a. a \<in> (insert x F)}"  using B5 B7 inf_lbd by blast
    show "(Inf X {(?sba), (Sup X {b, x})}) =  Inf X {Sup X {b, a}|a. a \<in> (insert x F)}"   using B8 B9 inf_equality by force
  qed
  have B10:"Sup X {b, (Inf X {?s, x})} = Inf X {Sup X {b, a}|a. a \<in> (insert x F)}" using B0 B1 B3 by presburger
  have B11:"Sup X {b, (Inf X {?s, x})} = Sup X {b, (Inf X (insert x F))}"
  proof-
    have B12:"Inf X {Inf X F, x} = Inf X (insert x F)"by (simp add: L P0 P1 P2 P3 finf_insert insert_commute)
    show "Sup X {b, Inf X {Inf X F, x}} = Sup X {b, Inf X (insert x F)}"   by (simp add: B12)
  qed
  have B13:"Sup X {b, (Inf X (insert x F))} =  Inf X {Sup X {b, a}|a. a \<in> (insert x F)}" using B10 B11 by presburger
  then show ?case  by auto
qed


lemma fin_distr2:"\<lbrakk>distributive_lattice X ;finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Inf X {b, (Sup X  A)} = Sup X {Inf X {b, a}|a. a \<in> A}" using distr_finite2[of b X A]  by (simp add: distr_eq_tmp1)

lemma fin_distr1:"\<lbrakk>distributive_lattice X; finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Sup X{ b, (Inf X  A)} = Inf X {Sup X {b, a}|a. a \<in> A}"  using distr_finite1[of b X A]  by (simp add: distr_eq_tmp3)


lemma finite_ind_in:
  "\<lbrakk>is_inf_semilattice X; finite I; I \<noteq> {}; (\<forall>i. i \<in> I \<longrightarrow> f i \<in> X)\<rbrakk> \<Longrightarrow>is_inf X (f`I) (Inf X (f`I))"
  by (simp add: binf_finite2 image_subset_iff)

lemma finite_ind_fil:
   "\<lbrakk>is_inf_semilattice X; finite I; I \<noteq> {}; is_greatest X top; (\<forall>i. i \<in> I \<longrightarrow> is_filter X (f i))\<rbrakk> \<Longrightarrow> is_inf (filters_on X) (f`I) (\<Inter>(f`I))"
  by (simp add: filters_inf_semilattice_inf filters_on_iff image_subsetI pow_neI)

lemma finite_ind_fil_lattice:
   "\<lbrakk>is_lattice X; finite I; I \<noteq> {}; is_greatest X top; (\<forall>i. i \<in> I \<longrightarrow> is_filter X (f i))\<rbrakk> \<Longrightarrow> is_inf (filters_on X) (f`I) (\<Inter>(f`I))"
  by (simp add: finite_ind_fil lattD41)

lemma finite_ind_fil2:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and A3:"is_sup R X (x` I) s"
  shows "s \<in> (\<Inter>(f` I))"
proof-
  have B0:"\<And>i. i \<in> I \<longrightarrow> s \<in> f i"
    proof
      fix i assume A4:"i \<in> I"
      have B1:"(x i) \<in> (f i)" using A0 A1 A2 A4 by blast
      have B2:"(x i) \<in> (x` I)"  by (simp add: A4)
      have B5:"s \<in> X"  using A3 is_supE1 by auto
      have B6:"x i \<le> s" using A3 B2 by(rule is_supD1121[of X "x` I" s "x i"]) 
      show "s \<in> f i"   using A4 B1 B5 B6 assms(5) filter_memI by blast
  qed
  show "s \<in>  (\<Inter>(f` I))"
    using B0 by blast
qed

lemma finite_ind_fil3:
  fixes f::"'b \<Rightarrow> 'a::order set"  and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2: "s \<in> (\<Inter>(f` I))" 
  shows "\<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> is_sup R X (x` I) s"
proof-
  define x where "x = (\<lambda>(i::'b). s)"
  have B0:"is_sup R X (x` I) s"
    apply(rule is_supI7)
    apply (metis A2 InterD assms(4) assms(5) equals0I filterD21 imageI)
    apply (simp add: ub_imageI x_def)
    using assms(4) ubE x_def by fastforce
  have B1:" (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"
    using A2 x_def by blast
  show ?thesis
    using B0 B1 by auto
qed


lemma finite_ind_fil4:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" 
  shows "Sup X (x` I) \<in> \<Inter>(f`I)"
  using A0 A1 A2 finite_ind_fil2[of X top I f x]
  by (metis (full_types) empty_is_image filterD21 finite_imageI image_subset_iff l_finsup sup_equality)



lemma finite_ind_fil5:
  fixes f::"'b \<Rightarrow> 'a::order set"  and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2: "s \<in> (\<Inter>(f` I))" 
  shows "s \<in> {Sup X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  using A0 A1 A2 finite_ind_fil3[of X top I f s]  using sup_equality by fastforce

lemma finite_ind_fil6:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "\<Inter>(f`I) = {Sup X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  apply(auto)
  apply (metis assms(4) assms(5) ex_in_conv filterD2 image_constant_conv subset_eq sup_singleton2)
  by (metis (no_types, lifting) INT_E assms(1) assms(2) assms(3) assms(4) assms(5) finite_ind_fil4)

lemma exp_lattice_filter_inf:
 fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Inf (filters_on X) (f`I) = {Sup X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  using A0 A1 finite_ind_fil_lattice[of X I top f] finite_ind_fil6[of X top I f] 
        inf_equality[of "(filters_on X)" "f`I" "\<Inter>(f`I)"] by(auto)



lemma fpow_neI3:
  "\<lbrakk>A \<subseteq> X;finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> A \<in> Fpow_ne X"  by (simp add: fpow_neI)

lemma fpow_neD4:
  "A \<in> Fpow_ne X  \<Longrightarrow> A \<subseteq> X \<and> finite A \<and> A \<noteq> {}"
  by (simp add: fpow_ne_iff2)


lemma filter_closure_of_filters6_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup (filters_on X) A= (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters5_ne sup_equality)


lemma filter_closure_of_filters8_ne:
  "\<lbrakk>is_lattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup (filters_on X) A= (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters6_ne lattD41)

lemma filter_closure_of_filters9_ne:
  "\<lbrakk>distributive_lattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup (filters_on X) A= (filter_closure X (\<Union>A))"
  by (simp add: distr_latticeD5 filter_closure_of_filters8_ne)


lemma filter_closure_of_filters7:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> Sup (filters_on X) A = (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters5 sup_equality)

lemma filter_closure_of_filters8:
  "\<lbrakk>is_lattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> Sup (filters_on X) A = (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters7 lattD41)

lemma filter_closure_of_filters9:
  "\<lbrakk>distributive_lattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> Sup (filters_on X) A = (filter_closure X (\<Union>A))"
  by (simp add: distr_latticeD5 filter_closure_of_filters8)             




lemma finite_ind_fil7:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). Inf X F \<le> x}"
proof-
  let ?A="\<Union>(f`I)"
  have B0:"?A \<noteq> {}" using filterD1 A1 by force
  have B1:"filter_closure X (?A) = {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x} " using B0 by(rule filter_closure_ne_simp)
  have B2:"... = {x \<in> X. \<exists>F \<in> Fpow_ne ?A. Inf X F \<le> x}"  using fpow_ne_iff2 using fpow_ne_iff2 by(fastforce)
  have B3:"filter_closure X (?A) = {x \<in> X. \<exists>F \<in> Fpow_ne ?A. Inf X F \<le> x}" using B1 B2 by auto
  show ?thesis using filter_closure_of_filters8[of X "(f`I)"] B3 A0 A1(2) filters_on_iff by blast
qed

lemma inf_comp:
  "\<lbrakk>is_inf X A1 i1; is_inf X A2 i2; (\<And>a2. a2 \<in> A2 \<longrightarrow> (\<exists>a1 \<in> A1. a1 \<le> a2)) \<rbrakk> \<Longrightarrow> i1 \<le> i2"
  by (metis inf_iff2 is_infD1121 is_infD42 lb_def order_trans)


lemma finite_ind_fil8:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"F \<in> Fpow_ne (\<Union>(f`I))" "Inf X F \<le> y" "y \<in> X"
  shows "\<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y "
proof-
  obtain n J where "I = J ` {i. i < (n::nat)} \<and> inj_on J {i. i < n}" using assms(3) finite_imp_nat_seg_image_inj_on by fastforce
  define G where "G = {(i, z)|z i. z \<in> F \<and> (z \<in> f i)}"
  have B0:"\<And>i. i \<in> I \<longrightarrow>  G``{i} \<noteq> {}  \<longrightarrow> G``{i} \<subseteq> F"
  proof
    fix i assume A3:"i \<in> I"
    show "G``{i}  \<noteq> {} \<longrightarrow> G``{i} \<subseteq> F"
    proof
      assume A4:"G``{i} \<noteq> {}"    
      show "G``{i} \<subseteq> F"
      proof
        fix z assume A5:"z \<in> G``{i}"
        have B1:"(i, z) \<in> G"  using A5 by auto 
        show "z \<in> F" using B1 by(auto simp add:G_def)
      qed
    qed
  qed
  have P:"\<And>i z. i \<in> I \<longrightarrow> G``{i} \<noteq> {} \<longrightarrow> z \<in> G``{i} \<longrightarrow> z \<in> (f i)"
    proof
    fix i z assume A6:"i \<in> I"
    show "G``{i}  \<noteq> {} \<longrightarrow> z \<in> G``{i} \<longrightarrow> z \<in> (f i)"
    proof
      assume A7:"G``{i}  \<noteq> {}" show " z \<in> G``{i} \<longrightarrow> z \<in> (f i)"
      proof
       assume A8:"z \<in> G``{i}" 
       have P0:"(i, z) \<in> G" using A8 by auto
       show "z \<in> f i" using P0 by(auto simp add:G_def)
      qed
    qed
  qed
  define x where "x = (\<lambda>i. if G``{i} \<noteq> {} then Inf X (G``{i}) else SOME z. z \<in> (f i))"
  have B2:"\<And>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)"
  proof
    fix i assume A6:"i \<in> I"
    show "x i \<in> f i"
    proof(cases " G``{i} \<noteq> {}")
      case True
      have B3:"x i =  Inf X (G``{i})"  by (simp add: True x_def)
      have B4:"G``{i} \<subseteq> (f i)"   using A6 P by blast
      have B5:"finite (G``{i})"    by (meson A6 B0 True assms(6) fpow_neD4 infinite_super)
      have B6:" Inf X (G``{i}) \<in> (f i)"    using A6 B4 B5 True assms(1) assms(5) filter_finf_closed3 lattD41 by blast
      then show ?thesis  by (simp add: B3)
    next
      case False
      then show ?thesis  by (metis A6 assms(5) ex_in_conv filterD1 someI2_ex x_def)
    qed
  qed
  have B7:"\<And>z. z \<in> F \<longrightarrow> (\<exists>w \<in> (x` I). w \<le> z)"
  proof
    fix z assume A7:"z \<in> F"
    obtain i where B8:"i \<in> I \<and> z \<in> (f i)"  by (metis A7 UN_E assms(6) fpow_neD1 in_mono)
    have B9:"G``{i} \<noteq> {}" using A7 B8 by(auto simp add:G_def)
    have B10:"x i =  Inf X (G``{i})" by (simp add: B9 x_def)
    have B11:"z \<in> G``{i}" by (simp add: A7 B8 G_def)
    have B12:"finite (G``{i}) \<and> (G``{i}) \<subseteq> X"   by (meson B0 B8 B9 P assms(5) assms(6) filterD21 fpow_neD4 infinite_super subsetI)
    have B13:"Inf X (G``{i}) \<le> z" using B11 B12 assms(1) finf_leI1 latt_iff by blast
    show " (\<exists>w \<in> (x` I). w \<le> z)"
      by (metis B10 B13 B8 imageI)
  qed
  have B14:"finite (x` I) \<and> (x` I) \<subseteq> X"
    using B2 assms(3) assms(5) filterD21 by blast
  have B15:"\<And>i. i \<in> I \<longrightarrow> (f i) \<subseteq> X"  by (simp add: assms(5) filterD2)
  have B16:"\<Union>(f`I) \<subseteq> X"   by (simp add: B15 UN_least)
  have B17:"finite F \<and> F \<subseteq> X" by (metis B16 assms(6) fpow_neD4 subset_trans)
  have B18:"Inf X (x` I) \<le> Inf X F "
    apply(rule_tac ?X="X" and ?A1.0="x` I" and ?A2.0="F" in inf_comp)
    apply (simp add: B14 assms fpow_neI3 inf_semilattice_finf lattD41)
    apply (metis B17 assms(1) assms(6) binf_finite2 fpow_ne_iff2 lattD41)
    using B7 by blast
  show ?thesis
    using B18 B2 assms(7) dual_order.trans by blast
qed



lemma finite_ind_fil9:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I)  \<subseteq> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y}" (is "?L \<subseteq> ?R")
proof
  fix z assume A2:"z \<in> ?L"
  obtain F where B0:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> Inf X F \<le> z" using A0 A1 A2 finite_ind_fil7[of X top I] by auto
  have B1:"(f`I) \<noteq> {}" using A0 A1 by simp
  have B2:"z \<in> X" using A0 A1 B1 by (metis (no_types, lifting) A2 CollectD finite_ind_fil7)
  have B3:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> Inf X F \<le> z  \<and> z \<in> X"   by (simp add: B0 B2)
  obtain x where B4:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> z" using A0 A1 A2 B0 B3 finite_ind_fil8[of X top I f F z] by(auto)
  show "z \<in> ?R" using B3 B4 by(auto)
qed



lemma finite_ind_fil10:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y} \<subseteq> Sup (filters_on X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix z assume A2:"z \<in> ?L"
  obtain x where B0:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> z" using A2 by auto
  have B1:"(x` I) \<in> Fpow_ne (\<Union>(f`I))"  by(auto simp add:Fpow_ne_def Fpow_def B0 assms)
  show "z \<in> ?R" using assms B0 B1 A2 finite_ind_fil7[of X top I] by auto
qed


lemma finite_ind_fil11:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y}  "
  apply(rule order.antisym) 
  using A0 A1 apply(rule finite_ind_fil9, simp)
  using A0 A1 by(rule finite_ind_fil10, simp)

lemma finite_ind_fil11b:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"y \<in> Sup (filters_on X) (f`I)"
  shows "\<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y"
  using finite_ind_fil11[of X top I f] assms by(auto)

lemma finite_ind_fil12:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"y \<in> X" "(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"  "Inf X (x` I) \<le> y"
  shows " \<exists>(x1::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) =y "
proof-
  define x1 where "x1 = (\<lambda>i. Sup X {y, x i})"
  have B00:"finite (x` I)" by (simp add: assms(4))
  have B01:"x` I \<subseteq> X" using assms(5) assms(7) filterD21 by blast
  have B02:"x` I \<noteq> {}"  by (simp add: assms(3))
  have B03:"finite (x1 ` I)"  by (simp add: assms(4))
  have B04:"(x1 ` I) \<subseteq> X"  by (metis B01 assms(1) assms(6) distr_latticeD5 image_subset_iff l_sup_closed x1_def)
  have B05:"(x1 ` I) \<noteq> {}"  using assms(3) by force
  have B0:"y = Sup X {y, Inf X (x` I)}" by (metis assms(6,8)  greatest_insert3 greatest_singleton sup_equality sup_maxE1) 
  have B1:"... = Inf X {Sup X {y,a}|a.  a \<in> (x` I)}" using B00 B01 B02 assms(1,6) fin_distr1 by blast
  have B2:"... = Inf X {Sup X {y, x i}|i. i \<in> I}" by (metis (no_types, opaque_lifting) image_iff)
  have B3:"... = Inf X {x1 i|i. i \<in> I}"  using x1_def by auto
  have B4:"... = Inf X (x1 ` I)"  by (simp add: Setcompr_eq_image)
  have B5:"Inf X (x1 ` I) = y"  using B0 B1 B2 B3 B4 by presburger
  have B6:"\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)"  by (simp add: assms(1) assms(5) assms(6) assms(7) distr_latticeD5 filter_on_lattice_sup01 x1_def)
  show ?thesis
    using B5 B6 by blast
qed


lemma finite_ind_fil13:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) \<subseteq> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) = y}" (is "?L \<subseteq> ?R")
proof
  fix y assume A2:"y \<in> ?L"
  have B0:"is_lattice X" by (simp add: assms(1) distr_latticeD5)
  have B1:"y \<in> X" by (metis (no_types, lifting) A2 B0 CollectD assms(2) assms(3) assms(4) assms(5) finite_ind_fil11)
  obtain x where B2:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y"  by (metis A2 B0 assms(2) assms(3) assms(4) assms(5) finite_ind_fil11b) 
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) =y" using finite_ind_fil12[of X top I f y x] A0 A1 A2  B1 B2 by presburger
  show "y \<in> ?R"
    using B1 B3 by blast
qed


lemma finite_ind_fil14:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) = y} \<subseteq> Sup (filters_on X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix y assume A2:"y \<in> ?L"
  have B0:"is_lattice X" by (simp add: assms(1) distr_latticeD5)
  have B1:"y \<in> X"  using A2 by blast
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) =y" using A2 by blast
  have B2:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) \<le> y"  by (simp add: B3)
  have B3:"y \<in> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y}"  using B1 B2 by blast
  show "y \<in> ?R"   by (meson B0 B3 assms(2) assms(3) assms(4) assms(5) finite_ind_fil10 subset_iff)
qed


lemma finite_ind_fil15:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) = y}  "
  using assms finite_ind_fil13[of X top I f] finite_ind_fil14[of X top I f] by fastforce



(*
lemma fin_distr2:"\<lbrakk>distributive_lattice X ;finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Inf X {b, (Sup X  A)} = Sup X {Inf X {b, a}|a. a \<in> A}" using distr_finite2[of b X A]  by (simp add: distr_eq_tmp1)

lemma fin_distr1:"\<lbrakk>distributive_lattice X; finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Sup X{ b, (Inf X  A)} = Inf X {Sup X {b, a}|a. a \<in> A}"  using distr_finite1[of b X A]  by (simp add: distr_eq_tmp3)
*)

definition subsemilattice_inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "subsemilattice_inf X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))"

definition subsemilattice_sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "subsemilattice_sup X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup R X {a, b} i))"


definition sublattice::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "sublattice X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>s \<in> A. is_sup R X {a, b} s) \<and> (\<exists>i \<in> A. is_inf X {a, b} i))"


lemma subsemilattice_infD:"subsemilattice_inf X A \<Longrightarrow>  (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))" by (simp add:subsemilattice_inf_def)
lemma subsemilattice_infD1:"subsemilattice_inf X A \<Longrightarrow>  (A \<subseteq> X)" by (simp add:subsemilattice_inf_def)
lemma subsemilattice_infD2:"subsemilattice_inf X A \<Longrightarrow>  (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))" by (simp add:subsemilattice_inf_def)
lemma subsemilattice_infI1:"\<lbrakk>(A \<subseteq> X); (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i)) \<rbrakk> \<Longrightarrow> subsemilattice_inf X A " by (simp add:subsemilattice_inf_def)

lemma subsemilattice_supD:"subsemilattice_sup X A \<Longrightarrow> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup R X {a, b} i))" by (simp add:subsemilattice_sup_def)
lemma subsemilattice_supD1:"subsemilattice_sup X A \<Longrightarrow> (A \<subseteq> X)" by (simp add:subsemilattice_sup_def)
lemma subsemilattice_supD2:"subsemilattice_sup X A \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>i \<in> A. is_sup R X {a, b} i))" by (simp add:subsemilattice_sup_def)
lemma subsemilattice_supI1:"\<lbrakk>(A \<subseteq> X); (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup R X {a, b} i)) \<rbrakk> \<Longrightarrow> subsemilattice_sup X A " by (simp add:subsemilattice_sup_def)


lemma sublatticeD:"sublattice X A \<Longrightarrow> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>s \<in> A. is_sup R X {a, b} s) \<and> (\<exists>i \<in> A. is_inf X {a, b} i))" by (simp add:sublattice_def)
lemma sublatticeD1:"sublattice X A \<Longrightarrow> (A \<subseteq> X)" by (simp add:sublattice_def)
lemma sublatticeD2:"sublattice X A \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>s \<in> A. is_sup R X {a, b} s))" by (simp add:sublattice_def)
lemma sublatticeD3:"sublattice X A \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))" by (simp add:sublattice_def)

lemma sublatticeI1:"\<lbrakk>(A \<subseteq> X); (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>s \<in> A. is_sup R X {a, b} s)\<and> (\<exists>i \<in> A. is_inf X {a, b} i)) \<rbrakk> \<Longrightarrow> sublattice X A " by (simp add:sublattice_def)

lemma sublatticeD4:"sublattice X A \<Longrightarrow> subsemilattice_sup X A"  by (simp add: sublattice_def subsemilattice_supI1)
lemma sublatticeD5:"sublattice X A \<Longrightarrow> subsemilattice_inf X A"  by (simp add: sublattice_def subsemilattice_infI1)

lemma sublatticeI2:"\<lbrakk> subsemilattice_sup X A; subsemilattice_inf X A  \<rbrakk> \<Longrightarrow> sublattice X A "   by (simp add: sublattice_def subsemilattice_infD1 subsemilattice_infD2 subsemilattice_supD2) 


definition homoinf::"'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
 "homoinf X Y f \<equiv> (\<forall>x y i. is_inf X {x, y} i \<longrightarrow>  is_inf Y {f x , f y} (f i))"


lemma homoinfsD1:"\<lbrakk>is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (Inf X {x, y}) = Inf Y {f x, f y}" by(simp add:homoinf_def) (metis inf_equality sinfD3)

lemma homoinfsD2:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow>  f (Inf X {a1, a2}) = Inf Y {f a1, f a2}" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"is_inf_semilattice X" and 
          A5:"is_inf_semilattice Y" and 
          A6:"f`X \<subseteq> Y"
  shows "f (Inf X A) = Inf Y (f`A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 singleton by fastforce
next
  case (insert x F)
  have B0:"f`(insert x F) = (insert (f x) (f`F))" by auto
  obtain B1:"f x \<in> Y" and B2:"f`F \<subseteq> Y"    by (meson A6 dual_order.trans image_eqI image_mono insert.prems insert_subset)
  obtain B3:"finite F" and B4:"F \<noteq> {}"    using insert.hyps(1) insert.hyps(2) by blast
  have B7:"Inf X (insert x F) = Inf X {x, Inf X F}"   using A4 B3 B4 insert.prems sfinf_insert by fastforce
  let ?a1="x"  let ?a2="Inf X F" let  ?i="Inf X {?a1, ?a2}"
  have B6:"?a1 \<in> X \<and> ?a2 \<in> X"  by (meson A4 B3 B4 binf_finite2 insert.prems insert_subset is_infE1)
  have B7:"is_inf X {?a1, ?a2} ?i" by (simp add: A4 B6 sinfD3)
  have B8:"is_inf Y {f ?a1, f ?a2} (f?i)"  by (metis A0 A5 A6 B6 image_subset_iff sinfD3)
  then show ?case
    by (metis A0 A4 A5 B0 B1 B2 B3 B4 B6 empty_is_image finite_imageI insert.hyps(4) insert.prems insert_subset sfinf_insert)
qed

lemma homoinfsD3:"\<lbrakk>f`X \<subseteq> Y;is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f; F \<subseteq> X; finite F; F \<noteq> {}\<rbrakk> \<Longrightarrow> f (Inf X F) = Inf Y (f`F)"by (meson homoinfsD1 homoinfsD2)


definition homosup::"'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where 
   "homosup X Y f \<equiv> (\<forall>x y s. is_sup R X {x, y} s \<longrightarrow> is_sup Y {f x, f y} (f s))"

lemma homosupD1:"\<lbrakk>is_sup_semilattice R X; is_sup_semilattice Y; homosup X Y f; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (Sup R X {x, y}) = Sup Y {f x, f y}" by (simp add:homosup_def) (metis sup_equality ssupD3)

lemma homosupD2:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> f (Sup X {a1, a2}) = Sup Y {f a1, f a2}" and
  A1: "finite A" and  A2: "A \<noteq> {}" and  A3: "A \<subseteq> X" and
  A4: "is_sup_semilattice R X" and    A5: "is_sup_semilattice Y" and  A6: "f`X \<subseteq> Y" shows "f (Sup X A) = Sup Y (f`A)"
  using A1 A2 A3
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 singleton by fastforce
next
  case (insert x F)
  have B0:"f`(insert x F) = (insert (f x) (f`F))" by auto
  obtain B1: "f x \<in> Y" and B2: "f`F \<subseteq> Y" by (meson A6 dual_order.trans image_eqI image_mono insert.prems insert_subset)
  obtain B3: "finite F" and B4: "F \<noteq> {}" using insert.hyps(1) insert.hyps(2) by blast
  have B7: "Sup X (insert x F) = Sup X {x, Sup X F}"  by (metis A4 B3 B4 insert.prems insert_subset sfsup_insert)
  let ?a1 = "x" let ?a2 = "Sup X F" let ?s = "Sup X {?a1, ?a2}"
  have B6: "?a1 \<in> X \<and> ?a2 \<in> X" by (meson A4 B3 B4 bsup_finite2 insert.prems insert_subset is_supE1)
  have B7: "is_sup R X {?a1, ?a2} ?s" by (simp add: A4 B6 ssupD3)
  have B8: "is_sup Y {f ?a1, f ?a2} (f ?s)" by (metis A0 A5 A6 B6 image_subset_iff ssupD3)
  then show ?case
    by (metis A4 A5 B0 B1 B2 B3 B4 finite_imageI image_is_empty insert.hyps(4) insert.prems insert_subset sfsup_insert sup_equality)
qed

lemma homosupD3:"\<lbrakk>f`X \<subseteq> Y; is_sup_semilattice R X; is_sup_semilattice Y; homosup X Y f; F \<subseteq> X; finite F; F \<noteq> {}\<rbrakk> \<Longrightarrow> f (Sup X F) = Sup Y (f`F)"  by (meson homosupD1 homosupD2)


lemma homosupD4:"\<lbrakk>f`X \<subseteq> Y; is_sup_semilattice R X; is_sup_semilattice Y; homosup X Y f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by(rule_tac ?X="Y" in ge_bsup1; auto; frule_tac ?a="x" and ?b="y" in bsup_ge1, simp_all)
    (frule_tac ?Y="Y" and ?f="f" and ?x="x" and ?y="y" in homosupD1, simp_all)

lemma homoinfD4:"\<lbrakk>f`X \<subseteq> Y; is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by(rule_tac ?X="Y" in le_binf1; auto; frule_tac ?a="x" and ?b="y" in binf_le1, simp_all)
    (frule_tac ?Y="Y" and ?f="f" and ?x="x" and ?y="y" in homoinfsD1, simp_all)

lemma subsemilattice_homomorphism1:"\<lbrakk>f`X \<subseteq> Y; is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f\<rbrakk> \<Longrightarrow> subsemilattice_inf Y (f`X)"
   by(rule subsemilattice_infI1;auto) (metis homoinf_def is_infE1 sinfD2)

lemma subsemilattice_homomorphism2:"\<lbrakk>f`X \<subseteq> Y; is_sup_semilattice R X; is_sup_semilattice Y; homosup X Y f\<rbrakk> \<Longrightarrow> subsemilattice_sup Y (f`X)"
   by(rule subsemilattice_supI1;auto) (metis homosup_def is_supE1 ssupD2)


definition homolatt::"'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where 
   "homolatt X Y f \<equiv> (\<forall>x y s. is_sup R X {x, y} s \<longrightarrow> is_sup Y {f x, f y} (f s)) \<and> (\<forall>x y i. is_inf X {x, y} i \<longrightarrow>  is_inf Y {f x , f y} (f i))"


lemma homolattD0:"homolatt X Y f \<Longrightarrow> homosup X Y f" by (simp add: homolatt_def homosup_def)
lemma homolattD1:"homolatt X Y f \<Longrightarrow> homoinf X Y f" by (simp add: homolatt_def homoinf_def)
lemma homolattD2:"\<lbrakk>is_lattice X; is_lattice Y; homolatt X Y f; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (Sup R X {x, y}) = Sup Y {f x, f y}" by (simp add:homolatt_def; metis lattD32 sup_equality)


lemma homolattD3:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> f (Sup X {a1, a2}) = Sup Y {f a1, f a2}" and
  A1: "finite A" and  A2: "A \<noteq> {}" and  A3: "A \<subseteq> X" and
  A4: "is_lattice X" and    A5: "is_lattice Y" and  A6: "f`X \<subseteq> Y" shows "f (Sup X A) = Sup Y (f`A)"
  using A1 A2 A3
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 singleton by fastforce
next
  case (insert x F)
  have P0:"is_sup_semilattice R X"  by (simp add: A4 lattD42)
  have B0:"f`(insert x F) = (insert (f x) (f`F))" by auto
  obtain B1: "f x \<in> Y" and B2: "f`F \<subseteq> Y" by (meson A6 dual_order.trans image_eqI image_mono insert.prems insert_subset)
  obtain B3: "finite F" and B4: "F \<noteq> {}" using insert.hyps(1) insert.hyps(2) by blast
  have B7: "Sup X (insert x F) = Sup X {x, Sup X F}"   using B3 B4 P0 insert.prems sfsup_insert by fastforce 
  let ?a1 = "x" let ?a2 = "Sup X F" let ?s = "Sup X {?a1, ?a2}"
  have B6: "?a1 \<in> X \<and> ?a2 \<in> X" by (meson B3 B4 P0 bsup_finite2 insert.prems insert_subset is_supE1) 
  have B7: "is_sup R X {?a1, ?a2} ?s" by (simp add: A4 B6 lattD32)
  have B8: "is_sup Y {f ?a1, f ?a2} (f ?s)" by (metis A0 A5 A6 B6 image_subset_iff lattD32) 
  then show ?case
    by (metis A0 A4 A5 B0 B1 B2 B3 B4 B6 empty_is_image finite_imageI fsup_insert insert.hyps(4) insert.prems insert_subset)
qed

lemma homolattD4:"\<lbrakk>f`X \<subseteq> Y; is_lattice X; is_lattice Y; homolatt X Y f; F \<subseteq> X; finite F; F \<noteq> {}\<rbrakk> \<Longrightarrow>f (Sup X F) = Sup Y (f`F)"   by (meson homolattD2 homolattD3)

lemma homolattD5:"\<lbrakk>f`X \<subseteq> Y; is_lattice X; is_lattice Y; homolatt X Y f; F \<subseteq> X; finite F; F \<noteq> {}\<rbrakk> \<Longrightarrow> f (Inf X F) = Inf Y (f`F)"by (simp add: homoinfsD3 homolattD1 lattD41)


lemma homolattD6:"\<lbrakk>f`X \<subseteq> Y; is_lattice X; is_lattice Y; homolatt X Y f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> f x \<le> f y" by (simp add: homoinfD4 homolattD1 latt_iff)

definition sup_distributive where
  "sup_distributive X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X. x \<le> Sup R X {a, b} \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup X {a1, b1}))"

definition inf_distributive where
  "inf_distributive X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X.  Inf X {a, b} \<le> x \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf X {a1, b1}))"

lemma sup_distributiveI1:
  "(\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X; x \<le> Sup  X {a, b}\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup X {a1, b1})) \<Longrightarrow> sup_distributive X"
  by(simp add:sup_distributive_def)

lemma sup_distributiveD1:
  "sup_distributive X \<Longrightarrow> (\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X; x \<le> Sup  X {a, b}\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup X {a1, b1}))"
  by(simp add:sup_distributive_def)

lemma inf_distributiveI1:
  "(\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X;  Inf X {a, b} \<le> x\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf X {a1, b1})) \<Longrightarrow> inf_distributive X"
  by(simp add:inf_distributive_def)

lemma inf_distributiveD1:
  "inf_distributive X \<Longrightarrow> (\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X; Inf  X {a, b} \<le> x\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf X {a1, b1}))"
  by(simp add:inf_distributive_def)

lemma lat_binf_leI1: "\<lbrakk>is_lattice X;x \<in> X; y \<in> X; z \<in> X; Inf X {x, y} = z \<rbrakk> \<Longrightarrow>z \<le> x" using binf_leI1 lattD41 by blast
lemma lat_binf_leI2: "\<lbrakk>is_lattice X;x \<in> X; y \<in> X; z \<in> X; Inf X {x, y} = z \<rbrakk> \<Longrightarrow>z \<le> y" using binf_leI2 lattD41 by blast
lemma lat_bsup_geI1: "\<lbrakk>is_lattice X;x \<in> X; y \<in> X; z \<in> X; Sup R X {x, y} = z\<rbrakk>  \<Longrightarrow> x \<le> z" using bsup_geI1 lattD42 by blast
lemma lat_bsup_geI2: "\<lbrakk>is_lattice X;x \<in> X; y \<in> X; z \<in> X; Sup R X {x, y} = z\<rbrakk>  \<Longrightarrow> y \<le> z" using bsup_geI2 lattD42 by blast

lemma sup_distributiveD2:
  "\<lbrakk>sup_distributive X; is_lattice X\<rbrakk> \<Longrightarrow> distributive_lattice X"
  apply(rule distr_latticeI2)
proof-
  fix x y z assume P:"sup_distributive X" "is_lattice X" "x \<in> X" "y \<in> X" "z \<in> X"
  have B1:"Inf X {x, Sup X {y, z}} \<le> Sup X {y, z}"  by (simp add: P(2-5) binf_leI2 l_sup_closed lattD41)
  obtain y1 z1 where dist:"y1 \<in> X \<and> z1 \<in> X \<and> y1 \<le> y \<and> z1 \<le> z \<and> (Inf X {x, Sup X {y, z}}) = Sup X {y1, z1}"  by (metis B1 P(1) P(2) P(3) P(4) P(5) l_inf_closed l_sup_closed sup_distributiveD1)
  have B2:"Sup X {y1, z1} \<le> x"by (metis P(2-5) dist l_sup_closed lat_binf_leI1) 
  have B3:"y1 \<le> x \<and> z1 \<le> x"  using B2 P(2) P(3) bsup_iff dist lattD42 by blast
  have B4:"y1 = Inf X {x, y1} \<and> z1 = Inf X {x, z1}" by (simp add: B3 P(3) dist le_inf2)
  have B40:"Inf X {x, y1} \<le> Inf X {x, y}" using lattD41[of X] binf_leI4[of X y1 y x] by (simp add: P(2-4) dist insert_commute)
  have B41:"Inf X {x, z1} \<le> Inf X {x, z}" using lattD41[of X] binf_leI4[of X z1 z x] by (simp add: P(1-5) dist insert_commute)
  have B5:"Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y1}, Inf X {x, z1}}"  using B4 dist by presburger
  have B6:"... \<le> Sup X {Inf X {x, y}, Inf X {x, z}}" by (simp add: B40 B41 P(2) P(3) P(4) P(5) bsup_geI5 dist l_inf_closed lattD42)  
  show "Inf X {x, Sup X {y, z}} \<le> Sup X {Inf X {x, y}, Inf X {x, z}}"  by (simp add: B5 B6)
qed

lemma inf_distributiveD2:
  "\<lbrakk>inf_distributive X; is_lattice X\<rbrakk> \<Longrightarrow> distributive_lattice X"
apply(rule distr_latticeI1)
proof-
  fix x y z assume P:"inf_distributive X" "is_lattice X" "x \<in> X" "y \<in> X" "z \<in> X"
  have B0:" Sup X {Inf X {x, y}, Inf X {x, z}} \<le> Inf X {x, Sup X {y, z}}"  by (simp add: P(2-5) distrib_inf_le) 
  have B1:" Inf X {y, z} \<le> Sup X {x, Inf X {y, z}}" by (simp add: P(2-5) bsup_geI2 l_inf_closed lattD42)
  obtain y1 z1 where dist:"y1 \<in> X \<and> z1 \<in> X \<and> y \<le> y1 \<and> z \<le> z1 \<and>  (Sup X {x, Inf X {y, z}}) = Inf X {y1, z1}" by (metis B1 P(1,2-5) inf_distributiveD1 l_inf_closed l_sup_closed) 
  have B2:"x \<le> Inf X {y1, z1}" by (metis P(2-5)  dist l_inf_closed lat_bsup_geI1)
  have B3:"(x, y)\<in>R1 \<and> x \<le> z1"  using B2 P(2-3) binf_iff dist lattD41 by blast 
  have B4:"y1 = Sup X {x, y1} \<and> z1 = Sup X {x, z1}" by (simp add: B3 P(3) dist ge_sup1)
  have B5:"Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y1}, Sup X {x, z1}}"  using B4 dist by presburger
  have B6:"... \<ge> Inf X {Sup R X {x, y}, Sup X {x, z}}" by (metis B3 B4 P(2-5) binf_leI5 bsup_geI3 dist lattD41 lattD42 ssupD4) 
  show "Inf X {Sup R X {x, y}, Sup X {x, z}} \<le> Sup X {x, Inf X {y, z}}" by (simp add: B5 B6) 
qed

lemma filter_compl1: "\<lbrakk>is_lattice X; is_pfilter X F\<rbrakk> \<Longrightarrow> (X -  F) \<noteq> {}" using is_pfilterD2 is_pfilterD3 by(blast)
lemma ideal_compl1: "\<lbrakk>is_lattice X; F \<subseteq> X;is_pideal X (X-F)\<rbrakk> \<Longrightarrow> (F \<noteq> X)" by (metis Diff_eq_empty_iff is_ideal_def is_pideal_def)

lemma filter_compl2: "\<lbrakk>is_lattice X; is_pfilter X F\<rbrakk> \<Longrightarrow> (X - F \<noteq> X)" using is_pfilterD3 pfilter_on_lattice_inf4b by fastforce
lemma ideal_compl2: "\<lbrakk>is_lattice X; F \<subseteq> X;is_pideal X (X-F)\<rbrakk> \<Longrightarrow>F \<noteq> {}"using is_pideal_def by fastforce

lemma pfilter_compl3: "\<lbrakk>is_lattice X; is_pfilter X F; x \<in> (X-F); y \<in> X; (y, x)\<in>R\<rbrakk> \<Longrightarrow>y \<in> (X-F)" by (metis DiffD1 DiffD2 DiffI lattice_absorb1 le_inf2 pfilter_on_lattice_sup01)
lemma pideal_compl3: "\<lbrakk>is_lattice X; F \<subseteq> X;is_pideal X (X-F); x \<in> F; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow>y \<in> F"  by (smt (verit) Diff_iff binf_commute2 in_mono le_inf2 pideal_on_lattice_inf01)

lemma pfilter_compl4: "\<lbrakk>is_lattice X; is_pfilter X F\<rbrakk> \<Longrightarrow> is_ord_cl X (X-F) (\<ge>)" using is_ord_cl_comp1 pfilters_upcl by fastforce 
lemma pideal_compl4: "\<lbrakk>is_lattice X;  F \<subseteq> X;is_pideal X (X-F)\<rbrakk> \<Longrightarrow> is_ord_cl X F (\<le>)"  by (metis is_ord_clI1 pideal_compl3)

lemma prime_filter_compl5: "\<lbrakk>is_lattice X; is_pfilter X F; sup_prime X F; x \<in> (X-F); y \<in> (X-F)\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> (X-F)" by (metis Diff_iff is_pfilterD1 l_sup_closed primefilterD1)
lemma prime_ideal_compl5:  "\<lbrakk>is_lattice X; F \<subseteq> X; is_pideal X (X-F) ; inf_prime X (X-F); x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> F" by (smt (verit, ccfv_threshold) DiffD2 DiffI inf_prime_def l_inf_closed subset_eq)

lemma prime_filter_compl6: "\<lbrakk>is_lattice X; is_pfilter X F; sup_prime X F\<rbrakk> \<Longrightarrow> is_dir (X-F) (\<le>)" by (meson Diff_subset is_updirI4 lattD42 prime_filter_compl5)
lemma prime_ideal_compl6: "\<lbrakk>is_lattice X; F \<subseteq> X; is_pideal X (X-F) ; inf_prime X (X-F)\<rbrakk> \<Longrightarrow> is_dir F (\<ge>)"  by (metis is_dwdirI4 lattD41 prime_ideal_compl5)

lemma prime_filter_compl7: "\<lbrakk>is_lattice X; is_pfilter X F; sup_prime X F; x \<in> X; y \<in> X; Inf X {x, y} \<in> (X-F)\<rbrakk> \<Longrightarrow> (x \<in> (X-F)) \<or> (y \<in> (X-F))"  by (metis Diff_iff filter_finf_closed1 is_pfilterD1 lattD41) 
lemma prime_ideal_compl7: "\<lbrakk>is_lattice X;  F \<subseteq> X; is_pideal X (X-F) ; inf_prime X (X-F); x \<in> X; y \<in> X; Sup R X {x, y} \<in> F\<rbrakk> \<Longrightarrow> (x \<in> F) \<or> (y \<in> F)" by (smt (verit) DiffE DiffI ideal_fsup_closed is_pidealD1 lattD32) 

lemma prime_filter_compl8: "\<lbrakk>is_lattice X; is_pfilter X F;  sup_prime X F\<rbrakk> \<Longrightarrow> is_ideal X (X-F)"  by (meson Diff_subset Posets16.is_filter_def filter_compl1 idealI1 is_ord_cl_comp1 is_pfilterD1 prime_filter_compl6)
lemma prime_ideal_compl8: "\<lbrakk>is_lattice X;  F \<subseteq> X; is_pideal X (X-F);inf_prime X (X-F)\<rbrakk> \<Longrightarrow> is_filter X F" by (metis Diff_empty filterI1 is_pideal_def pideal_compl4 prime_ideal_compl6) 

lemma prime_filter_compl9: "\<lbrakk>is_lattice X; is_pfilter X F;  sup_prime X F\<rbrakk> \<Longrightarrow> inf_prime X (X-F)" by (meson inf_primeI1 prime_filter_compl7)
lemma prime_ideal_compl9: "\<lbrakk>is_lattice X; F \<subseteq> X; is_pideal X (X-F);inf_prime X (X-F)\<rbrakk> \<Longrightarrow> sup_prime X F" by (meson sup_primeI1 prime_ideal_compl7)

lemma prime_ideal_compl10: "\<lbrakk>is_lattice X; F \<subseteq> X;is_pideal X (X-F); inf_prime X (X-F)\<rbrakk> \<Longrightarrow> is_pfilter X F"by (simp add: is_ideal_def is_pfilterI1 is_pideal_def prime_ideal_compl8) 
lemma prime_filter_compl10: "\<lbrakk>is_lattice X; is_pfilter X F;  sup_prime X F\<rbrakk> \<Longrightarrow> is_pideal X (X-F)" by (metis filter_compl2 is_pideal_def prime_filter_compl8)

lemma prime_ideal_compl: "\<lbrakk>is_lattice X; F \<subseteq> X;is_pideal X (X-F); inf_prime X (X-F)\<rbrakk> \<Longrightarrow> is_pfilter X F \<and>sup_prime X F" by (simp add: prime_ideal_compl10 prime_ideal_compl9)
lemma prime_filter_compl: "\<lbrakk>is_lattice X; is_pfilter X F;  sup_prime X F\<rbrakk> \<Longrightarrow> is_pideal X (X-F) \<and> inf_prime X (X-F)" by (simp add: prime_filter_compl10 prime_filter_compl9)



lemma prime_filter_on_lattice:
  assumes A0:"is_lattice X" and A1:"is_pfilter X F" and A2:"sup_prime X F" and
          A3:"a \<in> filters_on X" and
          A4:"b \<in> filters_on X" and
          A5:"F=Inf (filters_on X) {a, b}"
  shows "F = a \<or> F =b"
proof-
  have B0:"F=a \<inter> b" by (simp add: A0 assms(4) assms(5) assms(6) filters_lattice_inf_op)
  have B1:"a \<subseteq> F \<or> b \<subseteq> F" using B0 A0 A1 A2 A3 A4 B0 sup_prime_pfilterD4[of X F a b]  by (simp add:filters_on_iff)
  have B2:"\<not>(a \<subseteq> F) \<longrightarrow> b = F" using B0 B1 by blast
  show ?thesis
    using B0 B2 by blast
qed

(*
  using 
    sup_prime_pfilterD4 sup_prime_pfilterI2 
    prime_filter_compl prime_ideal_compl 
  we have the characterization of sup prime proper filters on a lattice in terms of
    \<forall>F1 F2 \<in> filters_on X. F1 \<inter> F2 \<subseteq> F \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F
  and in terms of 
    is_pideal (X-F)  \<and> inf_prime (X-F)
*)


lemma top_lattice_inf:"\<lbrakk> x \<in> X; y \<in> X; is_greatest X top; is_inf X {x, y} top\<rbrakk> \<Longrightarrow> x =top \<and> y=top"by (simp add: binary_infD31 binary_infD32 greatestD2 is_infE1 order_class.order_eq_iff)
lemma bot_lattice_sup:"\<lbrakk> x \<in> X; y \<in> X; is_least X bot; is_sup R X {x, y} bot\<rbrakk> \<Longrightarrow> x =bot \<and> y=bot" by (simp add: binary_supD31 binary_supD32 is_supE1 leastD2 order_antisym) 


locale bounded_poset=
  fixes X::"'a::order set" and
        top bot::"'a::order"
  assumes bot:"is_least X bot" and
          top:"is_greatest X top"
begin

definition complements::"'a::order \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "complements a a' \<equiv> is_inf X {a, a'} bot \<and> is_sup R X {a, a'} top"

lemma complements_idemp: "complements a a' \<Longrightarrow> complements a' a" by (simp add: complements_def insert_commute)
lemma complements_top_bot: "complements top bot" by (meson binary_infI1 binary_supI2 bot complements_def greatestD11 leastD11 leastD2 top)
lemma complements_bot_top: "complements bot top" by (simp add: complements_idemp complements_top_bot) 

end

locale blattice=bounded_poset+
  assumes dist:"distributive_lattice X"
begin
lemma complements_unique1:
  "\<lbrakk>a \<in> X; a' \<in> X;a'' \<in> X; complements a a'; complements a a''\<rbrakk> \<Longrightarrow> a'=a''"
proof-
  assume A0:"a \<in> X""a' \<in> X""a'' \<in> X"" complements a a'" " complements a a''"
  have B0:"a'' = Inf X {a'', top}"  by (simp add: A0(3) greatest_inf top) 
  also have B1:"... = Inf X {a'', Sup X {a, a'}}" using A0(4) complements_def sup_equality by blast
  also have B2:"... = Sup X {Inf X {a'', a}, Inf X {a'', a'}}" by (simp add: A0(1) A0(2) A0(3) dist distr_latticeD3)
  also have B3:"... = Sup X {bot, Inf X {a'', a'}}"  by (metis A0(1,3,5) binf_commute2 complements_def inf_equality)
  also have B4:"... = Sup X {Inf X {a, a'}, Inf X {a'', a'}}" using A0(4) complements_def inf_equality by blast
  also have B5:"... = Inf X {Sup X {a, a''}, a'}"  by (metis A0(1) A0(2) A0(3) blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD4)
  also have B6:"... = Inf X {top, a'}"  using A0(5) complements_def sup_equality by blast
  also have B7:"... = a'" by (simp add: A0(2) binf_commute2 greatestD11 greatest_inf top) 
  then show ?thesis
    by (simp add: calculation)
qed

lemma comp_eq1:"\<lbrakk>a \<in> X; a' \<in> X; complements a a'\<rbrakk> \<Longrightarrow> Sup X {a, a'} = top"  using complements_def sup_equality by blast
lemma comp_eq2:"\<lbrakk>a \<in> X; a' \<in> X; complements a a'\<rbrakk> \<Longrightarrow> Inf X {a, a'} = bot"  using complements_def inf_equality by blast

lemma complI1:"\<lbrakk>a \<in> X; x \<in> X; Inf X {a, x} = bot; Sup X {a, x} = top\<rbrakk> \<Longrightarrow> complements a x" using complements_def dist distr_latticeD5 inf_ex sup_ex by blast



lemma demorgs1:"\<lbrakk>x \<in> X; y \<in> X; x' \<in> X; y' \<in> X; complements x x'; complements y y'\<rbrakk> \<Longrightarrow> Inf X {Inf X {x, y}, Sup X {x', y'}} = bot "
proof-
  fix x y x' y' assume A0:"x \<in> X" "y \<in> X" "x' \<in> X" "y' \<in> X" "complements x x'" "complements y y'"
  have B0:"Inf X {Inf X {x, y}, Sup X {x', y'}} = Sup X {Inf X {Inf X {x, y}, x'}, Inf X {Inf X {x, y}, y'}}"  by (meson A0(1-4) blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD3 distributive_lattice_def l_inf_closed)
  also have "... = Sup X {Inf X {y, Inf X {x, x'}}, Inf X {x, Inf X {y, y'}}}"  by (metis A0(1-4) binf_assoc1 binf_commute2 blattice.axioms(2) blattice_axioms blattice_axioms_def distributive_lattice_def lattD41)
  also have "... =  Sup X {Inf X {y,bot}, Inf X {x,bot}}" by (metis A0(5) A0(6) complements_def inf_equality)
  also have "... = Sup X {bot, bot}" by (simp add: A0(1) A0(2) bot least_inf)
  also have "... = bot" using bot leastD11 sup_singleton2 by auto
  finally show "Inf X {Inf X {x, y}, Sup X {x', y'}} = bot" by simp
qed


lemma demorgs2:"\<lbrakk>x \<in> X; y \<in> X; x' \<in> X; y' \<in> X; complements x x'; complements y y'\<rbrakk> \<Longrightarrow> Sup X {Inf X {x, y}, Sup X {x', y'}} = top"
proof-
  fix x y x' y' assume A0:"x \<in> X" "y \<in> X" "x' \<in> X" "y' \<in> X" "complements x x'" "complements y y'"
  have B1:"Sup X {x, Sup X {x', y'}}=Sup X {Sup X {x, x'}, y'}" by (metis A0(1,3,4)  blattice.axioms(2) blattice_axioms blattice_axioms_def bsup_assoc1 distr_latticeD5 lattD42)
  have B2:"Sup X {y, Sup X {x', y'}} = Sup X {x', Sup X {y, y'}}"   by (metis A0(2-4) blattice.axioms(2) blattice_axioms blattice_axioms_def bsup_assoc2 distributive_lattice_def lattD42)
  have B0:"Sup X {Inf X {x, y}, Sup X {x', y'}} = Inf X {Sup X {x, Sup X {x', y'}}, Sup X {y, Sup X {x', y'}}}" by (meson A0(1-4) blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD2 distributive_lattice_def l_sup_closed)
  also have "...                                = Inf X {Sup X {Sup X {x, x'}, y'}, Sup X {x', Sup X {y, y'}}}"  by (simp add: B1 B2) 
  also have "... = Inf X {Sup X {x, top}, Sup X {y, top}}"  by (metis A0(1-6) comp_eq1 ge_sup2 greatestD11 greatestD2 greatest_sup top)
  also have "... = Inf X {top, top}"  by (simp add: A0(1) A0(2) greatest_sup top)
  also have "... = top" by (simp add: greatestD11 inf_singleton2 top)
  finally show "Sup X {Inf X {x, y}, Sup X {x', y'}} = top"
    by simp
qed

lemma demorgs3:"\<lbrakk>x \<in> X; y \<in> X; x' \<in> X; y' \<in> X; complements x x'; complements y y'\<rbrakk> \<Longrightarrow> complements (Inf X {x, y}) (Sup X {x', y'})" by (meson blattice.axioms(2) blattice_axioms blattice_axioms_def complI1 demorgs1 demorgs2 distributive_lattice_def l_inf_closed lattD42 ssupD4)
lemma demorgs4:"\<lbrakk>x \<in> X; y \<in> X; x' \<in> X; y' \<in> X; complements x x'; complements y y'\<rbrakk> \<Longrightarrow> complements (Sup R X {x, y}) (Inf X {x', y'})" by (metis complements_idemp demorgs3)


end                    

locale complemented_distr_lattice=blattice+
  assumes comp:"x \<in> X \<Longrightarrow> (\<exists>x' \<in> X. complements x x')"
begin
definition compl where "compl a \<equiv> (THE a'. a' \<in> X \<and> complements a a' )"
lemma compl_unique2:"x \<in> X \<Longrightarrow> \<exists>!x' \<in> X. complements x x'"using blattice.complements_unique1 blattice_axioms comp by blast
lemma compl_unique3:"x \<in> X \<Longrightarrow> compl x \<in> X \<and> complements x (compl x) "
proof-
  assume A0:"x \<in> X"  obtain x' where B0:"x' \<in> X \<and> complements x x'" using A0 comp by blast
  have B1:"compl x = x'" using A0 B0 compl_def compl_unique2 by fastforce
  show "compl x \<in> X \<and> complements x (compl x)"by (simp add: B0 B1)
qed

lemma compl_closed[intro]:"x \<in> X \<Longrightarrow> compl x \<in> X" by (simp add: compl_unique3)
lemma compl_unique4:"\<lbrakk>a \<in> X; x \<in> X; y \<in> X; Sup X {a, x} = top; Sup X {a, y} = top; Inf X {a, x} = bot; Inf X {a, y} = bot\<rbrakk> \<Longrightarrow> x=y" using complI1 complements_unique1 by presburger
lemma compl_unique5:"\<lbrakk>x \<in> X; y \<in> X; Sup R X {x, y}= top; Inf X {x, y} = bot\<rbrakk> \<Longrightarrow> compl x = y" using complI1 compl_unique3 complements_unique1 by presburger
lemma compl_idem:"x \<in> X \<Longrightarrow> compl (compl x) = x" using compl_unique3 complements_idemp complements_unique1 by blast
lemma disj_cancel_right:"x \<in> X \<Longrightarrow> Sup X {x, compl x} = top" by (simp add: comp_eq1 compl_unique3)
lemma conj_cancel_right:"x \<in> X \<Longrightarrow> Inf X {x, compl x} = bot"  using comp_eq2 compl_unique3 by presburger
lemma de_morgans_cinf:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compl (Inf X {x, y}) = Sup X {compl x, compl y}"
proof-
  fix x y assume A0:"x \<in> X" "y \<in> X"
  obtain B0:"compl x \<in> X \<and> complements x (compl x)" and B1:"compl y \<in> X \<and> complements y (compl y)"   by (simp add: A0(1) A0(2) compl_unique3)
  have B1:" complements (Inf X {x, y}) (Sup X {compl x,compl y})"  using demorgs3[of x y "compl x" "compl y"]   using A0(1) A0(2) B0 B1 by fastforce
  show "compl (Inf X {x, y}) = Sup X {compl x, compl y}"
    by (metis A0(1-2) B1 blattice.axioms(2) blattice.complements_unique1 blattice_axioms blattice_axioms_def compl_unique3 distr_latticeD5 l_inf_closed l_sup_closed)
qed 

lemma de_morgans_csup:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> compl (Sup R X {x, y}) = Inf X {compl x, compl y}"
proof-
  fix x y assume A0:"x \<in> X" "y \<in> X"
  obtain B0:"compl x \<in> X \<and> complements x (compl x)" and B1:"compl y \<in> X \<and> complements y (compl y)"   by (simp add: A0(1) A0(2) compl_unique3)
  have B1:" complements (Sup R X {x, y}) (Inf X {compl x,compl y})"  using demorgs4[of x y "compl x" "compl y"]   using A0(1) A0(2) B0 B1 by fastforce
  show "compl (Sup R X {x, y}) = Inf X {compl x, compl y}"
    by (metis A0(1-2) B1 blattice.axioms(2) blattice.complements_unique1 blattice_axioms blattice_axioms_def compl_unique3 distr_latticeD5 l_inf_closed l_sup_closed)
qed 

lemma compl_inf_le:"\<lbrakk>x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> Inf X {x, compl y} = bot"
proof-
  fix x y assume A0:"x \<in> X" "y \<in> X ""(x, y)\<in>R"
  have B0:"compl y \<in> X"  by (simp add: A0(2) compl_unique3)
  have B1:"Inf X {x, compl y} \<le> Inf X {y, compl y}"   using A0(1-3) B0 binf_leI4 blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD5 lattD41 by blast 
  also have "... = bot" by (simp add: A0(2) conj_cancel_right)
  then show "Inf X {x, compl y} = bot"  by (metis A0(1-3) B0 binf_assoc1 binf_commute2 bot blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD5 lattD41 le_inf2 least_inf)
qed


lemma compl_inf_ge:"\<lbrakk>x \<in> X; y \<in> X; Inf X {x, compl y} = bot\<rbrakk> \<Longrightarrow>  (x, y)\<in>R"
proof-
  fix x y assume A0:"x \<in> X" "y \<in> X ""Inf X {x, compl y} = bot"
  have B0:"compl y \<in> X"  by (simp add: A0(2) compl_unique3)
  have B1:"Inf X {x, y} = Sup X {Inf X {x, y}, Inf X {x, compl y}}"   by (metis A0(1) A0(2) A0(3) bot blattice.axioms(2) blattice_axioms blattice_axioms_def distributive_lattice_def l_inf_closed least_sup)
  also have B2:"...     = Inf X {x, Sup X {y, compl y}}"  by (metis A0(1) A0(2) B0 blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD3)
  also have B3:"...     = x"  by (simp add: A0(1) A0(2) disj_cancel_right greatest_inf top)
  then show "(x, y)\<in>R"
    by (metis A0(1) A0(2) blattice.axioms(2) blattice_axioms blattice_axioms_def calculation distributive_lattice_def lat_binf_leI2)
qed

lemma compl_sup_le1:"\<lbrakk>x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> Sup X {compl x, y} = top" by (metis compl_closed compl_idem compl_inf_le conj_cancel_right de_morgans_cinf disj_cancel_right)
lemma compl_sup_le2:"\<lbrakk>x \<in> X; y \<in> X;  Sup X {compl x, y} = top \<rbrakk> \<Longrightarrow> (x, y)\<in>R"  by (metis compl_closed compl_idem compl_inf_ge conj_cancel_right de_morgans_csup disj_cancel_right)

lemma inf_le_comp1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X; Inf X {x, y} \<le> z\<rbrakk> \<Longrightarrow> x \<le> Sup X {compl y, z}"
proof-
  fix x y z assume P:"x \<in> X" "y \<in> X " "z \<in> X" "Inf X {x, y} \<le> z"
  have B0:"compl y \<in> X"  by (simp add: P(2) compl_unique3)
  have B1:"Sup X {compl y, Inf X {x, y}} \<le> Sup X {compl y, z}"  by (meson B0 P blattice.axioms(2) blattice_axioms blattice_axioms_def bsup_geI5 compl_inf_ge conj_cancel_right distributive_lattice_def l_inf_closed latt_iff)
  have B2:"Inf X {Sup X {compl y ,x}, Sup X {compl y, y}} \<le> Sup X {compl y, z}"  by (metis B0 B1 P(1) P(2) blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD1)
  have B3:"Inf X {Sup X {compl y, x}, top} \<le> Sup X {compl y, z}"  using B0 B2 P(2) compl_idem disj_cancel_right by force
  have B4:"Sup X {compl y, x} \<le> Sup X {compl y, z}"   by (metis B0 B1 P(1) P(2) blattice.axioms(2) blattice_axioms blattice_axioms_def compl_idem disj_cancel_right distributive_lattice_def greatest_inf l_sup_closed top)
  then show "x \<le> Sup X {compl y, z}" by (metis B0 P(1) P(3) blattice.axioms(2) blattice_axioms blattice_axioms_def bsup_iff distributive_lattice_def l_sup_closed latt_iff)
qed


lemma inf_le_comp2:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X;  x \<le> Sup X {compl y, z}\<rbrakk> \<Longrightarrow> Inf X {x, y} \<le> z"
proof-
  fix x y z assume P:"x \<in> X" "y \<in> X " "z \<in> X" "x \<le> Sup X {compl y, z}"
  have B0:"Inf X {x, y} \<le> Inf X {Sup X {compl y, z}, y}" by (metis P(1-4) binf_leI4 blattice.axioms(2) blattice_axioms blattice_axioms_def compl_closed distributive_lattice_def l_sup_closed latt_iff)
  have B1:"Inf X {x, y} \<le> Sup X {Inf X {y, compl y}, Inf X {z, y}}" by (metis (full_types) B0 P(2) P(3) blattice.axioms(2) blattice_axioms blattice_axioms_def compl_closed distr_latticeD3 insert_commute)
  have B2:"Inf X {x, y} \<le> Sup X {bot, Inf X {z, y}}"  using B1 P(2) conj_cancel_right by fastforce
  have B3:"Inf X {x, y} \<le> Inf X {z, y}" by (metis B2 P(2) P(3) bot blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD5 insert_commute lattD41 least_sup sinfD4)
  then show "Inf X {x, y} \<le> z"  by (meson P(1) P(2) P(3) binf_iff blattice.axioms(2) blattice_axioms blattice_axioms_def distr_latticeD5 lattD41 sinfD4)
qed

lemma inf_comp_sup1:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> x \<le> Sup X {compl y, z} \<longleftrightarrow>  Inf X {x, y} \<le> z" by (meson inf_le_comp1 inf_le_comp2)
lemma inf_comp_sup2:"\<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> x \<le> Sup X {y, z} \<longleftrightarrow>  Inf X {x, compl y} \<le> z" by (metis compl_closed compl_idem inf_comp_sup1) 

lemma compl_anti1:"\<lbrakk>x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> compl y \<le> compl x"
proof-
  fix x y assume A0:"x \<in> X" "y \<in> X" "(x, y)\<in>R"
  have B0:"Sup R X {x, y} = y"  by (simp add: A0(1) A0(2) A0(3) ge_sup1)
  have B1:"compl (Sup R X {x, y}) = compl y" by (simp add: B0)
  have B2:"Inf X {compl x, compl y} = compl y" using A0(1-2) B1 de_morgans_csup by force
  show "compl y \<le> compl x" by (meson A0(1) A0(2) B2 blattice.axioms(2) blattice_axioms blattice_axioms_def compl_unique3 distributive_lattice_def latt_le_iff2)
qed

lemma compl_anti2:"\<lbrakk>x \<in> X; y \<in> X; compl (x, y)\<in>R\<rbrakk> \<Longrightarrow> compl (y, x)\<in>R"by (metis compl_anti1 compl_idem compl_unique3)
lemma compl_anti3:"\<lbrakk>x \<in> X; y \<in> X;  y \<le> compl x\<rbrakk> \<Longrightarrow> x \<le> compl y" by (metis compl_anti1 compl_idem compl_unique3)

lemma meet_bot_iff:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (Inf X {x, y} = bot) \<longleftrightarrow> (x \<le> compl y)"by (metis compl_closed compl_idem compl_inf_ge compl_inf_le)
lemma join_top_iff:"\<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {x, y} = top) \<longleftrightarrow> (compl (x, y)\<in>R)" by (metis compl_closed compl_idem compl_sup_le1 compl_sup_le2)

lemma proper_filter_boolD1:"\<lbrakk>is_pfilter X F; x \<in> F\<rbrakk> \<Longrightarrow> compl x \<notin> F" by (metis bot conj_cancel_right dist distr_latticeD5 filter_finf_closed1 in_mono is_pfilterD1 is_pfilterD3 is_pfilterD4 lattD41)

lemma proper_filter_boolI1:"\<lbrakk>is_filter X F; (\<And>x. x \<in> F \<Longrightarrow> compl x \<notin> F) \<rbrakk> \<Longrightarrow> is_pfilter X F"   using compl_closed filter_ex_elem is_pfilterI1 by blast
lemma proper_filter_boolD2:"\<lbrakk>is_pfilter X F; x \<in> X\<rbrakk> \<Longrightarrow> \<not> (x \<in> F \<and> compl x \<in> F)"  using proper_filter_boolD1 by auto
lemma proper_filter_boolI2:"\<lbrakk>is_filter X F; (\<And>x. x \<in> X \<Longrightarrow> \<not> (x \<in> F \<and> compl x \<in> F)) \<rbrakk> \<Longrightarrow> is_pfilter X F" using bot compl_unique3 is_pfilterI1 leastD11 by blast

lemma trivial_upsetI1:"bot \<in> F \<Longrightarrow> is_ord_cl X F (\<le>) \<Longrightarrow> X \<subseteq> F" using bot is_ord_clE1 leastD2 by blast
lemma trivial_filterI1:"bot \<in> F \<Longrightarrow> is_filter X F \<Longrightarrow> X = F" by (simp add: filterD2 filterD4 subset_antisym trivial_upsetI1) 
lemma trivial_filterI2:"\<lbrakk>x \<in> F; compl x \<in> F; is_filter X F\<rbrakk> \<Longrightarrow> X=F" using is_pfilterI1 proper_filter_boolD1 by blast

lemma pmb_filters1:"\<lbrakk>is_pfilter X F; sup_prime X F; x \<in> X\<rbrakk> \<Longrightarrow> (x \<in> F \<or> compl x \<in> F) \<and> \<not>(x \<in> F \<and> compl x \<in> F)"by (metis compl_unique3 disj_cancel_right filter_greatestD2 is_pfilterD1 proper_filter_boolD1 sup_primeD1 top)


lemma pmb_filters2:
  assumes A0:"is_pfilter X F" and A1:"\<And>x. x \<in> X \<Longrightarrow> (x \<in> F \<or> compl x \<in> F) \<and> \<not>(x \<in> F \<and> compl x \<in> F)"
  shows "is_maximal (pfilters_on X) F"
proof-
  have B0:"F \<in> pfilters_on X"    using A0 is_pfilter_def by blast
  have B1:"\<And>G. \<lbrakk>G \<in> filters_on X;  F \<subset> G \<rbrakk> \<Longrightarrow> G = X"
  proof-
    fix G assume A2:"G \<in> filters_on X" and A3:"F \<subset> G"
    obtain z where B10: "z \<in> G - F"  using A3 by auto
    have B11:"z \<notin> F" using B10 by blast 
    have B12:"compl z \<in> F"  by (meson A1 A2 B10 Diff_iff filterD21 filters_on_iff)
    have B13:"compl z \<in> G \<and> z \<in> G"  using A3 B10 B12 by blast
    have B14:"is_filter X G"   using A2 filters_on_iff by auto
    show "G=X"  using B13 B14 trivial_filterI2 by blast 
  qed
  have B2:"\<And>G. \<lbrakk>G \<in> pfilters_on X;  F \<subseteq> G \<rbrakk> \<Longrightarrow> G = F" using B1 filters_on_def by blast
  show ?thesis
    by (metis (no_types, lifting) B0 B2 is_maximal_def)
qed

lemma pmb_filters3:"\<lbrakk>is_pfilter X F; sup_prime X F\<rbrakk> \<Longrightarrow> is_maximal (pfilters_on X) F" by (simp add: pmb_filters1 pmb_filters2)


(*that maximal proper filters are prime holds in the context of distributive lattices e.g. by distr_lattice_maximal_prime
*)

end

definition meet_reducible::"'a::order set \<Rightarrow> 'a \<Rightarrow> bool" where "meet_reducible X x \<equiv> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf X A x)"
abbreviation meet_irr where "meet_irr X x \<equiv> \<not>(meet_reducible X x)"
lemma mredI1:"\<lbrakk>A \<in> Pow_ne X; x \<notin> A; is_inf X A x\<rbrakk> \<Longrightarrow> meet_reducible X x" using meet_reducible_def by blast 
lemma mredI2:"\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf X A x \<Longrightarrow> meet_reducible X x" by (simp add: meet_reducible_def)
lemma mredD1:"meet_reducible X x \<Longrightarrow> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf X A x)"  by (simp add: meet_reducible_def) 
lemma mredD2:"meet_reducible X x \<Longrightarrow> \<not>(is_greatest X x)"
proof-
  assume A0:"meet_reducible X x"
  obtain A where B0:"A \<in> Pow_ne X" "x \<notin> A" "is_inf X A x"  using A0 mredD1 by blast
  have B1:"A \<subseteq> X"  by (simp add: B0(1) pow_neD1)
  obtain a where  B2:"a \<in> A"  using B0(1) pow_ne_iff2 by fastforce
  have B3:"x < a"  using B0(2) B0(3) B2 is_infD1121 order_less_le by blast
  show "\<not>(is_greatest X x)"  by (meson B1 B2 B3 in_mono maximalD4 maximalI3)
qed
lemma mredD3:"\<lbrakk>m \<in> X; is_clattice X;  \<not>(is_greatest X m)\<rbrakk> \<Longrightarrow> {x \<in> X. m < x} \<noteq> {}"  by (metis Collect_empty_eq antisym_conv2 clatD1 csupD3 greatest_iff)
lemma mredD4:
  assumes A0:"is_clattice X" and A1:"m \<in> X" and A2:"\<not>(is_greatest X m)" and A3:"\<not>(m < Inf X {x \<in> X. m < x})"
  shows "meet_reducible X m"
proof-
  let ?A="{x \<in> X. m < x}"
  obtain B0:"?A \<subseteq> X" and B1:"?A \<noteq> {}" using A0 A1 A2 mredD3 by auto
  have B2:"m \<le> Inf X ?A"  by (metis (no_types, lifting) A0 A1 B0 B1 CollectD cinfD62 clatD2 lb_def order.strict_implies_order)
  have B3:"m = Inf X ?A"  using A3 B2 order_less_le by blast
  have B4:"?A \<in> Pow_ne X"  using B1 pow_ne_iff2 by blast
  have B5:"m \<notin> ?A"   by simp
  have B6:"is_inf X ?A m"  by (metis A0 B0 B1 B3 cinfD4 clatD2)
  show "meet_reducible X m"  using B4 B6 mredI1 by blast
qed
lemma mredD5:"\<lbrakk>is_clattice X; m \<in> X; \<not>(is_greatest X m); meet_irr X m\<rbrakk> \<Longrightarrow> m < Inf X {x \<in> X. m < x}" using mredD4 by blast
lemma mredD6:
  assumes A0:"is_clattice X" and A1:"m \<in> X" and A2:"\<not>(is_greatest X m)" and A3:"meet_reducible X m"
  shows "\<not> ( m < Inf X {x \<in> X. m < x})"
proof-
  let ?A="{x \<in> X. m < x}"
  obtain A where B0:"A \<in> Pow_ne X" "m \<notin> A" "is_inf X A m"  using A3 meet_reducible_def by blast 
  obtain B1:"\<And>x. x \<in> A \<Longrightarrow> m < x"  using B0(2) B0(3) is_infD1121 order_less_le by blast
  obtain B2:"A \<subseteq> ?A"  using B0(1) \<open>\<And>thesis::bool. ((\<And>x::'a::order. x \<in> (A::'a::order set) \<Longrightarrow> (m::'a::order) < x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pow_neD1 by auto
  have B3:"?A \<subseteq> X" "?A \<noteq> {}"  apply simp  using A0 A1 A2 mredD3 by blast
  have B4:"m \<le> Inf X ?A"   by (metis (no_types, lifting) A0 A1 B3(1) B3(2) CollectD cinfD62 clatD2 lb_def order.strict_implies_order)
  have B5:"... \<le> Inf X A"  by (simp add: A0 B2 inf_anti1)
  have B6:"... = m "    by (simp add: B0(3) inf_equality)
  show "\<not> ( m < Inf X {x \<in> X. m < x})"  using B5 B6 leD by blast
qed
lemma mredD7:"\<lbrakk>is_clattice X; m \<in> X; \<not>(is_greatest X m); m < Inf X {x \<in> X. m < x} \<rbrakk> \<Longrightarrow>meet_irr X m " using mredD6 by auto

lemma mred_iff1:"\<lbrakk>is_clattice X; m \<in> X; \<not>(is_greatest X m)\<rbrakk> \<Longrightarrow>  m < Inf X {x \<in> X. m < x} \<longleftrightarrow> meet_irr X m " using mredD5 mredD7 by blast
lemma mredD8:"\<lbrakk>m \<in> X; is_clattice X;  (is_greatest X m)\<rbrakk> \<Longrightarrow> meet_irr X m"   using mredD2 by blast 

lemma mirredD1:"\<lbrakk>A \<in> Pow_ne X; is_inf X A x; meet_irr X x\<rbrakk> \<Longrightarrow>x \<in> A " using mredI1 by blast 
lemma mirredI1:"(\<And>A.  \<lbrakk>A \<in> Pow_ne X; is_inf X A x\<rbrakk> \<Longrightarrow> x \<in> A) \<Longrightarrow>  meet_irr X x "   using mredD1 by blast
lemma mirredD2:" meet_irr X x \<Longrightarrow>(\<And>A.  \<lbrakk>A \<in> Pow_ne X; is_inf X A x\<rbrakk> \<Longrightarrow> x \<in> A)" using mredI1 by blast 


lemma compact_dense:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"x \<in> X"
  shows "x = Sup X {k \<in> compact_elements X. k \<le> x}"
proof-
  let ?K=" compact_elements X"
  let ?Kd="{k \<in> ?K. k \<le> x}"
  obtain Kx where A3:"Kx \<in> Pow ?K" "is_sup R X Kx x" by (meson A1 A2 compactly_generatedD1)
  have B0:"?K \<subseteq> X"   by (simp add: compact_elements_sub)
  have B1:"?Kd \<subseteq> X" using B0 by blast
  have B2:"Kx \<subseteq> ?Kd" using A3(1) A3(2) is_supD1121 by fastforce
  have B3:"Sup X ?Kd \<le> Sup X Kx"   by (metis (no_types, lifting) A0 A2 A3(2) B1 B2 clatD1 csupD62 dual_order.trans empty_iff mem_Collect_eq subsetI sup_equality sup_iso1 ub_def)
  have B4:"... = x"  by (simp add: A3(2) sup_equality)
  have B6:"x \<le> Sup X ?Kd"   using A0 B1 B2 B4 sup_iso1 by blast
  show ?thesis using B3 B4 B6 by auto
qed

lemma compactly_generated_meets:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"x \<in> X" and A3:"y \<in> X" and 
          A4:"\<not>((y, x)\<in>R)"
  shows "\<exists>k \<in> compact_elements X. k \<le> y \<and> \<not>(k \<le> x)"
  by (meson A1 A2 A3 A4 PowD compactly_generatedD1 is_supD1121 is_supE4 subset_iff ub_def)

lemma meet_reduction1:"\<lbrakk>is_clattice X; m \<in> X; meet_reducible X m\<rbrakk> \<Longrightarrow> m \<in> lbd R X {x \<in> X. m < x}" using lbd_mem_iff2 by fastforce

lemma meet_reduction2:"\<lbrakk>is_clattice X; m \<in> X; meet_reducible X m\<rbrakk> \<Longrightarrow>  m=Inf X {x \<in> X. m < x}"
proof-
  let ?A="{x \<in> X. m < x}"
  assume A0:"is_clattice X" "m \<in> X" "meet_reducible X m"
  obtain A where B0:"A \<in> Pow_ne X" "m \<notin> A" "is_inf X A m"  using A0(3) mredD1 by blast
  obtain B1:"\<And>x. x \<in> A \<Longrightarrow> m < x"  using B0(2) B0(3) is_infD1121 order_less_le by blast
  obtain B2:"A \<subseteq> ?A"  using B0(1) \<open>\<And>thesis::bool. ((\<And>x::'a::order. x \<in> (A::'a::order set) \<Longrightarrow> (m::'a::order) < x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pow_neD1 by auto
  have B3:"?A \<subseteq> X"  by simp
  have B4:"?A \<noteq> {}"  using B0(1) B2 pow_ne_iff2 by fastforce 
  have B5:"m \<le> Inf X ?A" by (metis (no_types, lifting) A0(1) A0(2) B3 B4 CollectD cinfD62 clatD2 lb_def order.strict_implies_order)
  have B6:"... \<le> Inf X A"  by (simp add: A0 B2 inf_anti1)
  have B7:"... = m "  by (simp add: B0(3) inf_equality)
  show "m=Inf X {x \<in> X. m < x}"
    using B5 B6 B7 by auto
qed

lemma mirred_temp1:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)" and A5:"is_compact X k" and A6:"k \<le> b" and A7:"\<not>(k \<le> a)" and 
          A9:"D \<subseteq>  {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}" and A10:"is_dir D (\<le>)" and A11:"D \<noteq> {}"
  shows "Sup X D \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}"
proof-
  let ?Q="{q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}"
  have B0:"?Q \<subseteq> X" by simp
  obtain j where B1:"is_sup R X D j"   by (meson A0 A9 B0 clatD21 dual_order.trans)
  have B2:"j \<in> X"    using B1 is_supE1 by blast
  have B3:"\<forall>d. d \<in> D \<longrightarrow> a \<le> d"   using A9 by blast
  have B4:"a \<in> lbd R X D"   by (simp add: A2 B3 lbdI)
  have B5:"a \<le> j"   by (meson A11 B1 B3 bot.extremum_uniqueI dual_order.trans is_supE2 subset_emptyI ub_def)
  have B6:"\<not> (k \<le> j)"
  proof(rule ccontr)
    assume P0:"\<not>(\<not> (k \<le> j))" obtain P1:"k \<le> j"  using P0 by auto
    have B7:"k \<le> Sup X D"   using B1 P1 sup_equality by blast
    have B8:"D \<in> Pow_ne X" by (meson A11 A9 B0 pow_neI subset_trans)
    have B9:"is_sup_semilattice R X"    by (simp add: A0 clatD1 csup_fsup)
    obtain d where B10:"d \<in> D \<and> k \<le> d" using ccompact0   using A10 A5 B7 B8 B9 by blast
    show False   using A9 B10 by blast
  qed
  have B11:"j \<in> ?Q"   by (simp add: B2 B5 B6)
  show "Sup X D \<in> ?Q"
    using B1 B11 sup_equality by blast
qed




lemma mirred_temp2b:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)" and A5:"is_compact X k" and A6:"k \<le> b" and A7:"\<not>(k \<le> a)"
  shows "\<exists>m \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}. \<forall>q \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}.  m \<le> q \<longrightarrow> q = m"
proof(rule predicate_Zorn)
  show "partial_order_on {q \<in> X. a \<le> q \<and> \<not> k \<le> q} (relation_of (\<le>) {q \<in> X. a \<le> q \<and> \<not> k \<le> q})"
    by (smt (verit, del_insts) dual_order.antisym order_trans partial_order_on_relation_ofI verit_comp_simplify1(2))
  show "\<And>C. C \<in> Chains (relation_of (\<le>) {q \<in> X. a \<le> q \<and> \<not> k \<le> q}) \<Longrightarrow> \<exists>u\<in>{q \<in> X. a \<le> q \<and> \<not> k \<le> q}. \<forall>q\<in>C. q \<le> u"
proof-
    let ?Q="{q \<in> X. a \<le> q \<and> \<not> k \<le> q}"
    fix C assume A8:"C \<in> Chains (relation_of (\<le>) ?Q)"
    have B0:"C \<subseteq> X"   using A8 Chains_relation_of by blast
    have B1:"\<forall>c. c \<in> C \<longrightarrow> (a, c)\<in>R"   using A8 Chains_relation_of by force
    have B2:"\<forall>c. c \<in> C \<longrightarrow> \<not> (k \<le> c)"   using A8 Chains_relation_of by blast
    show "\<exists>u\<in>{q \<in> X. a \<le> q \<and> \<not> k \<le> q}. \<forall>q\<in>C. q \<le> u"
      proof(cases "C = {}")
        case True
        then show ?thesis  using A2 A7 by blast
      next
        case False
        have B3:"C \<noteq> {}"   by (simp add: False)
        have B4:"\<And>x y. x \<in> C \<and> y \<in> C \<longrightarrow> (\<exists>z \<in> C. x \<le> z \<and> y \<le> z)"
        proof
          fix x y assume A10:"x \<in> C \<and>  y \<in> C"
          have B1:"(x, y) \<in> relation_of (\<le>) ?Q \<or> (y, x) \<in> relation_of (\<le>) ?Q" using Chains_def[of " relation_of (\<le>) ?Q"] A8 A10 by auto
          have B2:"(x, y)\<in>R \<or> (y, x)\<in>R" using B1  relation_of_def[of "(\<le>)" "?Q"] by blast
          show "(\<exists>z \<in> C. x \<le> z \<and> y \<le> z)"  using A10 B2 by blast
        qed
        have B5:"is_dir C (\<le>)" by (simp add: B4 is_updirI1)
        have B6:"C \<subseteq> ?Q"    using A8 Chains_relation_of by blast
        have B7:"Sup X C \<in> ?Q" using A0 A1 A2 A3 A4 A5 A6 A7 B3 B5 B6  mirred_temp1[of X a b k C] by blast
        have B8:"\<forall>c  \<in> C. c \<le> Sup X C"     by (meson A0 B0 False clatD1 csupD51 ubE) 
        then show ?thesis    using B7 by blast 
    qed
  qed
qed

lemma mirred_temp2c:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)" and A5:"is_compact X k" and A6:"k \<le> b" and A7:"\<not>(k \<le> a)" and
          A8:"m \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)} \<and> ( \<forall>q \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}.  m \<le> q \<longrightarrow> q = m)"
  shows "\<not>(meet_reducible X m)"
proof(rule ccontr)
  let ?Q="{q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}"
  assume P:"\<not>\<not>(meet_reducible X m)"
  obtain P1:"meet_reducible X m"
    using P by auto
  have B0:"\<And>x. x \<in> X \<and> x > m \<longrightarrow> k \<le> x"
  proof
    fix x assume A9: "x \<in> X \<and> x > m"
    have B01:"x \<notin> ?Q" using A8 A9 nless_le by blast 
    have B02:"(a, x) \<in> R"  using A8 A9 by force
    show "k \<le> x" using A9 B01 B02 by blast
  qed
  have B1:"m=Inf X {x \<in> X. m < x}"  using A0 A8 P meet_reduction2 by blast
  have B2:"k \<in> lbd R X {x \<in> X. m < x}"  by (metis (mono_tags, lifting) A5 B0 CollectD compactD2 lbdI)
  have B3:"k \<le> m"    by (metis A0 B1 B2 Collect_subset P cinfD61 clatD2 clatD22 inf_equality is_inf_def lbd_empty mredD2)
  show False
    using A8 B3 by blast
qed


lemma mirred_temp2d:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)"
  obtains m where "m \<in> X" "meet_irr X m" "(a, m)\<in>R" "\<not> (b \<le> m)"
proof-
  obtain k where B0:"k \<in> compact_elements X" and  B1:"k \<le> b" and B2: "\<not> (k \<le> a)"  using A0 A1 A2 A3 A4 compactly_generated_meets by blast
  have B0b:"is_compact X k"   using B0 compact_elements_mem_iff1 by blast
  obtain m where B3:"m \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)} \<and> (\<forall>q \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}.  m \<le> q \<longrightarrow> q = m)"   using A0 A1 A2 A3 A4 B0b B1 B2 mirred_temp2b[of X a b k] by blast
  have B4:"\<not>(meet_reducible X m)" using mirred_temp2c[of X a b  k m] A0 A1 A2 A3 A4 B0b B1 B2 B3  by blast 
  show ?thesis
    using B1 B3 B4 that by force
qed


lemma mirred_temp3:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X"
  shows "a = Inf X {m \<in> X. meet_irr X m \<and> (a, m)\<in>R}"
proof-
  let ?M="{m \<in> X. meet_irr X m \<and> (a, m)\<in>R}" 
  obtain top where top:"is_greatest X top" using A0 clatD1 csupD3 by blast
  obtain B0:"?M \<subseteq> X" and B1:"top \<in> ?M" and B2:"?M \<noteq> {}"   by (metis (no_types, lifting) A2 empty_iff greatestD11 greatestD2 mem_Collect_eq mredD2 subsetI top)
  obtain b where idef:"is_inf X ?M b"  using A0 B0 clatD22 by blast
  have B4:"(a, b)\<in>R"  using A2 idef is_infE4 lb_def by blast
  have B5: "\<not> (a < b)"
  proof(rule ccontr)
    assume B5dneg:"\<not> \<not> (a < b)" obtain B5neg:"a < b"  using B5dneg by auto
    obtain m where B50:"m \<in> X" and B51:"meet_irr X m" and  B52:"(a, m)\<in>R" and B53:"\<not> (b \<le> m)" by (meson A0 A1 A2 B5neg idef is_infE1 leD mirred_temp2d)
    have B54:"m \<in> ?M"   by (simp add: B50 B51 B52)
    have B55:"b \<le> m"  using B54 idef is_infD1121 by blast
    show False
      using B53 B55 by auto
  qed
  have "a = b"  using B4 B5 nless_le by blast
  show ?thesis
    using \<open>(a::'a::order) = (b::'a::order)\<close> idef inf_equality by fastforce
qed

lemma meet_irr_imp_fmeet_irr:
  "\<lbrakk>m \<in> X; is_lattice X;  meet_irr X m\<rbrakk> \<Longrightarrow> fin_inf_irr X m"
proof-
  assume A0:"m \<in> X" "is_lattice X" "meet_irr X m"
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and>  m = Inf X {a, b} \<longrightarrow> m = a \<or> m = b"
  proof
    fix a b assume A1:" a \<in> X \<and> b \<in> X \<and>  m = Inf X {a, b} "
    have B1:" {a, b} \<in> Pow_ne X"   by (simp add: A1 pow_ne_iff2)
    have B2:"is_inf X {a, b} m" by (simp add: A0(2) A1 lattD31)
    have B3:"m \<in> {a, b}"   using A0(3) B1 B2 mredI1 by blast
    show "m = a \<or> m = b"  using B3 by fastforce
  qed
  show "fin_inf_irr X m"
    using B0 fin_inf_irr_def by blast  
qed

lemma pfilters_metofprimes:
  assumes A0:"distributive_lattice X" and A1:"is_greatest X top" and A2:"F \<in> pfilters X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on X \<and> meet_irr (filters_on X) Fm " and "F = Inf (filters_on X) M"
proof-
  let ?FX="(filters_on X)"
  have B0:"compactly_generated ?FX"   using A0 A1 distr_latticeD5 filters_on_lattice_compactgen lattD1 by auto
  have B1:"is_clattice ?FX"  using A0 A1 distr_latticeD5 lattice_filters_complete by auto
  have B2:"F \<in> ?FX" by (simp add: A2 filters_on_iff pfilters_memD1)
  have B3:"F = Inf ?FX {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}"   by (simp add: B0 B1 B2 mirred_temp3)
  have B4:"\<forall>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm} \<longrightarrow> Fm \<in> ?FX \<and> meet_irr ?FX Fm "  by fastforce
  then show ?thesis  using B3 that by blast
qed



lemma sup_prime_pfilterI3:
  assumes A0:"distributive_lattice X" and A1:"fin_inf_irr (filters_on X) F" and A2:"is_pfilter X F"
  shows "sup_prime X F"
proof-
  have B1:"(\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)"  by (metis A0 A1 A2 distributive_lattice_def elem_inf_primeI3 elem_inf_prime_def filters_lattice_inf_op filters_on_iff is_pfilter_def lattice_filters_distr)
  show ?thesis by (simp add: A0 A2 B1 distr_latticeD5 sup_prime_pfilterI2)
qed

lemma prime_filter_irr3_converse:
  "\<lbrakk>distributive_lattice X; fin_inf_irr (filters_on X) F; pfilter X F\<rbrakk> \<Longrightarrow> sup_prime X F"  by (simp add: is_pfilterI1 sup_prime_pfilterI3)
(*
lemma prime_filter_irr3:
  "\<lbrakk>is_lattice X; sup_prime X F; pfilter X F\<rbrakk> \<Longrightarrow> fin_inf_irr (filters_on X) F"
  by (metis fin_inf_irr_def prime_filter_fin_irr2)

*)

lemma pfilters_metofprimes2:
  assumes A0:"distributive_lattice X" and A1:"is_greatest X top" and A2:"F \<in> pfilters X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on X \<and> sup_prime X Fm " and "F = Inf (filters_on X) M"
proof-
  let ?FX="(filters_on X)"
  have B0:"compactly_generated ?FX"   using A0 A1 distr_latticeD5 filters_on_lattice_compactgen lattD1 by auto
  have B1:"is_clattice ?FX"  using A0 A1 distr_latticeD5 lattice_filters_complete by auto
  have B2:"F \<in> ?FX" by (simp add: A2 filters_on_iff pfilters_memD1)
  have B3:"F = Inf ?FX {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}"   by (simp add: B0 B1 B2 mirred_temp3)
  have B4:"\<And>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm} \<Longrightarrow> Fm \<in> ?FX \<and> sup_prime X Fm " 
  proof-
    fix Fm assume A3:"Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}" 
    have B40:"Fm \<in> ?FX \<and> meet_irr ?FX Fm"  using A3 by blast
    have B41:"fin_inf_irr ?FX Fm"  using A0 B40 distr_lattice_filters meet_irr_imp_fmeet_irr by blast
    have B43:"is_greatest ?FX X"   by (meson A0 distr_latticeD5 filterD2 filters_is_clr1b filters_on_iff greatest_iff lattD41)
    have B44:"sup_prime X Fm"
    proof(cases "pfilter X Fm")
      case True then show ?thesis   using A0 B40 B41 filters_on_iff prime_filter_irr3_converse sup_prime_def by blast
    next
      case False obtain B45:"Fm = X"  using B40 False filters_on_iff by blast
      then show ?thesis using sup_primeI1 by blast
    qed
    show "Fm \<in> ?FX \<and> sup_prime X Fm"  by (simp add: B40 B44)
  qed
  then show ?thesis  using B3 that by blast
qed
*)
end
