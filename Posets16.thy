theory Posets16
  imports Main
begin

section Settings
hide_const top
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

lemma leq_iff_leq_eq:
  "\<lbrakk>(a::'a::order) \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. x \<le> a \<longleftrightarrow> x \<le> b) \<Longrightarrow> a =b"
  by (simp add: order_class.order_eq_iff)

lemma geq_iff_geq_eq:
  "\<lbrakk>(a::'a::order) \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. x \<ge> a \<longleftrightarrow> x \<ge> b) \<Longrightarrow> a =b"
  by (simp add: order_class.order_eq_iff)

definition Pow_ne::"'a set \<Rightarrow> 'a set set" where
  "Pow_ne X = Pow X - {{}}"

definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where
  "Fpow_ne X = Fpow X - {{}}"

lemma pow_ne_iff1:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<in> Pow X \<and> A \<noteq> {}"
  by (simp add: Pow_ne_def)

lemma pow_ne_iff2:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<subseteq> X \<and> A \<noteq> {}"
  by (simp add: Pow_ne_def)

lemma pow_neI:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<in> Pow_ne X"
  by(simp add:Pow_ne_def)

lemma pow_neD1:
  "A \<in> Pow_ne X \<Longrightarrow> A \<subseteq> X "
  by(simp add:Pow_ne_def)

lemma pow_neD2:
  " A \<in> Pow_ne X \<Longrightarrow> A \<noteq> {} "
  by(simp add:Pow_ne_def)

lemma pow_ne_iso0:
  "A \<in> Pow_ne X \<Longrightarrow> B \<in> Pow_ne A \<Longrightarrow> B \<subseteq> X" 
   by (drule pow_neD1)+ simp

lemma pow_ne_iso1:
  "A \<in> Pow_ne X \<Longrightarrow> B \<in> Pow_ne A \<Longrightarrow> B \<in> Pow_ne X"
  by(rule pow_neI,erule pow_ne_iso0,simp,erule pow_neD2)

lemma pow_ne_bot:
  "{} \<notin> Pow_ne X"
  by(simp add:Pow_ne_def)
               
lemma pow_ne_top:
  "X \<noteq> {} \<Longrightarrow> X \<in> Pow_ne X"
  by(simp add:Pow_ne_def)

lemma fpow_ne_iff1:
  "A \<in> Fpow_ne X \<longleftrightarrow> A \<in> Fpow X \<and> A \<noteq> {}"
  by (simp add: Fpow_ne_def)

lemma fpow_ne_iff2:
  "A \<in> Fpow_ne X \<longleftrightarrow> A \<subseteq> X \<and> finite A \<and> A \<noteq> {}"
  by (simp add: Fpow_Pow_finite fpow_ne_iff1)

lemma fpow_neI:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<in> Fpow_ne X"
  by (simp add: Fpow_def fpow_ne_iff1)

lemma fpow_neD0:
  "A \<in> Fpow_ne X \<Longrightarrow> A \<in> Pow X "
  by (simp add: fpow_ne_iff2)

lemma fpow_neD0b:
  "A \<in> Fpow_ne X \<Longrightarrow> A \<in> Pow_ne X"
  by (simp add: fpow_ne_iff2 pow_ne_iff1)

lemma fpow_neD1:
  "A \<in> Fpow_ne X \<Longrightarrow> A \<subseteq> X "
  by (simp add: fpow_ne_iff2)

lemma fpow_neD2:
  " A \<in> Fpow_ne X \<Longrightarrow> A \<noteq> {} "
  by (simp add: fpow_ne_iff2)

lemma fpow_neD3:
  " A \<in> Fpow_ne X \<Longrightarrow> finite A "
  by (simp add: fpow_ne_iff2)

lemma fpow_ne_iso0:
  "A \<in> Fpow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<subseteq> X" 
   by (drule fpow_neD1)+ simp

lemma fpow_ne_iso1:
  "A \<in> Fpow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<in> Fpow_ne X"
  by(rule fpow_neI,erule fpow_ne_iso0,simp,erule fpow_neD2, erule fpow_neD3)

lemma fpow_ne_iso2:
  "A \<in> Pow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<in> Fpow_ne X"
  by (metis dual_order.trans fpow_ne_iff2 pow_ne_iff2)

lemma fpow_ne_bot:
  "{} \<notin> Fpow_ne X"
  by (simp add: fpow_ne_iff1)

lemma ne_subset_ne:
  "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}"
  by blast

definition CartesianProduct::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "CartesianProduct I X = {f::('I \<Rightarrow> 'X). \<forall>i \<in> I. (f i) \<in> (X i)}"

abbreviation Prod::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "Prod I X \<equiv> CartesianProduct I X"

lemma prod_mem:
  "f \<in> Prod I X \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (X i))"
  by (simp add: CartesianProduct_def)

lemma prod_memI:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) \<in> (X i)) \<Longrightarrow> f \<in> Prod I X" 
  by(simp add:CartesianProduct_def)

lemma prod_memD:
  "f \<in> Prod I X \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i ) \<in> (X i))"
  by(simp add:CartesianProduct_def)

lemma prod_memE:
  "f \<in> Prod I X \<Longrightarrow> i \<in> I\<Longrightarrow> (f i ) \<in> (X i)"
  by(simp add:CartesianProduct_def)

definition choice::"'I set \<Rightarrow>('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X)" where
  "choice I X \<equiv> (\<lambda>i. SOME x. x \<in> X i)"

lemma choice_ne1:
  "\<lbrakk>I \<noteq> {}; (\<And>i. i \<in> I \<Longrightarrow> X i \<noteq> {})\<rbrakk> \<Longrightarrow> choice I X \<in> Prod I X"
  by (simp add: choice_def prod_memI some_in_eq)

lemma axiom_of_choice_lol:
  "\<lbrakk>I \<noteq> {}; (\<And>i. i \<in> I \<Longrightarrow> X i \<noteq> {})\<rbrakk> \<Longrightarrow> Prod I X \<noteq> {}"
  by (metis choice_ne1 empty_iff)

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


section Bounds
subsection UpperBoundsPredicate

definition ub::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "ub" 50) where 
   "x ub  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x)"

lemma ub_iff1:
  "x ub A \<longleftrightarrow> (\<forall>a \<in> A. a \<le> x)"
  by(auto simp add:ub_def)

lemma ubI: 
  "(\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> x ub A" 
  by (simp add:ub_def)

lemma ubD:
   "\<lbrakk>x ub A;  a \<in> A\<rbrakk>  \<Longrightarrow> a \<le> x "
    by (simp add:ub_def)

lemma ubE:
  "x ub A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x)"
  by (simp add: ubD)

lemma ub_ant2:
  "\<lbrakk>A \<subseteq> B; x ub B\<rbrakk> \<Longrightarrow> x ub A"
   by (simp add:ub_def subsetD)

lemma ub_iso1:
  "\<lbrakk>x \<le> y; x ub A\<rbrakk> \<Longrightarrow> y ub A" 
   by(intro ubI; drule ubD, simp+) 

lemma ub_empty:
  "x ub {}"
  by (simp add: ub_def)

lemma ub_singleton:
  "x ub {x}"
  by (simp add: ub_def)

lemma ub_singletonI:
  "x ub {y} \<Longrightarrow> x \<ge> y"
  by (simp add: ubE)

lemma ub_singletonD:
  "x \<ge> y \<Longrightarrow> x ub {y}"
  by (simp add: ub_iso1 ub_singleton)

lemma ub_singleton_simp:
  "x ub {y} \<longleftrightarrow> x \<ge> y"
  by (simp add: ub_def)

lemma ub_insert:
  "\<lbrakk>c ub F; c \<ge> x\<rbrakk> \<Longrightarrow> c ub (insert x F)"
  by (simp add: ub_def)

lemma ub_binaryI:
  "a \<le> b \<Longrightarrow> b ub {a, b}"
  by (simp add: ub_insert ub_singleton)

lemma ub_binaryD:
  "b ub {a, b} \<Longrightarrow> a \<le> b"
  by (simp add: ubE)

lemma ub_binary_iff1:
  "a \<le> b \<longleftrightarrow> b ub {a, b}"
  by (simp add: ub_def)

lemma ub_doubleE1:
  "c ub {a, b} \<Longrightarrow> a \<le> c"
  by (simp add: ubD)

lemma ub_doubleE2:
  "c ub {a, b} \<Longrightarrow> b \<le> c"
  by (simp add: ubD)

lemma ub_doubleI:
  "\<lbrakk>a \<le> c; b \<le> c\<rbrakk> \<Longrightarrow> c ub {a, b}"
  by (simp add: ub_empty ub_insert)

lemma ub_double_iff1:
  "c ub {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by(auto, erule ub_doubleE1, erule ub_doubleE2, erule ub_doubleI, simp)

lemma ub_unionI:
  "\<lbrakk>x ub A; x ub B\<rbrakk> \<Longrightarrow> x ub A \<union> B"
  by (simp add: ub_def)

lemma ub_unionD1:
  "x ub A \<union> B \<Longrightarrow> x ub A"
  by (simp add: ub_def)

lemma ub_unionD2:
  "x ub A \<union> B \<Longrightarrow> x ub B"
  by (simp add: ub_def)

lemma ub_unI:
  "(\<And>A. A \<in> S \<Longrightarrow> x ub A) \<Longrightarrow> x ub (\<Union>S)"
  by (simp add: ub_iff1)

lemma ub_unD:
  "x ub (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x ub A"
 using ub_ant2[of A "\<Union>S" x] by blast

lemma ub_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<ge> f a) \<Longrightarrow> x ub (f`A)"
  by(simp add:ub_def image_p[of "A" "\<lambda>a. x \<ge> a" "f"])


subsection UpperBoundsSet

definition ubd::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "ubd X A \<equiv> {b \<in> X. b ub A}"

lemma ubdI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> b); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
   by(simp add: ubd_def ubI)

lemma ubdI2:
  "\<lbrakk>b ub A; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  by (simp add: ubdI ub_def) 

lemma ubdD1:
  "\<lbrakk>b \<in> ubd X A; x \<in> A\<rbrakk> \<Longrightarrow> x \<le> b"
  by (simp add: ubd_def ub_def)

lemma ubdD2:
  "b \<in> ubd X A \<Longrightarrow> b \<in> X"
  by (simp add: ubd_def)

lemma ubdD3:
  "b \<in> ubd X A \<Longrightarrow> b ub A"
  by (simp add: ubd_def)

lemma ubd_D31:
  "b \<in> ubd X A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> b)"
  by (simp add: ubdD1)

lemma ubd_mem_iff:
  "b \<in> ubd X A \<longleftrightarrow> (b \<in> X \<and> b ub A)" 
   by(simp add: ubd_def)

lemma ubd_mem_iff2:
  "b \<in> ubd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  a \<le> b))"
  by (simp add: ubd_mem_iff ub_def)

lemma ubd_mem_iff3:
  "b \<in> ubd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. a \<le> b))"
  by (simp add: ubd_mem_iff ub_iff1)

lemma ubd_sub:
  "ubd X A \<subseteq> X"
   by(simp add: ubd_def)

lemma ubd_ant1:
  "A \<subseteq> B \<Longrightarrow> ubd X B \<subseteq> ubd X A"
  by (simp add: ubd_mem_iff subset_iff ub_ant2) 

lemma ubd_ant1b:
  "\<lbrakk>A \<subseteq> B; b \<in> ubd X B\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  using ubd_ant1 by blast

lemma ubd_iso2:
  "Y \<subseteq> X \<Longrightarrow> ubd Y A \<subseteq> ubd X A" 
  by (simp add:subset_iff ubd_def)

lemma ubd_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> ubd Y A \<rbrakk> \<Longrightarrow> x \<in> ubd X A"
  by (simp add: ubd_mem_iff in_mono)

lemma ubd_emptyI:
  "x \<in> X \<Longrightarrow> x \<in> ubd X {}"
  by (simp add: ubd_mem_iff3)

lemma ubd_empty:
  "ubd X {} = X"
   by(simp add: set_eq_iff ubd_mem_iff ub_def)

lemma ubd_singleton:
  "x \<in> X \<Longrightarrow> x \<in> ubd X {x}"
  by (simp add: ubd_def ub_singleton)

lemma ubd_singleton2:
  "\<lbrakk>x \<in> X; y \<le> x \<rbrakk> \<Longrightarrow>  x \<in> ubd X {y}"
  by (simp add: ubd_mem_iff ub_iso1 ub_singleton)

lemma ubd_singleton_iff:
  "x \<in> ubd X {y} \<longleftrightarrow> (x \<in> X \<and> x \<ge> y)"
  by (simp add: ubd_mem_iff ub_singleton_simp)

lemma ubd_mem_insert:
  "\<lbrakk>c \<in> ubd X F; c \<ge> x\<rbrakk> \<Longrightarrow> c \<in> ubd X (insert x F)"
  by (simp add: ubd_mem_iff ub_insert)

lemma ubd_mem_binaryI:
  "\<lbrakk>a \<le> b; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd X {a, b}"
  by (simp add: ubdI2 ub_binaryI)

lemma ubd_mem_binaryD:
  "b \<in> ubd X {a, b} \<Longrightarrow> a \<le> b"
  by (simp add: ubdD1)

lemma ubd_mem_binary_iff1:
  "b \<in> ubd X {a, b} \<longleftrightarrow> a \<le> b \<and> b \<in> X"
  using ubdD2 ubd_mem_binaryD ubd_mem_binaryI by blast

lemma ubd_mem_doubleE1:
  "c \<in> ubd X {a, b} \<Longrightarrow> a \<le> c"
  by (simp add: ubdD1)

lemma ubd_mem_doubleE2:
  "c \<in> ubd X {a, b} \<Longrightarrow> b \<le> c"
  by (simp add: ubdD1)

lemma ubd_mem_doubleI:
  "\<lbrakk>a \<le> c; b \<le> c; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> ubd X {a, b}"
  by (simp add: ubd_empty ubd_mem_insert)

lemma ubd_mem_singleE:
  "x \<in> ubd X {a}\<Longrightarrow> a \<le> x"
  by (simp add: ubdD1)

lemma ubd_mem_binary:
  "b \<in> X \<Longrightarrow> a \<le> b \<longleftrightarrow> b \<in> ubd X {a, b}"
  by (simp add: ubd_mem_iff ub_binary_iff1)

lemma ubd_mem_double:
  "c \<in> X \<Longrightarrow> c \<in> ubd X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by (simp add: ubd_mem_iff ub_double_iff1)

lemma upbd_neE1:
  "ubd X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> a \<le> x)"
  using ubdD1 ubd_sub by blast

lemma upbd_neE3:
  "ubd X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. a \<le> x)"
  using upbd_neE1 by auto

lemma ubd_mem_unionI:
  "\<lbrakk>x \<in> ubd X A; x \<in> ubd X B\<rbrakk> \<Longrightarrow> x \<in> ubd X (A \<union> B)"
  by (simp add: ubd_mem_iff ub_unionI)

lemma ubd_mem_unionD1:
  " x \<in> ubd X (A \<union> B) \<Longrightarrow> x \<in> ubd X A "
  using ubd_ant1b[of A "A \<union> B" x X]  by blast

lemma ubd_mem_unionD2:
  " x \<in> ubd X (A \<union> B) \<Longrightarrow> x \<in> ubd X B "
  using ubd_ant1b[of B "A \<union> B" x X]  by blast

lemma ubd_unI:
  "x \<in> X \<Longrightarrow> (\<And>A. A \<in> S \<Longrightarrow> x \<in> ubd X A) \<Longrightarrow> x \<in> ubd X (\<Union>S)"
  by (simp add: ubd_mem_iff3)

lemma ubd_unD:
  "x \<in> X \<Longrightarrow> x \<in> ubd X (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x \<in> ubd X A"
  using ubd_ant1b[of A "\<Union>S" x X] by blast

lemma ubd_imageI:
  "x \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<ge> f a) \<Longrightarrow> x \<in> ubd X (f`A)"
  by (simp add: ub_imageI ubdI2)

lemma ubd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x ub A \<Longrightarrow> x ub B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x ub B \<Longrightarrow> x ub A) \<Longrightarrow> ubd X A = ubd X B"
  by(auto simp add:set_eq_iff ubd_mem_iff)

lemma ubd_double1:
  " a \<le> b \<Longrightarrow>  ubd X {a, b} \<subseteq> ubd X {b}"
  by (simp add: ubd_ant1)

lemma ubd_double1b:
  " a \<le> b \<Longrightarrow> x \<in> ubd X {a, b} \<Longrightarrow> x \<in> ubd X {b}"
  by (simp add: ubd_mem_iff2)

lemma ubd_double2:
  " a \<le> b \<Longrightarrow>  ubd X {b} \<subseteq> ubd X {a, b}"
  by (meson dual_order.trans subset_iff ubd_mem_insert ubd_mem_singleE)

lemma ubd_double2b:
  " a \<le> b \<Longrightarrow> x \<in> ubd X {b} \<Longrightarrow> x \<in> ubd X {a, b}"
  using ubd_double2 by fastforce

lemma ubd_double3:
  "a \<le> b \<Longrightarrow> ubd X {a, b} = ubd X {b}"
  by (simp add: subset_antisym ubd_double1 ubd_double2)


subsection LowerBoundsPredicate

definition lb::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "lb" 50) where 
   "x lb  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<ge> x)"


lemma lb_iff1:
  "x lb A \<longleftrightarrow> (\<forall>a \<in> A. a \<ge> x)"
  by(auto simp add:lb_def)

lemma lbI:
  "(\<And>a. a \<in> A \<Longrightarrow> a \<ge> x) \<Longrightarrow> x lb A" 
  by (simp add: lb_def)

lemma lbD:
  "\<lbrakk>x lb A; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> x"
  by (simp add: lb_def)

lemma lbE:
  "x lb A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<ge> x)"
  by (simp add: lbD)

lemma lb_ant2:
  "\<lbrakk>A \<subseteq> B; x lb B\<rbrakk> \<Longrightarrow> x lb A"
   by (simp add:lb_def subsetD)

lemma lb_iso1:
  "\<lbrakk>y \<le> x; x lb A\<rbrakk> \<Longrightarrow> y lb A" 
   apply(intro lbI; drule lbD) 
   by(simp)+

lemma lb_empty:
  "x lb {}"
  by (simp add: lb_def)

lemma lb_singleton:
  "x lb {x}"
  by (simp add: lb_def)

lemma lb_singletonI:
  "x lb {y} \<Longrightarrow> x \<le> y"
  by (simp add: lbE)

lemma lb_singletonD:
  "x \<le> y \<Longrightarrow> x lb {y}"
  by (simp add: lb_iso1 lb_singleton)

lemma lb_insert:
  "\<lbrakk>c lb F; c \<le> x\<rbrakk> \<Longrightarrow> c lb (insert x F)"
  by (simp add: lb_def)

lemma lb_binaryI:
  "a \<ge> b \<Longrightarrow> b lb {a, b}"
  by (simp add: lb_insert lb_singleton)

lemma lb_binaryD:
  "b lb {a, b} \<Longrightarrow> a \<ge> b"
  by (simp add: lbE)

lemma lb_binary_iff1:
  "a \<ge> b \<longleftrightarrow> b lb {a, b}"
  by (simp add: lb_def)

lemma lb_doubleE1:
  "c lb {a, b} \<Longrightarrow> a \<ge> c"
  by (simp add: lbD)

lemma lb_doubleE2:
  "c lb {a, b} \<Longrightarrow> b \<ge> c"
  by (simp add: lbD)

lemma lb_doubleI:
  "\<lbrakk>a \<ge> c; b \<ge> c\<rbrakk> \<Longrightarrow> c lb {a, b}"
  by (simp add: lb_empty lb_insert)

lemma lb_double_iff1:
  "c lb {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b"
  using lb_doubleE1 lb_doubleE2 lb_doubleI by blast

lemma lb_unionI:
  "\<lbrakk>x lb A; x lb B\<rbrakk> \<Longrightarrow> x lb A \<union> B"
  by (simp add: lb_def)

lemma lb_unionD1:
  "x lb A \<union> B \<Longrightarrow> x lb A"
  by (simp add: lb_def)

lemma lb_unionD2:
  "x lb A \<union> B \<Longrightarrow> x lb B"
  by (simp add: lb_def)

lemma lb_unI:
  "(\<And>A. A \<in> S \<Longrightarrow> x lb A) \<Longrightarrow> x lb (\<Union>S)"
  by (simp add: lb_iff1)

lemma lb_unD:
  "x lb (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x lb A"
 using lb_ant2[of A "\<Union>S" x] by blast

lemma lb_singleton_simp:
  "x lb {y} \<longleftrightarrow> x \<le> y"
  by (simp add: lb_def)

lemma lb_binary:
  "a \<le> b \<longleftrightarrow> a lb {a, b}"
  by (simp add: lb_def)

lemma lb_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<le> f a) \<Longrightarrow> x lb (f`A)"
  by(simp add:lb_def image_p[of "A" "\<lambda>a. x \<le> a" "f"])


subsection LowerBoundsSet
definition lbd::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "lbd X A \<equiv> {b \<in> X. b lb A}"

lemma lbdI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<ge> b); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> lbd X A"
   by(simp add: lbd_def lbI)

lemma lbdI2:
  "\<lbrakk>b lb A; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> lbd X A"
  by (simp add: lbdI lb_def) 

lemma lbdD1:
  "\<lbrakk>b \<in> lbd X A; x \<in> A\<rbrakk> \<Longrightarrow> x \<ge> b"
  by (simp add: lbd_def lb_def)

lemma lbdD2:
  "b \<in> lbd X A \<Longrightarrow> b \<in> X"
  by (simp add: lbd_def)

lemma lbdD3:
  "b \<in> lbd X A \<Longrightarrow> b lb A"
  by (simp add: lbd_def)

lemma lbd_D31:
  "b \<in> lbd X A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<ge> b)"
  by (simp add: lbdD1)

lemma lbd_mem_iff:
  "b \<in> lbd X A \<longleftrightarrow> (b \<in> X \<and> b lb A)" 
   by(simp add: lbd_def)

lemma lbd_mem_iff2:
  "b \<in> lbd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  a \<ge> b))"
  by (simp add: lbd_mem_iff lb_def)

lemma lbd_mem_iff3:
  "b \<in> lbd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. a \<ge> b))"
  by (simp add: lbd_mem_iff lb_iff1)

lemma lbd_sub:
  "lbd X A \<subseteq> X"
   by(simp add: lbd_def)

lemma lbd_ant1:
  "A \<subseteq> B \<Longrightarrow> lbd X B \<subseteq> lbd X A"
  by (simp add: lbd_mem_iff lb_ant2 subset_iff) 

lemma lbd_ant1b:
  "\<lbrakk>A \<subseteq> B; b \<in> lbd X B\<rbrakk> \<Longrightarrow> b \<in> lbd X A"
  using lbd_ant1 by blast

lemma lbd_iso2:
  "Y \<subseteq> X \<Longrightarrow> lbd Y A \<subseteq> lbd X A" 
  by (simp add:subset_iff lbd_def)

lemma lbd_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> lbd Y A \<rbrakk> \<Longrightarrow> x \<in> lbd X A"
  by (simp add: lbd_mem_iff in_mono)

lemma lbd_emptyI:
  "x \<in> X \<Longrightarrow> x \<in> lbd X {}"
  by (simp add: lbd_mem_iff3)

lemma lbd_empty:
  "lbd X {} = X"
   by(simp add: set_eq_iff lbd_mem_iff lb_def)

lemma lbd_singleton:
  "x \<in> X \<Longrightarrow> x \<in> lbd X {x}"
  by (simp add: lbd_def lb_singleton)

lemma lbd_singleton2:
  "\<lbrakk>x \<in> X; x \<le> y \<rbrakk> \<Longrightarrow>  x \<in> lbd X {y}"
  by (simp add: lbd_mem_iff lb_iso1 lb_singleton)

lemma lbd_singleton_iff:
  "x \<in> lbd X {y} \<longleftrightarrow> (x \<in> X \<and> x \<le> y)"
  by (simp add: lbd_mem_iff lb_singleton_simp)

lemma lbd_mem_insert:
  "\<lbrakk>c \<in> lbd X F; c \<le> x\<rbrakk> \<Longrightarrow> c \<in> lbd X (insert x F)"
  by (simp add: lbd_mem_iff lb_insert)

lemma lbd_mem_binaryI:
  "\<lbrakk>b \<le> a; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> lbd X {a, b}"
  by (simp add: lbdI2 lb_binaryI)

lemma lbd_mem_binaryD:
  "b \<in> lbd X {a, b} \<Longrightarrow> a \<ge> b"
  by (simp add: lbdD1)

lemma lbd_mem_binary_iff1:
  "b \<in> lbd X {a, b} \<longleftrightarrow> a \<ge> b \<and> b \<in> X"
  using lbdD2 lbd_mem_binaryD lbd_mem_binaryI by blast

lemma lbd_mem_doubleE1:
  "c \<in> lbd X {a, b} \<Longrightarrow> a \<ge> c"
  by (simp add: lbdD1)

lemma lbd_mem_doubleE2:
  "c \<in> lbd X {a, b} \<Longrightarrow> b \<ge> c"
  by (simp add: lbdD1)

lemma lbd_mem_doubleI:
  "\<lbrakk>a \<ge> c; b \<ge> c; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> lbd X {a, b}"
  by (simp add: lbd_empty lbd_mem_insert)

lemma lbd_mem_singleE:
  "x \<in> lbd X {a}\<Longrightarrow> a \<ge> x"
  by (simp add: lbdD1)

lemma lbd_mem_binary:
  "b \<in> X \<Longrightarrow> a \<ge> b \<longleftrightarrow> b \<in> lbd X {a, b}"
  by (simp add: lbd_mem_iff lb_binary_iff1)

lemma lbd_mem_double:
  "c \<in> X \<Longrightarrow> c \<in> lbd X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b"
  by (simp add: lbd_mem_iff lb_double_iff1)

lemma lpbd_neE1:
  "lbd X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> a \<ge> x)"
  using lbdD1 lbd_sub by blast

lemma lpbd_neE3:
  "lbd X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. a \<ge> x)"
  using lpbd_neE1 by auto

lemma lbd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x lb A \<Longrightarrow> x lb B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x lb B \<Longrightarrow> x lb A) \<Longrightarrow> lbd X A = lbd X B"
  by(auto simp add:set_eq_iff lbd_mem_iff)

lemma lbd_mem_unionI:
  "\<lbrakk>x \<in> lbd X A; x \<in> lbd X B\<rbrakk> \<Longrightarrow> x \<in> lbd X (A \<union> B)"
  by (simp add: lbd_mem_iff lb_unionI)

lemma lbd_mem_unionD1:
  " x \<in> lbd X (A \<union> B) \<Longrightarrow> x \<in> lbd X A "
  using lbd_ant1b[of A "A \<union> B" x X]  by blast

lemma lbd_mem_unionD2:
  " x \<in> lbd X (A \<union> B) \<Longrightarrow> x \<in> lbd X B "
  using lbd_ant1b[of B "A \<union> B" x X]  by blast

lemma lbd_unI:
  "x \<in> X \<Longrightarrow> (\<And>A. A \<in> S \<Longrightarrow> x \<in> lbd X A) \<Longrightarrow> x \<in> lbd X (\<Union>S)"
  by (simp add: lbd_mem_iff3)

lemma lbd_unD:
  "x \<in> X \<Longrightarrow> x \<in> lbd X (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x \<in> lbd X A"
  using lbd_ant1b[of A "\<Union>S" x X] by blast

lemma lbd_imageI:
  "x \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> f a) \<Longrightarrow> x \<in> lbd X (f`A)"
  by (simp add: lb_imageI lbdI2)

lemma lbd_double1:
  "a \<ge> b \<Longrightarrow>  lbd X {a, b} \<subseteq> lbd X {b}"
  by (simp add: lbd_ant1)

lemma lbd_double1b:
  "a \<ge> b \<Longrightarrow> x \<in> lbd X {a, b} \<Longrightarrow> x \<in> lbd X {b}"
  by (simp add: lbd_mem_iff2)

lemma lbd_double2:
  "a \<ge> b \<Longrightarrow> lbd X {b} \<subseteq> lbd X {a, b}"
  by (meson dual_order.trans subset_iff lbd_mem_insert lbd_mem_singleE)

lemma lbd_double2b:
  "a \<ge> b \<Longrightarrow> x \<in> lbd X {b} \<Longrightarrow> x \<in> lbd X {a, b}"
  using lbd_double2 by fastforce

lemma lbd_double3:
  "a \<ge> b \<Longrightarrow> lbd X {a, b} = lbd X {b}"
  by (simp add: subset_antisym lbd_double1 lbd_double2)

subsection Composition

lemma lubd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> lbd X (ubd X A)"
  by (simp add: lbdI ubdD1 subset_iff) 

lemma lubd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A"
  by (simp add: lbdI ubdD1 subset_iff) 

lemma ulbd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ubd X (lbd X A)"
  by (simp add: lbdD1 ubdI subset_iff)

lemma ulbd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A"
  by (simp add: ubdI lbdD1 subset_iff) 

lemma lubd_comp2:
  "A \<subseteq> B \<Longrightarrow> lbd X (ubd X A) \<subseteq> lbd X (ubd X B)"
  by (simp add: lbd_ant1 ubd_ant1)

lemma lubd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A  \<subseteq> ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) B"
  by (simp add: lbd_ant1 ubd_ant1)

lemma ulbd_comp2:
  "A \<subseteq> B  \<Longrightarrow> ubd X (lbd X A) \<subseteq> ubd X (lbd X B)"
  by (simp add: lbd_ant1 ubd_ant1)

lemma ulbd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A  \<subseteq> ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) B"
  by (simp add: lbd_ant1 ubd_ant1)

lemma lubd_comp3:
  "lbd X (ubd X A) = lbd X (ubd X (lbd X (ubd X A)))"
  by (simp add: lbd_ant1 lbd_sub lubd_comp1 subset_antisym ubd_sub ulbd_comp1)

lemma lubd_comp3b:
  " ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A  = ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A"
  by (simp add: lbd_ant1 lbd_sub lubd_comp1 subset_antisym ubd_sub ulbd_comp1)

lemma ulbd_comp3:
  "ubd X (lbd X A) = ubd X (lbd X (ubd X (lbd X A)))"
  by (simp add: lbd_sub lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1)

lemma ulbd_comp3b:
  "((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A  = ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A"
  by (simp add: ubd_ant1 lbd_sub ulbd_comp1 subset_antisym ubd_sub lubd_comp1)


section AbsoluteExtrema
subsection GreatestPredicate
definition is_greatest::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_greatest A m \<equiv> m \<in> ubd A A"

lemma greatestI1:
  "m \<in> ubd A A \<Longrightarrow> is_greatest A m" 
  by (simp add: is_greatest_def)

lemma greatestI2:
  "\<lbrakk>m ub A; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> m); m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: ubI greatestI2)

lemma greatestI4:
  "\<lbrakk>m \<in> ubd X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: ubdD3 greatestI2)

lemma greatestD1:
  "is_greatest A m \<Longrightarrow> (m \<in> A \<and> m ub A)"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestD11:
  "is_greatest A m \<Longrightarrow> m \<in> A"
  by (simp add: greatestD1)

lemma greatestD12:
  "is_greatest A m \<Longrightarrow> m ub A"
  by (simp add: greatestD1)

lemma greatestD2:
  "\<lbrakk>is_greatest A m; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> m " 
  by (simp add: ubD[of "m" "A" "a"] greatestD1[of "A" "m"])

lemma greatest_iff:
  "is_greatest A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m))"
  by (simp add: ubd_mem_iff is_greatest_def ub_def)

lemma greatest_unique:
  "is_greatest A m1 \<Longrightarrow> is_greatest A m2 \<Longrightarrow> m1 =m2"
  by (simp add: greatest_iff order_antisym)

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest A ma \<Longrightarrow> is_greatest B mb \<Longrightarrow> ma \<le> mb"
  using greatestD11 greatestD2 by blast

lemma greatest_singleton:
  "is_greatest {x} x"
  by (simp add: greatestI2 ub_singleton)

lemma singleton_ex_greatest:
  "\<exists>m. is_greatest {x} m"
  using greatest_singleton by blast

lemma greatest_insert1:
  "x ub A \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatestI2 ub_insert)

lemma greatest_insert2:
  "is_greatest A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_greatest (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma greatest_insert3:
  "is_greatest A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatest_insert1 greatestD12 ub_iso1)

lemma greatest_insert5:
  "is_greatest A m \<Longrightarrow> m < x \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatest_insert3)

lemma greatest_finite_linear:
  assumes A0:"finite A" and A1:"A \<noteq> {}" and A3:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (a \<le> b) \<or> (b \<le> a))"
  shows "\<exists>m. is_greatest A m"
  by (metis A0 A1 A3 finite_has_maximal greatestI3)

subsection GreatestOperator

definition Greatest::"'a::order set \<Rightarrow> 'a::order" where
  "Greatest A \<equiv> (THE m. is_greatest A m)"

lemma greatest_equality:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> m); m \<in> A\<rbrakk> \<Longrightarrow> Greatest A = m"
  by (simp add: Greatest_def greatestI3 greatest_unique the_equality) 

lemma greatest_equality2:
  "is_greatest A m \<Longrightarrow> Greatest A = m"
  by (simp add: greatest_equality greatest_iff)

lemma greatest_equality3:
  "m \<in> ubd A A \<Longrightarrow> Greatest A = m"
  by (simp add: greatest_equality2 is_greatest_def)

lemma lb_single_greatest1:
  "x \<in> X \<Longrightarrow> is_greatest (lbd X {x}) x"
  by (simp add: greatest_iff lbd_singleton_iff)

lemma lb_single_greatest2:
  "x \<in> X \<Longrightarrow> Greatest (lbd X {x}) = x"
  by (simp add: greatest_equality2 lb_single_greatest1)

lemma greatest_exD0:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> A \<noteq> {}"
  using greatestD1 by auto

lemma greatest_exD1:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> Greatest A \<in> A"
  using greatestD11 greatest_equality2 by auto

lemma greatest_exD2:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> (Greatest A))"
  using greatestD2 greatest_equality2 by blast

lemma greatest_exD3:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> (Greatest A) \<in> ubd A A"
  using greatest_equality2 is_greatest_def by blast

lemma greatest_exD4:
  "(\<exists>m. is_greatest A m) \<Longrightarrow>  Greatest A ub A"
  using greatestD1 greatest_equality2 by blast

lemma greatest_exD5:
  "\<lbrakk>A \<subseteq> B; (\<exists>m. is_greatest A m); (\<exists>m. is_greatest B m)\<rbrakk> \<Longrightarrow> Greatest A \<le> Greatest B"
  using greatest_equality2 is_greatest_iso2 by blast

lemma greatest_singleton2:
  "Greatest {x} = x"
  by (simp add: greatest_equality2 greatest_singleton)

lemma greatest_insert1b:
  "x ub A \<Longrightarrow> Greatest (insert x A) = x"
  by (simp add: greatest_equality2 greatest_insert1)

lemma greatest_insert2b:
  "is_greatest A m \<Longrightarrow> x \<le> m \<Longrightarrow> Greatest (insert x A) = m"
  by (simp add: greatest_equality2 greatest_insert2)

lemma greatest_insert3b:
  "is_greatest A m \<Longrightarrow> m \<le> x \<Longrightarrow> Greatest (insert x A) =  x"
  by (simp add: greatest_equality2 greatest_insert3)

lemma greatest_insert4b:
  "is_greatest A m \<Longrightarrow> x < m \<Longrightarrow> Greatest (insert x A) = m"
  by (simp add: greatest_insert2b)

lemma greatest_insert5b:
  "is_greatest A m \<Longrightarrow> m < x \<Longrightarrow> Greatest (insert x A) = x"
  by (simp add: greatest_insert3b)

lemma greatest_ub:
  "is_greatest A m \<Longrightarrow> ubd A A = {m}"
  by(rule order_antisym, auto intro: greatestI1 greatest_unique, simp add: is_greatest_def)

subsection LeastPredicate

definition is_least::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_least A m \<equiv> m \<in> lbd A A"

lemma leastI1:
  "m \<in> lbd A A \<Longrightarrow> is_least A m" 
  by (simp add: is_least_def)

lemma leastI2:
  "\<lbrakk>m lb A; m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: lbd_mem_iff is_least_def)

lemma leastI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> m \<le> a); m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: lbI leastI2)

lemma leastI4:
  "\<lbrakk>m \<in> lbd X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: lbdD3 leastI2)

lemma leastD1:
  "is_least A m \<Longrightarrow> (m \<in> A \<and> m lb A)"
  by (simp add: lbd_mem_iff is_least_def)

lemma leastD11:
  "is_least A m \<Longrightarrow> m \<in> A"
  by (simp add: leastD1)

lemma leastD12:
  "is_least A m \<Longrightarrow> m lb A"
  by (simp add: leastD1)

lemma leastD2:
  "\<lbrakk>is_least A m; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> m " 
  by (simp add: lbD[of "m" "A" "a"] leastD1[of "A" "m"])

lemma least_iff:
  "is_least A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<ge>  m))"
  by (simp add: lbd_mem_iff is_least_def lb_def)

lemma least_unique:
  "is_least A m1 \<Longrightarrow> is_least A m2 \<Longrightarrow> m1 =m2"
  by (simp add: least_iff order_antisym)

lemma is_least_iso2:
  "A \<subseteq> B \<Longrightarrow> is_least A ma \<Longrightarrow> is_least B mb \<Longrightarrow> ma \<ge> mb"
  using leastD11 leastD2 by blast

lemma least_ne:
  "is_least A m \<Longrightarrow> A \<noteq> {}"
  using leastD11 by auto

lemma least_singleton:
  "is_least {x} x"
  by (simp add: lb_singleton leastI2)

lemma singleton_ex_least:
  "\<exists>m. is_least {x} m"
  using least_singleton by blast

lemma least_pair:
  "is_least {a, b} a \<longleftrightarrow> a \<le> b"
  by (simp add: least_iff)

lemma least_insert1:
  "x lb A \<Longrightarrow> is_least (insert x A) x"
  by (simp add: leastI2 lb_insert)

lemma least_insert2:
  "is_least A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_least (insert x A) m"
  by (simp add: leastD11 leastI2 leastD12 lb_insert)

lemma least_insert3:
  "is_least A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_least (insert x A) x"
  by (simp add: lb_iso1 leastD1 least_insert1)

lemma least_insert4:
  "is_least A m \<Longrightarrow> m < x \<Longrightarrow> is_least (insert x A) m"
  by (simp add: least_insert2)

lemma least_finite_linear:
  assumes A0:"finite A" and A1:"A \<noteq> {}" and A3:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (a \<le> b) \<or> (b \<le> a))"
  shows "\<exists>m. is_least A m"
  by (metis A0 A1 A3 finite_has_minimal least_iff)

subsection LeastOperator

definition Least::"'a::order set \<Rightarrow> 'a::order" where
  "Least A \<equiv> (THE m. is_least A m)"

lemma least_equality:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<ge> m); m \<in> A\<rbrakk> \<Longrightarrow> Least A = m"
  by (simp add: Least_def leastI3 least_unique the_equality)

lemma least_equality2:
  "is_least A m \<Longrightarrow> Least A = m"
  by (simp add: Least_def least_unique the_equality) 

lemma least_equality3:
  "m \<in> lbd A A \<Longrightarrow> Least A = m"
  by (simp add: least_equality2 is_least_def)

lemma ub_single_least1:
  "x \<in> X \<Longrightarrow> is_least (ubd X {x}) x"
  by (simp add: ubdD1 ubd_singleton least_iff)

lemma ub_single_least2:
  "x \<in> X \<Longrightarrow> Least (ubd X {x}) = x"
  by (simp add: least_equality2 ub_single_least1)

lemma least_exD0:
  "(\<exists>m. is_least A m) \<Longrightarrow> A \<noteq> {}"
  using leastD1 least_equality2 by blast

lemma least_exD1:
  "(\<exists>m. is_least A m) \<Longrightarrow> Least A \<in> A"
  using leastD1 least_equality2 by blast

lemma least_exD2:
  "(\<exists>m. is_least A m) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (Least A) \<le> a)"
  using leastD2 least_equality2 by blast

lemma least_exD3:
  "(\<exists>m. is_least A m) \<Longrightarrow> (Least A) \<in> lbd A A"
  using is_least_def least_equality2 by auto

lemma least_exD4:
  "(\<exists>m. is_least A m) \<Longrightarrow>  Least A lb A"
  using leastD1 least_equality2 by blast

lemma least_exD5:
  "\<lbrakk>A \<subseteq> B; (\<exists>m. is_least A m); (\<exists>m. is_least B m)\<rbrakk> \<Longrightarrow> Least B \<le> Least A"
  using is_least_iso2 least_equality2 by blast

lemma least_singleton2:
  "Least {x} = x"
  by (simp add: least_equality2 least_singleton)

lemma least_insert1b:
  "x lb A \<Longrightarrow> Least (insert x A) =  x"
  by (simp add: least_equality2 least_insert1)

lemma least_insert2b:
  "is_least A m \<Longrightarrow> m \<le> x \<Longrightarrow> Least (insert x A) = m"
  by (simp add: least_equality2 least_insert2)

lemma least_insert3b:
  "is_least A m \<Longrightarrow> x \<le> m \<Longrightarrow> Least (insert x A) = x"
  by (simp add: least_equality2 least_insert3)

lemma least_insert4b:
  "is_least A m \<Longrightarrow> m < x \<Longrightarrow> Least (insert x A) =  m"
  by (simp add: least_insert2b)

lemma least_insert5b:
  "is_least A m \<Longrightarrow> x < m \<Longrightarrow> Least (insert x A) = x"
  by (simp add: least_insert3b)

lemma least_lb:
  "is_least A m \<Longrightarrow> lbd A A = {m}"
  by(rule order_antisym, auto intro: leastI1 least_unique, simp add: is_least_def)

section Extrema
subsection Suprema

definition is_sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_sup X A x \<equiv> (is_least (ubd X A) x)"

lemma is_supI1:
  "is_least (ubd X A) x \<Longrightarrow> is_sup X A x"
  by (simp add: is_sup_def) 

lemma is_supD1:
  "is_sup X A x \<Longrightarrow> (is_least (ubd X A) x)"
  by (simp add: is_sup_def)

lemma is_supI2:
  "x \<in> lbd (ubd X A) (ubd X A) \<Longrightarrow> is_sup X A x"
  using is_least_def is_supI1 by blast

lemma is_supD2:
  "is_sup X A x \<Longrightarrow> x \<in> lbd (ubd X A) (ubd X A)"
  using is_least_def is_supD1 by blast

lemma is_supI3:
  "\<lbrakk>x lb (ubd X A); x \<in> (ubd X A)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI1 leastI2)

lemma is_supD31:
  "is_sup X A x \<Longrightarrow> x lb (ubd X A)"
  by (simp add: is_sup_def leastD12)

lemma is_supD32:
  "is_sup X A x \<Longrightarrow> x \<in>  (ubd X A)"
  by (simp add: is_supD1 leastD1)

lemma is_supI4:
  "\<lbrakk>x lb (ubd X A); x \<in> X; x ub A\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: ubd_mem_iff leastI2 is_supI1)

lemma is_supE1:
  "is_sup X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_supD32[of "X" "A" "x"] ubdD2[of "x" "X" "A"])

lemma is_supI5:
  "\<lbrakk>(\<And>a. a \<in> (ubd X A) \<Longrightarrow> x \<le> a); x \<in> (ubd X A)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI1 leastI3)

lemma is_supI6:
  "\<lbrakk>x \<in> X; x ub A; (\<And>a. a \<in> (ubd X A) \<Longrightarrow> x \<le> a)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI5 ubdI2)

lemma is_supI7:
  "\<lbrakk>x \<in> X; x ub A; (\<And>a. a \<in> X \<Longrightarrow> a ub A \<Longrightarrow>  x \<le> a)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI4 lb_def ubd_mem_iff)

lemma is_supI8:
  "\<lbrakk>x \<in> X; (\<And>z. z \<in> ubd X A \<longleftrightarrow> z \<ge> x)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI1 least_iff)

lemma is_supI9:
  "\<lbrakk>x \<in> X; (\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A))\<rbrakk> \<Longrightarrow> is_sup X A x"
  using is_supI7 by blast

lemma is_supE2:
  "is_sup X A x \<Longrightarrow> x ub A" 
  by(simp add: ubdD3[of "x" "X" "A"] is_supD32[of "X" "A" "x"])            

lemma is_supE3:
  "\<lbrakk> is_sup X A x; y \<in> ubd X A\<rbrakk> \<Longrightarrow> x \<le> y "
  by (simp add: is_sup_def leastD2)
                     
lemma is_supE4:
  "\<lbrakk>is_sup X A x; y \<in> X; y ub A\<rbrakk> \<Longrightarrow> x \<le> y "
  by (simp add: ubd_mem_iff is_supE3)
        
lemma is_supE5:
  "\<lbrakk>is_sup X A x; z \<in> X;  x \<le> z\<rbrakk> \<Longrightarrow> z \<in> ubd X A"
  by (simp add: is_supE2 ub_iso1 ubdI2)

lemma is_supD1121:
  "\<lbrakk>is_sup X A x; a \<in> A \<rbrakk> \<Longrightarrow> a \<le> x"
  using is_supE2 ubE by blast

lemma is_supE6:
  "\<lbrakk>is_sup X A x;  x \<le> z\<rbrakk> \<Longrightarrow> z ub A"
  by (simp add: is_supE2 ub_iso1)

lemma is_supE7:
  "\<lbrakk>is_sup X A x;  x \<le> z; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> z"
  by (simp add: is_supE6[of "X" "A" "x" "z"] ubD[of "z" "A" "a"])

lemma is_supD41:
  "is_sup X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> z \<ge> x \<Longrightarrow> z ub A)"
  by (simp add: is_supE6)

lemma is_supD42:
  "is_sup X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  z ub A \<Longrightarrow> z \<ge> x)"
  by (simp add: is_supE4)

lemma is_supD5:
  "is_sup X A x \<Longrightarrow> (\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A))"
  using is_supE4 is_supE6 by blast
   
lemma is_sup_iff1:
  "\<lbrakk>x \<in> X; A \<subseteq> X\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A)) \<longleftrightarrow> is_sup X A x)"
  by (meson is_supD5 is_supI9)
   
lemma sup_iff2:
  "is_sup X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  s \<le> z \<longleftrightarrow> z \<in> ubd X A)"
  by (meson dual_order.refl is_supE1 is_supE3 is_supE5 is_supI5 ubdD2)

lemma is_sup_unique:
  "is_sup X A m1 \<Longrightarrow> is_sup X A m2 \<Longrightarrow> m1 = m2"
  using is_supD1 least_unique by blast

lemma is_sup_iso1:
  "A \<subseteq> B \<Longrightarrow> is_sup X A ma \<Longrightarrow> is_sup X B mb \<Longrightarrow> ma \<le> mb "
  by (simp add: is_supE1 is_supE2 is_supE4 ub_ant2)

lemma is_sup_iso2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_sup Y A my \<Longrightarrow> is_sup X A mx \<Longrightarrow> mx \<le> my"
  by (simp add: in_mono is_supD42 is_supE1 is_supE2)

lemma sup_maxI1:
  "is_sup X A x \<Longrightarrow> x \<in> A \<Longrightarrow> (is_greatest A x)"
  by (simp add: greatestI2 is_supE2)

lemma sup_maxE1:
  "(is_greatest A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_sup X A x"
  by (simp add: greatestD11 greatestD12 is_supI6 ubdD1)

lemma sup_maxE2:
  "(is_greatest A x) \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup X A x"
  using greatestD11 sup_maxE1 by blast

lemma sup_max_eq:
  "A \<subseteq> X \<Longrightarrow> (is_sup X A x \<and> x \<in> A) \<longleftrightarrow> (is_greatest A x)"
  using greatestD11 sup_maxE2 sup_maxI1 by blast

lemma sup_max_eq2:
  "(is_sup A A x) \<longleftrightarrow> (is_greatest A x)"
  using greatestD11 is_supE1 sup_maxE1 sup_maxI1 by blast

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup B A s"
  by(simp add:in_mono sup_iff2 ubd_mem_iff)

lemma sup_singleton:
  "s \<in> X \<Longrightarrow> is_sup X {s} s"
  by (simp add: is_supI1 ub_single_least1)

lemma sup_emptyI:
  "is_least X i \<Longrightarrow> is_sup X {} i"
  by (simp add: is_sup_def ubd_empty)

lemma sup_emptyD:
  "is_sup X {} i \<Longrightarrow> is_least X i "
  by (simp add: is_sup_def ubd_empty)

lemma sup_empty:
  "is_sup X {} i \<longleftrightarrow> (is_least X i)"
  by (simp add: ubd_empty is_sup_def)

lemma binary_supI1:
  "\<lbrakk>a \<in> X; b \<in> X; a \<le> b\<rbrakk> \<Longrightarrow> is_sup X {a, b} b"
  by (simp add: greatest_insert2 greatest_singleton sup_maxE1)

lemma binary_supI2:
  "\<lbrakk>a \<in> X; b \<in> X; b \<le> a\<rbrakk> \<Longrightarrow> is_sup X {a, b} a"
  by (simp add: greatest_insert1 sup_maxE1 ub_singleton_simp)

lemma binary_supD21:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup X {a, b} s; c \<le> a\<rbrakk> \<Longrightarrow>  c \<le> s"
  using is_supD1121 by fastforce

lemma binary_supD22:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup X {a, b} s; c \<le> b\<rbrakk> \<Longrightarrow>  c \<le> s"
  by (simp add: binary_supD21 insert_commute)

lemma binary_supD31:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow>  a \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD32:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow>  b \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD4:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow> (s \<le> c \<longleftrightarrow> a \<le> c \<and> b \<le> c)"
  by (simp add: sup_iff2 ubd_mem_double)

lemma sup_insert1:
  "\<lbrakk>x ub A; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (simp add: greatest_insert1 sup_maxE1)

lemma sup_insert2:
  "\<lbrakk>is_sup X A m;  x \<le> m\<rbrakk> \<Longrightarrow> is_sup X (insert x A) m"
  by (meson is_supE1 is_supE2 is_supE4 is_supI9 subset_insertI ub_ant2 ub_insert ub_iso1)

lemma sup_insert3:
  "\<lbrakk>is_sup X A m; m \<le> x; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (simp add: is_supD41 sup_insert1)

lemma sup_insert61:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 ub A"
  by (simp add: is_supD1121 is_supE6)

lemma sup_insert62:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> ubd X A"
  by (simp add: is_supE1 sup_insert61 ubd_mem_iff)

lemma sup_insert7:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2; u \<in> ubd X (insert x A)\<rbrakk> \<Longrightarrow>  s2 \<le> u"
  by (simp add: ubd_mem_iff2 is_supE3)

lemma ub_eq_sup_eq:
  "(\<And>x. x ub A \<longleftrightarrow> x ub B) \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: ubd_mem_iff sup_iff2)

lemma Upper_eq_sup_eq:
  "ubd X A = ubd X B \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: is_sup_def)

definition Sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Sup X A \<equiv> (THE m. is_sup X A m)"

lemma sup_equality:
  "is_sup X A m \<Longrightarrow> Sup X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

lemma sup_exI:
  "\<exists>s. is_sup X A s \<Longrightarrow> (\<And>s. is_sup X A s \<Longrightarrow> P s) \<Longrightarrow> P (Sup X A)"
  using sup_equality by auto

lemma sup_unc:
  "\<lbrakk>is_sup X (A \<union> B) s; is_sup X A s1; is_sup X B s2; is_sup X {s1, s2} s3\<rbrakk> \<Longrightarrow> s=s3"
  by (metis binary_supD4 is_supD42 is_supE6 order_class.order_eq_iff sup_iff2 ub_unionD1 ub_unionD2 ub_unionI)

lemma sup_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub Sup X ` A \<Longrightarrow> x ub \<Union> A"
  by (metis imageI is_supD5 sup_equality ub_def ub_unI)

lemma sup_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub \<Union> A \<Longrightarrow>  x ub Sup X ` A"
  by (metis is_supD5 sup_equality ub_imageI ub_unD)

lemma sup_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow>(is_sup X ((\<lambda>Ai. Sup X Ai)`A) s) \<longleftrightarrow> (is_sup X (\<Union>A) s)"
  apply(rule Upper_eq_sup_eq, rule ubd_eqI1)  using sup_families1 apply blast using sup_families2 by blast


lemma bsup_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_sup X {a1, a2} (Sup X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows "is_sup X A (Sup X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"is_sup X F s1"
    using insert.hyps(4) insert.prems by blast
  have B1:"s1 \<in> X"
    using B0 is_supE1 by blast
  obtain s2 where B2:"is_sup X {s1, x} s2"
    using A0 B1 insert.prems by auto
  have B3:"s2 \<in> ubd X (insert x F)"
    by (meson B0 B2 insertI2 is_supD1121 singleton_iff sup_insert62 ubd_mem_insert)
  have B4:"\<And>u. u \<in> ubd X (insert x F) \<longrightarrow> s2 \<le> u"
    using B0 B2 sup_insert7 by blast
  have B3:"is_sup X (insert x F) s2"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: sup_equality)
qed

lemma bsup_commute:
  "is_sup X {a, b} c \<longleftrightarrow> is_sup X {b, a } c "
  by (simp add: insert_commute)

lemma bsup_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup X {a, b} =  Sup X  {b, a}"
  by (simp add: insert_commute)

lemma bsup_idem1:
  "a\<in> X \<Longrightarrow> Sup X {a, a} = a"
  by (simp add: sup_equality sup_singleton)

lemma sup_ge1:
  "\<lbrakk>c \<in> X; a \<in> X;b \<in> X; a \<ge> c; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow> s \<ge> c "
  by (meson binary_supD21 is_supE1)

lemma sup_ge2:
  "\<lbrakk>is_sup X {a, b} s;a \<in> X; b \<in> X; c \<in> X; b \<ge> c\<rbrakk>  \<Longrightarrow> s \<ge> c"
  by (meson binary_supD32 dual_order.trans is_supE1)

lemma sup_ge3:
  "\<lbrakk>is_sup X {a, b} s;a \<in> X; b \<in> X; c \<in> X; c \<ge>a; c \<ge> b\<rbrakk> \<Longrightarrow> c \<ge> s"
  using is_supD42 ub_doubleI by blast

lemma sup_ge4:
  "\<lbrakk>is_sup X {x, z} sxz; is_sup X {y, z} syz; x \<in> X; y \<in> X; z \<in> X; x \<le> y\<rbrakk> \<Longrightarrow>sxz \<le> syz"
  by (meson binary_supD32 sup_ge1 sup_ge3 is_supE1)

lemma sup_ge5:
  "\<lbrakk>is_sup X {x1, x2} sx; is_sup X {y1, y2} sy; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;x1 \<le> y1; x2 \<le> y2\<rbrakk> \<Longrightarrow>sx \<le> sy"
  by (meson sup_ge1 sup_ge2 sup_ge3 is_supE1)

lemma ge_sup_iff:
  "\<lbrakk>is_sup X {a, b} s; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<ge> s \<longleftrightarrow> c \<ge> a \<and> c \<ge> b)"
  by (simp add: binary_supD4 is_supE1)

lemma sup_assoc1:
  "\<lbrakk>is_sup X {a, b} sab; is_sup X {sab, c} sab_c; is_sup X {b, c} sbc; is_sup X {a, sbc} sbc_a;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sbc_a = sab_c"
  by(rule order.antisym; meson binary_supD31 binary_supD32 ge_sup_iff is_supE1)+

lemma sup_assoc2:
  "\<lbrakk>is_sup X {b, c} sbc; is_sup X {a, sbc} sbc_a; is_sup X {a, c} sac; is_sup X {b, sac} sac_b;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sac_b=sbc_a"
  by(rule order.antisym; meson binary_supD31 binary_supD32 ge_sup_iff is_supE1)+

lemma sup_idem2:
  "\<lbrakk>a \<in> X; b \<in> X; is_sup X {a, b} s\<rbrakk> \<Longrightarrow> is_sup X {a, s} s"
  by (simp add: binary_supI1 is_supD1121 is_supE1)

lemma sup_idem3:
  "\<lbrakk>a \<in> X; b \<in> X; is_sup X {a, b} s\<rbrakk> \<Longrightarrow> is_sup X {b, s} s"
  by (simp add: binary_supI1 is_supD1121 is_supE1)

lemma ge_sup1:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Sup X {a, b} = b"
  by (simp add: binary_supI1 sup_equality)

lemma ge_sup2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Sup X {a, b} = a"
  by (simp add: binary_supI2 sup_equality)

lemma sup_upper_bounds:
  "is_sup X A s \<Longrightarrow> ubd X {s} = ubd X A"
  by(auto simp add:ubd_mem_iff; simp add: is_supD41 ub_singleton_simp;simp add: is_supE4 ub_singleton)

subsection Infima

definition is_inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_inf X A x \<equiv> (is_greatest (lbd X A) x)"

lemma is_infI1:
  "is_greatest (lbd X A) x \<Longrightarrow> is_inf X A x"
  by (simp add: is_inf_def) 

lemma is_infD1:
  "is_inf X A x \<Longrightarrow> (is_greatest (lbd X A) x)"
  by (simp add: is_inf_def)

lemma is_infI2:
  "x \<in> ubd (lbd X A) (lbd X A) \<Longrightarrow> is_inf X A x"
  using is_greatest_def is_infI1 by blast

lemma is_infD2:
  "is_inf X A x \<Longrightarrow> x \<in> ubd (lbd X A) (lbd X A)"
  using is_greatest_def is_infD1 by blast

lemma is_infI3:
  "\<lbrakk>x ub (lbd X A); x \<in> (lbd X A)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI1 greatestI2)

lemma is_infD31:
  "is_inf X A x \<Longrightarrow> x ub (lbd X A)"
  by (simp add: is_inf_def greatestD12)

lemma is_infD32:
  "is_inf X A x \<Longrightarrow> x \<in> (lbd X A)"
  by (simp add: is_infD1 greatestD1)

lemma is_infI4:
  "\<lbrakk>x ub (lbd X A); x \<in> X; x lb A\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: lbd_mem_iff greatestI2 is_infI1)

lemma is_infE1:
  "is_inf X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_infD32[of "X" "A" "x"] lbdD2[of "x" "X" "A"])

lemma is_infI5:
  "\<lbrakk>(\<And>a. a \<in> (lbd X A) \<Longrightarrow> x \<ge> a); x \<in> (lbd X A)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI1 greatestI3)

lemma is_infI6:
  "\<lbrakk>x \<in> X; x lb A; (\<And>a. a \<in> (lbd X A) \<Longrightarrow> x \<ge> a)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI5 lbdI2)

lemma is_infI7:
  "\<lbrakk>x \<in> X; x lb A; (\<And>a. a \<in> X \<Longrightarrow> a lb A \<Longrightarrow>  x \<ge> a)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI4 ub_def lbd_mem_iff)

lemma is_infI8:
  "\<lbrakk>x \<in> X; (\<And>z. z \<in> lbd X A \<longleftrightarrow> z \<le> x)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI1 greatest_iff)

lemma is_infI9:
  "\<lbrakk>x \<in> X; (\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A))\<rbrakk> \<Longrightarrow> is_inf X A x"
  using is_infI7 by blast

lemma is_infE2:
  "is_inf X A x \<Longrightarrow> x lb A" 
  by(simp add: lbdD3[of "x" "X" "A"] is_infD32[of "X" "A" "x"])            

lemma is_infE3:
  "\<lbrakk> is_inf X A x; y \<in> lbd X A\<rbrakk> \<Longrightarrow> x \<ge> y "
  by (simp add: is_inf_def greatestD2)

              
lemma is_infE4:
  "\<lbrakk>is_inf X A x; y \<in> X; y lb A\<rbrakk> \<Longrightarrow> x \<ge> y "
  by (simp add: lbd_mem_iff is_infE3)
        
lemma is_infE5:
  "\<lbrakk>is_inf X A x; z \<in> X;  x \<ge> z\<rbrakk> \<Longrightarrow> z \<in> lbd X A"
  by (simp add: is_infE2 lb_iso1 lbdI2)

lemma is_infD1121:
  "\<lbrakk>is_inf X A x; a \<in> A \<rbrakk> \<Longrightarrow> a \<ge> x"
  using is_infE2 lbE by blast

lemma is_infE6:
  "\<lbrakk>is_inf X A x;  x \<ge> z\<rbrakk> \<Longrightarrow> z lb A"
  by (simp add: is_infE2 lb_iso1)

lemma is_infE7:
  "\<lbrakk>is_inf X A x;  x \<ge> z; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> z"
  by (simp add: is_infE6[of "X" "A" "x" "z"] lbD[of "z" "A" "a"])

lemma is_infD41:
  "is_inf X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> z \<le> x \<Longrightarrow> z lb A)"
  by (simp add: is_infE6)

lemma is_infD42:
  "is_inf X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  z lb A \<Longrightarrow> z \<le> x)"
  by (simp add: is_infE4)

lemma is_infD5:
  "is_inf X A x \<Longrightarrow> (\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A))"
  using is_infE4 is_infE6 by blast

lemma is_inf_iff1:
  "\<lbrakk>x \<in> X; A \<subseteq> X\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A)) \<longleftrightarrow> is_inf X A x)"
  by (meson is_infD5 is_infI9)

lemma inf_iff2:
  "is_inf X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  s \<ge> z \<longleftrightarrow> z \<in> lbd X A)"
  by (meson dual_order.refl is_infE1 is_infE3 is_infE5 is_infI5 lbdD2)

lemma is_inf_unique:
  "is_inf X A m1 \<Longrightarrow> is_inf X A m2 \<Longrightarrow> m1 = m2"
  using is_infD1 greatest_unique by blast

lemma is_inf_ant1:
  "A \<subseteq> B \<Longrightarrow> is_inf X A ma \<Longrightarrow> is_inf X B mb \<Longrightarrow> ma \<ge> mb "
  by (simp add: is_infE1 is_infE2 is_infE4 lb_ant2)

lemma is_inf_iso2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_inf Y A my \<Longrightarrow> is_inf X A mx \<Longrightarrow> mx \<ge> my"
  by (simp add: in_mono is_infD42 is_infE1 is_infE2)


lemma inf_minI1:
  "is_inf X A x \<Longrightarrow> x \<in> A \<Longrightarrow> (is_least A x)"
  by (simp add: leastI2 is_infE2)

lemma inf_minE1:
  "(is_least A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_inf X A x"
  by (simp add: leastD11 leastD12 is_infI6 lbdD1)

lemma inf_minE2:
  "(is_least A x) \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf X A x"
  using leastD11 inf_minE1 by blast

lemma inf_min_eq:
  "A \<subseteq> X \<Longrightarrow> (is_inf X A x \<and> x \<in> A) \<longleftrightarrow> (is_least A x)"
  using leastD11 inf_minE2 inf_minI1 by blast

lemma inf_min_eq2:
  "(is_inf A A x) \<longleftrightarrow> (is_least A x)"
  using leastD11 is_infE1 inf_minE1 inf_minI1 by blast

lemma inf_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_inf X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_inf B A s"
  by(simp add:in_mono inf_iff2 lbd_mem_iff)

lemma inf_singleton:
  "s \<in> X \<Longrightarrow> is_inf X {s} s"
  by (simp add: inf_minE1 least_singleton)

lemma inf_emptyI:
  "is_greatest X i \<Longrightarrow> is_inf X {} i"
  by (simp add: is_inf_def lbd_empty)

lemma inf_emptyD:
  "is_inf X {} i \<Longrightarrow> is_greatest X i "
  by (simp add: is_inf_def lbd_empty)

lemma inf_empty:
  "is_inf X {} i \<longleftrightarrow> (is_greatest X i)"
  by (simp add: lbd_empty is_inf_def)

lemma binary_infI1:
  "\<lbrakk>a \<in> X; b \<in> X; a \<ge> b\<rbrakk> \<Longrightarrow> is_inf X {a, b} b"
  by (simp add: least_insert2 least_singleton inf_minE1)

lemma binary_infD21:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_inf X {a, b} s; c \<ge> a\<rbrakk> \<Longrightarrow>  c \<ge> s"
  using is_infD1121 by fastforce

lemma binary_infD22:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_inf X {a, b} s; c \<ge> b\<rbrakk> \<Longrightarrow>  c \<ge> s"
  by (simp add: binary_infD21 insert_commute)

lemma binary_infD31:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_inf X {a, b} s\<rbrakk>  \<Longrightarrow>  a \<ge> s"
  by (simp add: is_infD1121)

lemma binary_infD32:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_inf X {a, b} s\<rbrakk>  \<Longrightarrow>  b \<ge> s"
  by (simp add: is_infD1121)

lemma binary_infD4:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_inf X {a, b} s\<rbrakk>  \<Longrightarrow> (s \<ge> c \<longleftrightarrow> a \<ge> c \<and> b \<ge> c)"
  by (simp add: inf_iff2 lbd_mem_double)

lemma inf_insert1:
  "\<lbrakk>x lb A; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: least_insert1 inf_minE1)

lemma inf_insert2:
  "\<lbrakk>is_inf X A m;  x \<ge> m\<rbrakk> \<Longrightarrow> is_inf X (insert x A) m"
  by (meson is_infE1 is_infE2 is_infE4 is_infI9 subset_insertI lb_ant2 lb_insert lb_iso1)

lemma inf_insert3:
  "\<lbrakk>is_inf X A m; m \<ge> x; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: is_infD41 inf_insert1)

lemma inf_insert61:
  "\<lbrakk>is_inf X A s1; is_inf X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 lb A"
  by (simp add: is_infD1121 is_infE6)

lemma inf_insert62:
  "\<lbrakk>is_inf X A s1; is_inf X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> lbd X A"
  by (simp add: is_infE1 inf_insert61 lbd_mem_iff)

lemma inf_insert7:
  "\<lbrakk>is_inf X A s1; is_inf X {s1, x} s2; u \<in> lbd X (insert x A)\<rbrakk> \<Longrightarrow>  s2 \<ge> u"
  by (simp add: lbd_mem_iff2 is_infE3)

lemma lb_eq_inf_eq:
  "(\<And>x. x lb A \<longleftrightarrow> x lb B) \<Longrightarrow> (is_inf X A s \<longleftrightarrow> is_inf X B s)"
  by (simp add: lbd_mem_iff inf_iff2)

lemma Lower_eq_inf_eq:
  "lbd X A = lbd X B \<Longrightarrow> (is_inf X A s \<longleftrightarrow> is_inf X B s)"
  by (simp add: is_inf_def)

definition Inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Inf X A \<equiv> (THE m. is_inf X A m)"

lemma inf_equality:
  "is_inf X A m \<Longrightarrow> Inf X A = m"
  by (simp add: Inf_def is_inf_unique the_equality) 

lemma inf_exI:
  "\<exists>t. is_inf X A t \<Longrightarrow> (\<And>t. is_inf X A t \<Longrightarrow> P t) \<Longrightarrow> P (Inf X A)"
  using inf_equality by auto

lemma inf_unc:
  "\<lbrakk>is_inf X (A \<union> B) x; is_inf X A a; is_inf X B b; is_inf X {a, b} c\<rbrakk> \<Longrightarrow> x=c"
  by (metis binary_infD4 inf_iff2 is_infD42 is_infE6 lb_unionD1 lb_unionD2 lb_unionI order_class.order_eq_iff)

lemma inf_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_inf X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb Inf X ` A \<Longrightarrow> x lb \<Union> A"
  by (metis imageI is_infD5 inf_equality lb_def lb_unI)

lemma inf_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_inf X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb \<Union> A \<Longrightarrow>  x lb Inf X ` A"
  by (metis is_infD5 inf_equality lb_imageI lb_unD)

lemma inf_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_inf X Ai si) \<Longrightarrow>(is_inf X ((\<lambda>Ai. Inf X Ai)`A) s) \<longleftrightarrow> (is_inf X (\<Union>A) s)"
  apply(rule Lower_eq_inf_eq, rule lbd_eqI1) using inf_families1 apply blast using inf_families2 by blast


lemma binf_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_inf X {a1, a2} (Inf X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows "is_inf X A (Inf X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 by force
next
  case (insert x F)
  obtain i1 where B0:"is_inf X F i1"  using insert.hyps(4) insert.prems by blast
  have B1:"i1 \<in> X" using B0 is_infE1 by auto
  obtain i2 where B2:"is_inf X {i1, x} i2" using A0 B1 insert.prems by blast
  have B3:"i2 \<in> lbd X (insert x F)" by (meson B0 B2 inf_insert62 insertI2 is_infD1121 lbd_mem_insert singleton_iff)
  have B4:"\<And>l. l \<in> lbd X (insert x F) \<longrightarrow> l \<le> i2"using B0 B2 inf_insert7 by blast
  have B3:"is_inf X (insert x F) i2" by (simp add: B3 B4 is_infI5)
  then show ?case  by (simp add: inf_equality)
qed

lemma binf_commute:
  "is_inf X {a, b} c \<longleftrightarrow> is_inf X {b, a} c "
  by (simp add: insert_commute)

lemma binf_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, b}  =  Inf X {b,a}"
  by (simp add: insert_commute)

lemma binf_idem1:
  "a\<in> X \<Longrightarrow>Inf X {a, a} = a"
  by (simp add:  inf_equality inf_singleton)

lemma inf_le1:
  "\<lbrakk>is_inf X {a, b} i;a \<in> X; b \<in> X; c \<in> X; a \<le> c\<rbrakk>  \<Longrightarrow> i \<le> c"
  using is_infD1121 by fastforce

lemma inf_le2:
  "\<lbrakk>is_inf X {a, b} i;a \<in> X; b \<in> X; c \<in> X; b \<le> c\<rbrakk>  \<Longrightarrow>i \<le> c"
  using is_infE2 lb_doubleE2 by fastforce

lemma inf_le3:
  "\<lbrakk>is_inf X {a, b} i;a \<in> X; b \<in> X; c \<in> X; c \<le>a; c \<le> b\<rbrakk>  \<Longrightarrow>c \<le>i"
  by (simp add: is_infE4 lb_insert lb_singletonD)

lemma inf_le4:
  "\<lbrakk>is_inf X {x, z} ixz; is_inf X {y, z} iyz; x \<in> X; y \<in> X; z \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> ixz \<le> iyz"
  by (meson binary_infD31 binary_infD32 inf_le3 dual_order.trans is_infE1)

lemma inf_le5:
  "\<lbrakk>is_inf X {x1, x2} ix; is_inf X {y1, y2} iy; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;x1 \<le> y1; x2 \<le> y2\<rbrakk> \<Longrightarrow>ix \<le> iy"
  by (meson Posets16.inf_le1 binf_commute inf_le3 is_infE1)

lemma le_inf_iff:
  "\<lbrakk>is_inf X {a, b} i ;a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> i \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 is_infE1)

lemma inf_assoc1:
  "\<lbrakk>is_inf X {a, b} iab; is_inf X {b, c} ibc; is_inf X {iab, c} iab_c; is_inf X {a, ibc} ibc_a;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  ibc_a=iab_c"
  by(rule order.antisym;metis Orderings.order_eq_iff inf_iff2 is_infD42 is_infE6 lb_double_iff1)+

lemma inf_assoc2:
  "\<lbrakk>is_inf X {b, c} ibc;is_inf X {a, ibc} ibc_a;is_inf X {a, c} iac; is_inf X {b, iac} iac_b; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> iac_b=ibc_a"
  by(rule order.antisym;metis Orderings.order_eq_iff inf_iff2 is_infD42 is_infE6 lb_double_iff1)+

lemma inf_idem2:
  "is_inf X {a, b} i \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> is_inf X {a, i} i"
  by (meson binary_infD31 binary_infI1 is_infE1)

lemma inf_idem3:
  "is_inf X {a, b} i \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> is_inf X {b, i} i"
  by (simp add: binary_infI1 is_infD1121 is_infE1)

lemma le_inf1:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Inf X {a, b} = a"
  using inf_equality inf_insert3 inf_singleton by blast

lemma le_inf2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Inf X {a, b} = b"
  by (metis binf_commute2 le_inf1)

lemma inf_lower_bounds:
  "is_inf X A i \<Longrightarrow> lbd X {i} = lbd X A"
  by(auto simp add:lbd_mem_iff; simp add: is_infD41 lb_singleton_simp;simp add: is_infE4 lb_singleton)


subsection Duality

lemma sup_imp_inf_ub:
  "is_sup X A s \<Longrightarrow>  is_inf X (ubd X A) s"
  by(simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)
  
lemma sup_if_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_inf X (ubd X A) s \<Longrightarrow>  is_sup X A s"
  by(auto simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)
  
lemma inf_imp_sup_lb:
  "is_inf X A s \<Longrightarrow>  is_sup X (lbd X A) s"
  by(simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)
  
lemma inf_if_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_sup X (lbd X A) s \<Longrightarrow>  is_inf X A s"
  by(auto simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)


subsection Misc

lemma sup_of_ineq1:
  "\<lbrakk>a \<le> b; is_sup X {a, c} x; is_sup X {b, c} y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson is_supE1 is_supE2 is_supE3 order_trans ub_double_iff1 ubd_mem_double)
 
lemma inf_of_ineq1:
  "\<lbrakk>a \<le> b; is_inf X {a, c} x; is_inf X {b, c} y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson dual_order.trans is_infD42 is_infE1 is_infE2 lb_doubleE1 lb_doubleE2 lb_doubleI)

lemma sup_of_ineq2:
  "\<lbrakk>a \<le> b; c \<le> d; is_sup X {a, c} x; is_sup X {b, d} y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson is_supE1 is_supE2 is_supE4 order_trans ub_double_iff1)
 
lemma inf_of_ineq2:
  "\<lbrakk>a \<le> b; c \<le> d; is_inf X {a, c} x; is_inf X {b, d} y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson dual_order.trans insertI1 is_infD1121 is_infD42 is_infE1 is_infE2 lb_doubleE2 lb_doubleI)

lemma sup_of_ineq3:
  "\<lbrakk>b \<le> a; is_sup X {b, c} x; a \<le> x; is_sup X {a, c} y\<rbrakk> \<Longrightarrow> x =y"
  by (meson dual_order.eq_iff is_supE1 is_supE2 is_supE4 sup_of_ineq1 ub_double_iff1)
 
lemma inf_of_ineq3:
  "\<lbrakk>b \<ge> a; is_inf X {b, c} x; a \<ge> x; is_inf X {a, c} y\<rbrakk> \<Longrightarrow> x =y"
  by (meson inf_of_ineq1 is_infD42 is_infE1 is_infE2 lb_double_iff1 order_antisym)

lemma int_inf1:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (Pow X) A  (\<Inter>A)"
  by(auto simp add:is_inf_def is_greatest_def ubd_def lbd_def ub_def lb_def)

lemma int_inf2:
  "is_inf (Pow X) A (X \<inter> \<Inter>A)"
  by(auto simp add:is_inf_def is_greatest_def ubd_def lbd_def ub_def lb_def)

lemma uni_sup1:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_sup (Pow X) A  (\<Union>A)"
  by(auto simp add:is_sup_def is_least_def lbd_def ubd_def lb_def ub_def)

lemma uni_sup_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Union>A \<in> S\<rbrakk> \<Longrightarrow> is_sup S A (\<Union>A) "
  by (meson Sup_le_iff is_supI9 ub_def)

lemma uni_inf_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Inter>A \<in> S\<rbrakk> \<Longrightarrow> is_inf S A (\<Inter>A) "
  by (meson is_infI9 lb_def le_Inf_iff)

lemma union_sup_univ:
  "\<Union>A = Sup UNIV A"
  by (metis UNIV_I subset_Pow_Union sup_equality top_greatest uni_sup_fam)


lemma lattice_id6:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i\<rbrakk> \<Longrightarrow> s \<le> i \<Longrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b) "
  using is_infE7 is_supE7 by blast

lemma lattice_id7:
  "\<lbrakk>A \<subseteq> lbd X B; is_sup X A s; is_inf X B i\<rbrakk> \<Longrightarrow> s \<le> i "
  using inf_imp_sup_lb is_sup_iso1 by blast

lemma lattice_id8:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i;(\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b)\<rbrakk> \<Longrightarrow> s \<le> i"
  by (simp add: in_mono is_infD42 is_infE1 is_supE4 lb_iff1 ubI)

lemma lattice_id9:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i;(\<forall>a \<in> A. a lb B)\<rbrakk> \<Longrightarrow> s \<le> i"
  using is_infD42 is_infE1 is_supD5 ubI by fastforce


definition is_minimal::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_minimal A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> a \<le> x \<longrightarrow> a =x)"

definition is_maximal::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_maximal A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> x \<le> a \<longrightarrow> a = x)"

lemma maximalD1:
  "is_maximal A x \<Longrightarrow> x \<in> A"
  by(simp add:is_maximal_def)

lemma maximalD2:
  "is_maximal A x \<Longrightarrow> (\<forall>a. a \<in> A \<and> x \<le> a \<longrightarrow> a = x)"
  by(simp add:is_maximal_def)

lemma maximalD3:
  "is_maximal A x \<Longrightarrow> a \<in> A \<Longrightarrow> x \<le> a \<Longrightarrow> a = x"
  by(simp add:is_maximal_def)

lemma maximalD4:
  "is_maximal A x \<Longrightarrow> \<not>(\<exists>a \<in> A. a > x)"
  by (simp add: maximalD3 order.strict_iff_not)

lemma maximalI1:
  "\<lbrakk>x \<in> A; (\<And>a. \<lbrakk>a \<in> A; x \<le> a\<rbrakk> \<Longrightarrow> a = x)\<rbrakk> \<Longrightarrow> is_maximal A x"
  by(simp add:is_maximal_def)

lemma maximalI2:
  "\<lbrakk>x \<in> A; \<not>(\<exists>a \<in> A. a > x)\<rbrakk> \<Longrightarrow> is_maximal A x"
  by (meson dual_order.order_iff_strict maximalI1)

lemma maximalI3:
  "is_greatest A x \<Longrightarrow> is_maximal A x"
  by (simp add: greatest_iff leD maximalI2)

lemma maximalD5:
  "is_maximal A x \<Longrightarrow> y > x \<Longrightarrow> y \<notin> A"
  using maximalD4 by blast

subsection InfSemilattices

definition is_inf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_inf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))"

definition is_finf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_finf_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Inf X {a1, a2} \<in> A)"

lemma is_finf_closedD1:
  "is_finf_closed X A \<Longrightarrow> (\<And>a1 a2. \<lbrakk>a1 \<in> A; a2 \<in> A\<rbrakk> \<Longrightarrow> Inf X {a1, a2} \<in> A)"
  by (simp add: is_finf_closed_def)

lemma is_finf_closedE1:
  "is_finf_closed X A \<Longrightarrow> a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Inf X {a1, a2} \<in> A"
  by (simp add: is_finf_closed_def)

lemma is_finf_closedI1:
  "(\<And>a1 a2. \<lbrakk>a1 \<in> A; a2 \<in> A\<rbrakk> \<Longrightarrow> Inf X {a1, a2} \<in> A) \<Longrightarrow> is_finf_closed X A"
  by (simp add: is_finf_closed_def)

lemma is_finf_closedI2:
  "(\<And>a1 a2. \<lbrakk>a1 \<in> A; a2 \<in> A\<rbrakk> \<Longrightarrow>(\<exists>i \<in> A. is_inf X {a1, a2} i)) \<Longrightarrow> is_finf_closed X A"
  apply(rule is_finf_closedI1) using inf_equality by blast

lemma is_finf_closedI1b:
  "(\<And>E. E \<in> Fpow_ne A \<Longrightarrow> Inf X E \<in> A) \<Longrightarrow> is_finf_closed X A"
  by (simp add: fpow_ne_iff2 is_finf_closedI1)

lemma is_finf_closedI2b:
  "(\<And>E. E \<in> Fpow_ne A \<Longrightarrow> (\<exists>i \<in> A. is_inf X E i)) \<Longrightarrow> is_finf_closed X A"
  by(simp add: is_finf_closedI2 fpow_ne_iff2)

lemma sinfI1:
  "\<lbrakk>(X \<noteq> {});  (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))\<rbrakk> \<Longrightarrow> is_inf_semilattice X"
  by (simp add:is_inf_semilattice_def)

lemma sinfD2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X {a, b} x) "
  by (simp add: is_inf_semilattice_def)

lemma sinfD3:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_inf X {a, b} (Inf X {a, b}) "
  using inf_equality sinfD2 by blast

lemma sinfD4:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (Inf X {a, b}) \<in> X"
  using is_infE1 sinfD3 by blast

lemma binf_leI1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD21 sinfD3 sinfD4)

lemma binf_leI2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD22 sinfD3 sinfD4)

lemma binf_leI3:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<le>a; c \<le> b\<rbrakk>  \<Longrightarrow>c \<le> Inf X {a, b}"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_leI4:
  "\<lbrakk>is_inf_semilattice X; x \<in> X; y \<in> X; z \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> Inf X {x, z} \<le> Inf X {y, z}"
  by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)

lemma binf_leI5:
  "\<lbrakk>is_inf_semilattice X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;x1 \<le> y1; x2 \<le> y2\<rbrakk> \<Longrightarrow> Inf X {x1, x2} \<le> Inf X {y1, y2}"
  by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)

lemma binf_finite2:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_inf X A (Inf X A)"
  by (meson binf_finite sinfD3)

lemma finf_leI1:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; a \<in> A\<rbrakk> \<Longrightarrow> Inf X A \<le> a"
  using is_infD1121[of X A "Inf X A" a] binf_finite2[of X A] by blast

lemma finf_lb:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf X A lb A"
  using is_infD32[of X A "Inf X A"] binf_finite2[of X A] by (simp add: is_infE2)

lemma finf_glb:
   "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> lbd X A\<rbrakk> \<Longrightarrow> b \<le> Inf X A"
  using is_infE3[of X A "Inf X A" b] binf_finite2[of X A] by fastforce  

lemma binfI:
  "\<lbrakk>is_inf_semilattice X; (\<And>s. is_inf X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Inf X {a, b})"
  by (simp add: sinfD3)

lemma binf_commute1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, b} = Inf X {b, a}"
  by (simp add: insert_commute)

lemma binf_iff:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> Inf X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_assoc1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  Inf X {Inf X {a, b}, c} = Inf X {a,  Inf X {b, c}}"
  apply(rule order.antisym) by(simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)+

lemma binf_assoc2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, Inf X {b, c}} = Inf X {b, Inf X {a, c}}"
  apply(rule order.antisym) by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)+

lemma binf_idem2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, Inf X {a, b}} = Inf X {a, b}"
  by (metis binf_assoc1 binf_idem1)

lemma binf_idem3:
  "is_inf_semilattice X \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  Inf X {Inf X {a, b}, b} = Inf X {a, b}"
  by (metis binf_assoc1 binf_idem1)

lemma binf_le1:
  "is_inf_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Inf X {a, b} = a"
  by (simp add: dual_order.eq_iff binf_iff binf_leI1)

lemma binf_le2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Inf X {a, b} = b"
  by (simp add: dual_order.eq_iff binf_iff binf_leI2)

lemma le_binf1:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; Inf X {a, b} = a\<rbrakk> \<Longrightarrow>  a \<le> b"
  by (metis binf_iff dual_order.refl)

lemma le_binf2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; Inf X {a, b} = b\<rbrakk> \<Longrightarrow>  b \<le> a"
  by (simp add: insert_commute le_binf1)


lemma finf_closedD1:
  "is_finf_closed X A \<Longrightarrow> (\<And>a1 a2. a1 \<in> A\<Longrightarrow> a2 \<in> A \<Longrightarrow> Inf X {a1, a2} \<in> A)"
  by (simp add: is_finf_closed_def)

lemma finite_inf_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>  Inf X {a1, a2} \<in> A" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> A" and
          A4:"A \<subseteq> X" and
          A5:"is_inf_semilattice X"
  shows "Inf X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  obtain i where A6:"is_inf X F i"
    by (meson A4 A5 binf_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset order_trans)
  have B0:"i \<in> A"
    using A4 A5 A6 inf_equality insert.hyps(4) insert.prems(1) by blast
  have B1:"x \<in> A"
    using insert.prems(1) by auto
  obtain t where A7:"is_inf X {x, i} t" by (meson A4 A5 A6 dual_order.trans insert.prems(1) insert_subset is_infE1 sinfD2)
  have B2:"t \<in> A"
    using A0 A7 B0 B1 inf_equality by blast
  have B3:"t \<in> (lbd X (insert x F))"
    by (meson A6 A7 insertCI is_infD1121 is_infE1 is_infE5 lbd_mem_insert)
  have B4:"\<And>y. y \<in> (lbd X (insert x F)) \<longrightarrow> y \<le>t "
    by (metis A6 A7 lbdD3 lbd_mem_iff2 insertCI is_infD42 lb_double_iff1)
  have B5:"is_inf X (insert x F) t"
    by (simp add: B3 B4 is_infI5)
  then show ?case
    by (simp add: B2 inf_equality)
qed

lemma inf_semilattice_finf_closed:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_inf_semilattice X\<rbrakk> \<Longrightarrow> Inf X E \<in> A "
  by (metis finite_inf_closed2 is_finf_closed_def)

lemma inf_semilattice_finf_closed2:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<in> Fpow_ne A; is_inf_semilattice X\<rbrakk> \<Longrightarrow> Inf X E \<in> A "
  by (simp add: fpow_ne_iff2 inf_semilattice_finf_closed)

lemma inf_semilattice_finf_closed3:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<in> Fpow_ne A; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_inf X E (Inf X E)"
  by (metis binf_finite2 dual_order.trans fpow_ne_iff2)

lemma inf_semilattice_finf:
  "\<lbrakk>is_inf_semilattice X; A \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> is_inf X A (Inf X A)"
  by (simp add: binf_finite2 fpow_ne_iff2)

lemma finfI:
  "\<lbrakk>is_inf_semilattice X; (\<And>s E. is_inf X E s \<Longrightarrow> P s); F \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> P (Inf X F)"
  using inf_semilattice_finf by blast

lemma inf_semilattice_finf_props0:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, b, c}  \<in> X"
  by(erule finfI,simp add:is_infE1, simp add: fpow_ne_iff2)

lemma inf_assoc_lbd1:
  "is_inf X {b, c} i \<Longrightarrow> x \<in> lbd X {a, i} \<Longrightarrow> x \<in> lbd X {a, b, c}"
  by (meson is_infE5 lbdD2 lbd_mem_doubleE1 lbd_mem_doubleE2 lbd_mem_insert)

lemma inf_assoc_lbd1b:
  "is_inf X {a, b} i \<Longrightarrow> is_inf X {c, d} j \<Longrightarrow> x \<in> lbd X {i, j} \<Longrightarrow> x \<in> lbd X {a, b, c, d}"
  by (meson is_infE5 lbdD2 lbd_mem_doubleE1 lbd_mem_doubleE2 lbd_mem_insert)

lemma inf_assoc_lbd2:
  "\<lbrakk>is_inf X {b, c} i\<rbrakk> \<Longrightarrow> lbd X {a, b, c} = lbd X {a, i} "
  by (auto, simp add: is_infE4 lb_def lbd_mem_iff, simp add:inf_assoc_lbd1)

lemma inf_assoc_lbd2b:
  "is_inf X {a, b} i \<Longrightarrow> is_inf X {c, d} j \<Longrightarrow>  lbd X {i, j} =  lbd X {a, b, c, d}"
  by (auto, simp add:inf_assoc_lbd1b, simp add: is_infE4 lb_double_iff1 lbd_mem_iff2)

lemma inf_assoc_lbd3:
  "\<lbrakk>is_inf X {b, c} i\<rbrakk> \<Longrightarrow> (\<forall>j. is_inf X {a, b, c} j  \<longleftrightarrow> is_inf X  {a, i} j) "
  by (simp add: inf_assoc_lbd2 is_inf_def)

lemma inf_assoc_lbd3a:
  "\<lbrakk>is_inf X {b, c} i; is_inf X {a, b, c} j\<rbrakk> \<Longrightarrow> is_inf X  {a, i} j "
  by (simp add: inf_assoc_lbd2 is_inf_def)

lemma inf_assoc_lbd3b:
  "\<lbrakk>is_inf X {b, c} i;is_inf X  {a, i} j\<rbrakk> \<Longrightarrow>  is_inf X {a, b, c} j"
  by (simp add: inf_assoc_lbd2 is_inf_def)

lemma inf_assoc_lbd4a:
  "\<lbrakk>is_inf X {a, b} i; is_inf X {c, d} j; is_inf X {a, b, c, d} k\<rbrakk> \<Longrightarrow> is_inf X  {i, j} k "
  by (meson Lower_eq_inf_eq inf_assoc_lbd2b)

lemma inf_assoc_lbd4b:
  "\<lbrakk>is_inf X {a, b} i; is_inf X {c, d} j; is_inf X  {i, j} k\<rbrakk> \<Longrightarrow>  is_inf X {a, b, c, d} k"
  by (meson Lower_eq_inf_eq inf_assoc_lbd2b)

lemma inf_semilattice_finf_props1:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> is_inf X {a, Inf X {b, c}} (Inf X {a, b, c})"
  by (metis inf_assoc_lbd3b inf_equality sinfD3 sinfD4)

lemma inf_semilattice_finf_props2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, Inf X {b, c}} = Inf X {a, b, c}"
  by (simp add: inf_equality inf_semilattice_finf_props1)

lemma inf_semilattice_finf_props3:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> is_inf X {Inf X {a, b}, Inf X {c, d}} (Inf X {a, b, c, d})"
  by (meson binf_finite2 bot.extremum finite.emptyI finite_insert inf_assoc_lbd4a insert_not_empty insert_subsetI)

lemma inf_semilattice_finf_props4:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> Inf X {Inf X {a, b}, Inf X {c, d}} = Inf X {a, b, c, d}"
  by (simp add: inf_equality inf_semilattice_finf_props3)

lemma inf_semilattice_finf_anti:
  "\<lbrakk>is_inf_semilattice X; A \<in> Fpow_ne X; B \<in> Fpow_ne X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Inf X B \<le> Inf X A"
  using is_inf_ant1[of A B X "Inf X A" "Inf X B"] inf_semilattice_finf by blast
    
subsection SupSemilattices

definition is_sup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_sup_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup X {a, b} x))"

definition is_fsup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fsup_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup X {a1, a2} \<in> A)"

lemma ssupD2:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X {a, b} x) "
  by (simp add: is_sup_semilattice_def)

lemma ssupD3:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_sup X {a, b} (Sup X {a, b}) "
  using ssupD2 sup_equality by blast

lemma ssupD4:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  (Sup X {a, b}) \<in> X"
  using ssupD3 sup_iff2 by blast

lemma bsup_geI1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD21 ssupD3 ssupD4)

lemma bsup_geI2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD22 ssupD3 ssupD4)

lemma bsup_geI3:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<ge>a; c \<ge> b\<rbrakk> \<Longrightarrow> c \<ge> Sup X {a, b}"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsup_geI4:
  "\<lbrakk>is_sup_semilattice X; x \<in> X; y \<in> X; z \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> Sup X {x, z} \<le> Sup X {y, z}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)

lemma bsup_geI5:
  "\<lbrakk>is_sup_semilattice X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;x1 \<le> y1; x2 \<le> y2\<rbrakk> \<Longrightarrow> Sup X {x1, x2} \<le> Sup X {y1, y2}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)


lemma bsup_iff:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<ge> Sup X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b)"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsupI:
  "\<lbrakk>is_sup_semilattice X; (\<And>s. is_sup X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Sup X {a, b})"
  by (metis is_sup_semilattice_def sup_equality)

lemma bsup_commute1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup X {a, b} = Sup X {b, a}"
  by (simp add: insert_commute)

lemma bsup_assoc1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {Sup X {a, b}, c} =Sup X {a, Sup X {b, c}}"
  apply(rule order.antisym) by (simp add:bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)+

lemma bsup_assoc2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {a, Sup X {b, c}} = Sup X {b, Sup X {a, c}}"
  apply(rule order.antisym)  by(simp add:bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)+

lemma bsup_idem2:
  "is_sup_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  Sup X {a, Sup X {a, b}} =  Sup X {a, b}"
  by (metis bsup_assoc1 bsup_idem1)

lemma bsup_idem3:
  "is_sup_semilattice X \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup X {Sup X {a, b}, b} =  Sup X {a, b}"
  by (metis bsup_assoc1 bsup_idem1)

lemma bsup_ge1:
  "is_sup_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Sup X {a, b} = b"
  by (simp add: Orderings.order_eq_iff bsup_geI2 bsup_geI3)

lemma bsup_ge2:
  "is_sup_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Sup X {a, b} = a"
  by (simp add: dual_order.eq_iff bsup_iff bsup_geI1)

lemma ge_bsup1:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; Sup X {a, b} = b\<rbrakk> \<Longrightarrow> a \<le> b"
  by (metis bsup_geI1 order_refl)

lemma ge_bsup2:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; Sup X {a, b} = a\<rbrakk> \<Longrightarrow>  b \<le> a"
  by (simp add: bsup_commute1 ge_bsup1)

lemma bsup_finite2:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup X A (Sup X A)"
  by (simp add: bsup_finite ssupD3)


lemma fsup_geI1:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> Sup X A"
  using is_supD1121[of X A "Sup X A" a] bsup_finite2[of X A] by blast

lemma fsup_ub:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Sup X A ub A"
  using is_supD32[of X A "Sup X A"] bsup_finite2[of X A] by (simp add: is_supE2)

lemma fsup_lub:
   "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> ubd X A\<rbrakk> \<Longrightarrow> Sup X A \<le> b"
  using is_supE3[of X A "Sup X A" b] bsup_finite2[of X A] by fastforce  

lemma fsup_lub2:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> X; b ub A\<rbrakk> \<Longrightarrow> Sup X A \<le> b"
  by (simp add: fsup_lub ubdI2)

lemma fsup_lub3:
  "\<lbrakk>is_sup_semilattice X;  A \<in> Fpow_ne X; b \<in> ubd X A\<rbrakk> \<Longrightarrow> Sup X A \<le> b"
  by (simp add: fpow_ne_iff2 fsup_lub)


lemma fsup_closedD1:
  "is_fsup_closed X A \<Longrightarrow> (\<And>a1 a2. a1 \<in> A\<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup X {a1, a2} \<in> A)"
  by (simp add: is_fsup_closed_def)

lemma finite_sup_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup X {a1, a2} \<in> A" and 
          A1: "finite E" and
          A2: "E \<noteq> {}" and
          A3: "E \<subseteq> A" and
          A4: "A \<subseteq> X" and
          A5: "is_sup_semilattice X"
  shows "Sup X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  obtain s where A6: "is_sup X F s"
    by (meson A4 A5 bsup_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset order_trans)
  have B0: "s \<in> A"
    using A4 A5 A6 sup_equality insert.hyps(4) insert.prems(1) by blast
  have B1: "x \<in> A"
    using insert.prems(1) by auto
  obtain t where A7: "is_sup X {x, s} t"
    by (meson A4 A5 A6 B1 in_mono is_supE1 ssupD2)
  have B2: "t \<in> A"
    using A0 A7 B0 B1 sup_equality by blast
  have B3: "t \<in> ubd X (insert x F)"
    by (meson A6 A7 insertCI is_supD1121 is_supE1 is_supE5 ubd_mem_insert)
  have B4: "\<And>y. y \<in> ubd X (insert x F) \<longrightarrow> t \<le> y"
    by (metis A6 A7 ubdD3 ubd_mem_iff2 insertCI is_supD42 ub_double_iff1)
  have B5: "is_sup X (insert x F) t"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: B2 sup_equality)
qed

lemma sup_semilattice_fsup_closed:
  "\<lbrakk>is_fsup_closed X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_sup_semilattice X\<rbrakk> \<Longrightarrow> Sup X E \<in> A "
  by (metis finite_sup_closed2 is_fsup_closed_def)


lemma sup_semilattice_fsup:
  "\<lbrakk>is_sup_semilattice X; A \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  by (simp add: bsup_finite2 fpow_ne_iff2)

lemma fsupI:
  "\<lbrakk>is_sup_semilattice X; (\<And>s E. is_sup X E s \<Longrightarrow> P s); F \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> P (Sup X F)"
  using sup_semilattice_fsup by blast

lemma sup_semilattice_fsup_props0:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {a, b, c}  \<in> X"
  by(erule fsupI,simp add:is_supE1, simp add: fpow_ne_iff2)

lemma sup_assoc_ubd1:
  "is_sup X {b, c} s \<Longrightarrow> x \<in> ubd X {a, s} \<Longrightarrow> x \<in> ubd X {a, b, c}"
  by (metis is_supE5 ubdD2 ubd_mem_doubleE1 ubd_mem_doubleE2 ubd_mem_insert)

lemma sup_assoc_ubd1b:
  "is_sup X {a, b} s \<Longrightarrow> is_sup X {c, d} t \<Longrightarrow> x \<in> ubd X {s, t} \<Longrightarrow> x \<in> ubd X {a, b, c, d}"
  by (metis is_supE5 ubdD2 ubd_mem_double ubd_mem_insert)

lemma sup_assoc_ubd2:
  "is_sup X {b, c} s \<Longrightarrow> ubd X {a, b, c} = ubd X {a, s} "
  by (auto, simp add: is_supE4 ub_def ubd_mem_iff, simp add:sup_assoc_ubd1)

lemma sup_assoc_ubd2b:
  "is_sup X {a, b} s \<Longrightarrow> is_sup X {c, d} t \<Longrightarrow>  ubd X {s, t} =  ubd X {a, b, c, d}"
  by (auto, simp add:sup_assoc_ubd1b, simp add: is_supE4 ub_double_iff1 ubd_mem_iff2)

lemma sup_assoc_ubd3:
  "is_sup X {b, c} s \<Longrightarrow> (\<forall>t. is_sup X {a, b, c} t  \<longleftrightarrow> is_sup X  {a, s} t) "
  by (simp add: sup_assoc_ubd2 is_sup_def)

lemma sup_assoc_ubd3a:
  "\<lbrakk>is_sup X {b, c} s; is_sup X {a, b, c} t\<rbrakk> \<Longrightarrow> is_sup X  {a, s} t"
  by (simp add: sup_assoc_ubd2 is_sup_def)

lemma sup_assoc_ubd3b:
  "\<lbrakk>is_sup X {b, c} s;is_sup X  {a, s} t\<rbrakk> \<Longrightarrow>  is_sup X {a, b, c} t"
  by (simp add: sup_assoc_ubd2 is_sup_def)

lemma sup_assoc_ubd4a:
  "\<lbrakk>is_sup X {a, b} s; is_sup X {c, d} t; is_sup X {a, b, c, d} r\<rbrakk> \<Longrightarrow> is_sup X  {s, t} r"
  by (simp add: sup_iff2 ubd_mem_iff3)

lemma sup_assoc_ubd4b:
  "\<lbrakk>is_sup X {a, b} s; is_sup X {c, d} t; is_sup X  {s, t} r\<rbrakk> \<Longrightarrow>  is_sup X {a, b, c, d} r"
  by (meson Upper_eq_sup_eq sup_assoc_ubd2b)

lemma sup_semilattice_fsup_props1:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> is_sup X {a, Sup X {b, c}} (Sup X {a, b, c})"
  by (metis ssupD3 ssupD4 sup_assoc_ubd3b sup_equality)

lemma sup_semilattice_supf_props2:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {a, Sup X {b, c}} = Sup X {a, b, c}"
  by (simp add: sup_equality sup_semilattice_fsup_props1)

lemma sup_semilattice_fsup_props3:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> is_sup X {Sup X {a, b}, Sup X {c, d}} (Sup X {a, b, c, d})"
  by (metis (full_types) bsup_finite2 empty_not_insert empty_subsetI finite.emptyI finite.insertI insert_subsetI sup_assoc_ubd4a)

lemma sup_semilattice_fsup_props4:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> Sup X {Sup X {a, b}, Sup X {c, d}} = Sup X {a, b, c, d}"
  by (simp add: sup_equality sup_semilattice_fsup_props3)

lemma sup_semilattice_fsup_iso:
  "\<lbrakk>is_sup_semilattice X; A \<in> Fpow_ne X; B \<in> Fpow_ne X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup X B"
  using is_sup_iso1[of A B X "Sup X A" "Sup X B"] sup_semilattice_fsup by blast
    
subsection Lattices

definition is_lattice::"'a::order set \<Rightarrow> bool" where
  "is_lattice X \<equiv> ((X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x) \<and>  (\<exists>x. is_sup X {a, b} x)))"

lemma lattI1:
  "\<lbrakk>X \<noteq> {}; (\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf X {a, b} x) \<and>  (\<exists>x. is_sup X {a, b} x))\<rbrakk> \<Longrightarrow> is_lattice X"
  by (simp add: is_lattice_def)

lemma lattI2:
  "\<lbrakk>is_inf_semilattice X; is_sup_semilattice X\<rbrakk> \<Longrightarrow> is_lattice X"
  by (simp add: is_inf_semilattice_def is_sup_semilattice_def lattI1)

lemma lattD1:
  "is_lattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_lattice_def)

lemma lattD21:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD22:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_sup X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD31:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_inf X {a, b} (Inf X {a, b}) "
  using inf_equality lattD21 by blast

lemma lattD32:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_sup X {a, b} (Sup X {a, b}) "
  using sup_equality lattD22 by blast

lemma lattD41:
  "is_lattice X \<Longrightarrow> is_inf_semilattice X"
  by (simp add: is_inf_semilattice_def is_lattice_def)

lemma lattD42:
  "is_lattice X \<Longrightarrow> is_sup_semilattice X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD5:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; Sup X {x, y} = y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (metis bsup_geI1 dual_order.refl lattD42)

lemma latt_iff:
  "is_lattice X \<longleftrightarrow> (is_inf_semilattice X) \<and> (is_sup_semilattice X)"
  using lattD41 lattD42 lattI2 by blast

lemma latt_ge_iff1:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (x \<le> y \<longleftrightarrow> Sup X {x, y} = y)"
  by (auto simp add: bsup_ge1 lattD42 lattD5)

lemma latt_ge_iff2:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (y \<le> x \<longleftrightarrow> Sup X {x, y} = x)"
  by (simp add: bsup_commute2 latt_ge_iff1)

lemma latt_le_iff1:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (x \<le> y \<longleftrightarrow> Inf X {x, y} = x)"
  using binf_le1 lattD41 le_binf1 by blast

lemma latt_le_iff2:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (y \<le> x \<longleftrightarrow> Inf X {x, y} = y)"
  by (simp add: binf_commute2 latt_le_iff1)

lemma lattice_absorb1:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x,Inf X {x, y}} = x"
  by (simp add: binf_leI1 bsup_ge2 latt_iff sinfD4)

lemma lattice_absorb2:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf X {x,Sup X {x, y} } = x"
  by (simp add: binf_le1 bsup_geI1 latt_iff ssupD4)

lemma distrib_sup_le: "\<lbrakk>is_lattice X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, Inf X {y, z}} \<le> Inf X {Sup X {x, y}, Sup X {x, z}}"
  by(auto simp add: bsup_geI1 lattD42 binary_infD4 bsup_geI2 bsup_iff latt_iff sinfD3 sinfD4 ssupD4 binf_leI3 binf_leI1 binf_leI2)

lemma distrib_inf_le: "\<lbrakk>is_lattice X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {Inf X {x, y}, Inf X {x, z}} \<le> Inf X {x, Sup X {y, z}}"
  by(auto simp add:bsup_geI1 lattD42 binary_infD4 bsup_geI2 bsup_iff latt_iff sinfD3 sinfD4 ssupD4 binf_leI1 binf_leI2 binf_leI3)

subsection DistributiveLattices


(*
x \<and> (y \<or> z) = (x \<and> y) \<or> (x \<and> z) 

x \<or> (y \<and> z)=(x \<or> (x \<and> z)) \<or> (y \<and> z) 
           = x \<or> (x \<and> z)  \<or> (y \<and> z)
           = x \<or> (z \<and> (x \<or> y)) 
           =(x \<and> (x \<or> y)) \<or> (z \<and> (x \<or> y))
           =(x \<or> y) \<and> (x \<or> z)


*)

lemma distibD1:
  assumes A0:"is_lattice X" and 
          A1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}" and
          A2:" x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}"
proof-
  have B0:"Sup X {x, Inf X {y, z}} = Sup X {Sup X {x, Inf X {x, z}}, Inf X {y, z}}"
    by (simp add: A0 A2 lattice_absorb1)
  have B1:"... = Sup X {x, Inf X {z, Sup X {x, y}}}"
    by (simp add: A0 A1 A2 binf_commute2 bsup_assoc1 lattD41 lattD42 sinfD4)
  have B2:"... = Sup X {Inf X {Sup X {x, y}, x}, Inf X {Sup X {x, y}, z}}"
    by (simp add: A0 A2 insert_commute lattice_absorb2)
  have B3:"... = Inf X {Sup X {x, y}, Sup X {x, z}}"
    by (simp add: A0 A1 A2 lattD42 ssupD4)
  show ?thesis
    by (simp add: B0 B1 B2 B3)
qed
  
lemma distribD2:
  assumes A0: "is_lattice X" and
          A1: "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}" and
          A2: "x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}"
proof -
  have B0:"Inf X {x, Sup X {y, z}} = Inf X {Inf X {x, Sup X {x, z}}, Sup X {y, z}}"
    by (simp add: A0 A2 lattice_absorb2)
  have B1:"... = Inf X {x, Sup X {z, Inf X {x, y}}}"
    by (simp add: A0 A1 A2 binf_assoc1 bsup_commute2 lattD41 lattD42 ssupD4)
  have B2:"... = Inf X {Sup X {Inf X {x, y}, x}, Sup X {Inf X {x, y}, z}}"
    by (simp add: A0 A2 insert_commute lattice_absorb1)
  have B3:"... = Sup X {Inf X {x, y}, Inf X {x, z}}"
    by (simp add: A0 A1 A2 lattD41 sinfD4)
  show ?thesis
    by (simp add: B0 B1 B2 B3)
qed


definition distributive_lattice::"'a::order set \<Rightarrow> bool" where
  "distributive_lattice X \<equiv> (is_lattice X) \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<forall>z \<in> X. Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}})"

lemma distr_latticeI1:
  "\<lbrakk>is_lattice X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup X {x, Inf X {y, z}} \<ge> Inf X {Sup X {x, y}, Sup X {x, z}})\<rbrakk> \<Longrightarrow> distributive_lattice X"
  by (simp add: distrib_sup_le distributive_lattice_def order_class.order_eq_iff)

lemma distr_latticeD1:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}} "
  by (simp add: distributive_lattice_def insert_commute)

lemma distr_latticeD2:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup X {Inf X {y, z}, x} = Inf X {Sup X {y, x}, Sup X {z, x}}"
  by (simp add: distributive_lattice_def insert_commute)
 
lemma distr_latticeD3:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}"
  using distribD2 distributive_lattice_def by fastforce
 
lemma distr_latticeD4:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf X {Sup X {y, z}, x} = Sup X {Inf X {y, x}, Inf X {z, x}}"
  by (simp add: distr_latticeD3 insert_commute)

lemma lattice_ne_inf_le_sup:
  "\<lbrakk>A \<noteq> {}; is_inf X A i; is_sup X A s\<rbrakk> \<Longrightarrow> i \<le> s"
  by (meson all_not_in_conv dual_order.trans is_infD1121 is_supD1121)

lemma lattice_in_inf_le_sup:
  "\<lbrakk>A \<inter> B \<noteq> {}; is_inf X A i; is_sup X B s\<rbrakk> \<Longrightarrow> i \<le> s"
  by (meson Int_emptyI is_infD1121 is_supD1121 order_trans)

lemma lattice_id0:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, y} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  by (simp add: lb_def binf_leI1 binf_leI2 bsup_geI1 lattD41 lattD42 ssupD4)

lemma lattice_id1:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {y, z} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  by(simp add:lb_def  binary_supD32 binf_leI1 binf_leI2 lattD32 latt_iff ssupD4)

lemma lattice_id2:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, z} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  using lattice_id0[of "X" "x" "z" "y"] by (simp add: insert_commute)

lemma lattice_id3:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, y} ub {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"
  by (simp add: ub_def binf_leI1 bsup_geI1 bsup_geI2 lattD41 lattD42 sinfD4)

lemma lattice_id4:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {y, z} ub {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"
  by (simp add: ub_def binf_leI2 bsup_geI1 bsup_geI2 latt_iff sinfD4)

lemma lattice_id5:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, z} ub {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"
  using lattice_id3[of X x z y] by (simp add: insert_commute)


lemma lattice_id10:
  assumes A0:"is_lattice X" and A1:" x \<in> X \<and> y \<in> X \<and> z \<in> X" 
  shows  "Sup X {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}} \<le> Inf X {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
proof-
  let ?A="{Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"  let ?B="{Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  have B0:"\<forall>a \<in> ?A. a lb ?B" by (simp add: A0 A1 lattice_id0 lattice_id1 lattice_id2)
  have B1:"finite ?A \<and> ?A \<subseteq> X \<and> finite ?B \<and> ?B \<subseteq> X"
    by (metis A0 A1 empty_subsetI finite.emptyI finite_insert insert_subset latt_iff sinfD4 ssupD4)
  have B2:"is_sup X ?A (Sup X ?A) \<and> is_inf X ?B (Inf X ?B)"
    by (meson A0 B1 binf_finite2 bsup_finite2 insert_not_empty lattD41 lattD42)
  have B3:"Sup X ?A \<le> Inf X ?B"
    by (meson B0 B1 B2 lattice_id9)
  show ?thesis
    using B3 by force
qed

lemma distrib_I3:
  "\<lbrakk>distributive_lattice X ;x \<in> X; y \<in>X; z \<in> X; Inf X {x, z} = Inf X {y, z}; Sup X {x, z}=Sup X {y, z}\<rbrakk> \<Longrightarrow> x=y"
  by (metis distributive_lattice_def doubleton_eq_iff lattice_absorb1)

(*lemma distrib_D3:
  assumes A0:"is_lattice X" and
          A1:"(\<And>x y z. \<lbrakk>x \<in> X; y \<in>X; z \<in> X; Inf X {x, z} = Inf X {y, z}; Sup X {x, z}=Sup X {y, z}\<rbrakk> \<Longrightarrow> x=y)"
  shows "distributive_lattice X"
proof-
  have B0:"\<And>x y z. x \<in> X \<and>  y \<in> X \<and> z \<in> X \<longrightarrow> Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}"
  proof
    fix x y z assume A2:"x \<in> X \<and>  y \<in> X \<and> z \<in> X " 
    show "Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}"
*)  
  

subsection CompleteLattices

definition is_cinf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_cinf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf X A x))"

definition is_cinf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_cinf_closed X A \<equiv> (\<forall>E. E \<subseteq> A\<longrightarrow> E \<noteq>{} \<longrightarrow> Inf X E \<in> A)"

definition is_csup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_csup_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup X A x))"

definition is_csup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_csup_closed X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Inf X E \<in> A)"

definition is_clattice::"'a::order set \<Rightarrow> bool" where
  "is_clattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>s. is_sup X A s))"

lemma cinfD2:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (simp add: is_cinf_semilattice_def)

lemma cinfD4:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf X A (Inf X A)"
  using cinfD2 inf_equality by blast

lemma cinfD50:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf X A) \<in> X"
  by (meson cinfD4 is_infE1)

lemma cinfD51:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf X A) lb A"
  by (meson cinfD4 is_infE2)
         
lemma cinfD52:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf X A) \<in> lbd X A"
  by (simp add: cinfD4 is_infD32)

lemma cinfD61:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> l \<in> lbd X A \<Longrightarrow> l \<le> Inf X A"
  by (meson cinfD4 is_infD5 lbdD2 lbdD3)

lemma cinfD62:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> l \<in> X \<Longrightarrow> l lb A \<Longrightarrow>  l \<le> Inf X A"
  by (simp add: cinfD61 lbdI2)

lemma csupD2:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: is_csup_semilattice_def)

lemma clatD21:
  "\<lbrakk>is_clattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: is_clattice_def)

lemma clatD22:
  "\<lbrakk>is_clattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (meson lbd_sub clatD21 inf_if_sup_lb)

lemma clatD1:
  "is_clattice X \<Longrightarrow> is_csup_semilattice X"
  by (simp add: is_clattice_def is_csup_semilattice_def)

lemma clatD2:
  "is_clattice X \<Longrightarrow> is_cinf_semilattice X"
  by (simp add: clatD22 is_cinf_semilattice_def is_clattice_def)

lemma cinfD3:
  "is_cinf_semilattice X \<Longrightarrow> (\<exists>x. is_least X x)"
  by (metis inf_min_eq2 is_cinf_semilattice_def order_refl)

lemma csupD3:
  "is_csup_semilattice X \<Longrightarrow> (\<exists>x. is_greatest X x)"
  by (metis is_csup_semilattice_def order_refl sup_max_eq2)

lemma csupD4:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  using csupD2 sup_equality by blast

lemma clatD41:
  "\<lbrakk>is_clattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  by (simp add: clatD21 sup_exI)

lemma csupD50:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup X A) \<in> X"
  by (meson csupD4 is_supE1)

lemma csupD51:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup X A) ub A"
  by (meson csupD4 is_supE2)
         
lemma csupD52:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup X A) \<in> ubd X A"
  by (simp add: csupD4 is_supD32)

lemma csupD61:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> ubd X A \<Longrightarrow> Sup X A \<le> b"
  by (meson csupD4 is_supE3)

lemma csupD62:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> X \<Longrightarrow> b ub A \<Longrightarrow> Sup X A \<le> b"
  by (simp add: csupD61 ubdI2)

lemma cinf_sup:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; ubd X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (meson ubd_sub cinfD2 sup_if_inf_ub)

lemma csup_inf:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; lbd X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (meson lbd_sub csupD2 inf_if_sup_lb)

lemma csup_fsup:
  "is_csup_semilattice X \<Longrightarrow> is_sup_semilattice X"
  by (simp add: is_csup_semilattice_def is_sup_semilattice_def)

lemma cinf_sinf:
  "is_cinf_semilattice X \<Longrightarrow> is_inf_semilattice X"
  by (simp add: is_cinf_semilattice_def is_inf_semilattice_def)

lemma clatD31:
  "\<lbrakk>is_clattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<in> X"
  by (simp add: clatD1 csupD50)

lemma clatD32:
  "\<lbrakk>is_clattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A \<in> X"
  by (simp add: clatD2 cinfD50)

lemma clat_lattice:
  "is_clattice X \<Longrightarrow> is_lattice X"
  by (simp add: cinf_sinf clatD1 clatD2 csup_fsup latt_iff)

lemma sup_iso1b:
  "\<lbrakk>is_csup_semilattice X; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup X B"
  by (metis csupD4 dual_order.trans is_sup_iso1 ne_subset_ne)

lemma sup_iso1:
  "\<lbrakk>is_clattice X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup X B"
  by (metis clatD21 dual_order.trans is_sup_iso1 sup_equality)

lemma sup_iso2:
  "\<lbrakk>is_clattice X; is_clattice Y;A \<subseteq> Y; Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup Y A"
  by (metis clatD21 dual_order.trans in_mono is_supE2 is_supE4 sup_equality sup_iff2)

lemma inf_anti1:
  "\<lbrakk>is_clattice X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> Inf X B \<le> Inf X A"
  by (metis clatD22 dual_order.trans inf_equality is_inf_ant1)


lemma pow_is_clattice1:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (Pow X) A  (\<Inter>A)"
  by(auto simp add:is_inf_def is_greatest_def ubd_def lbd_def ub_def lb_def)

lemma pow_is_clattice2:
  "is_inf (Pow X) {} X"
  by(auto simp add:is_inf_def is_greatest_def ubd_def lbd_def ub_def lb_def)

lemma pow_is_clattice3:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_sup (Pow X) A  ( \<Union>A)"
  by(auto simp add:is_sup_def is_least_def ubd_def lbd_def ub_def lb_def)

lemma pow_is_clattice:
  "is_clattice (Pow X)"
   using  pow_is_clattice3 apply(auto simp add:is_clattice_def)
   by (metis Pow_not_empty ubd_empty pow_is_clattice1 subset_refl sup_if_inf_ub)

lemma univ_is_clattice:
  "is_clattice (UNIV :: 'a set set)"
  by (metis Pow_UNIV pow_is_clattice)

section Functions
subsection Isotonicity

definition is_isotone::"  'a::order set\<Rightarrow>('a::order \<Rightarrow> 'b::order)  \<Rightarrow> bool" where
  "is_isotone X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

lemma isotoneD1:
  "\<lbrakk>is_isotone X f; x1 \<in> X; x2 \<in> X; x1 \<le> x2 \<rbrakk> \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: is_isotone_def)

lemma isotoneD2:
  "A \<subseteq> X \<Longrightarrow> is_isotone X f \<Longrightarrow> is_isotone A f"
  by (simp add: is_isotone_def subset_eq)

lemma isotoneI1:
  "(\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> f x1 \<le> f x2) \<Longrightarrow> is_isotone X f"
  by (simp add: is_isotone_def)

lemma isotoneD31:
  "\<lbrakk>is_isotone X f; b ub A; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> (f b) ub (f`A) "
  by(auto simp add:ub_def image_iff is_isotone_def subset_iff)

lemma isotoneD32:
  "\<lbrakk>is_isotone X f; b lb A; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> (f b) lb (f`A) "
  by(auto simp add:lb_def image_iff is_isotone_def subset_iff)

lemma isotoneD41:
  "\<lbrakk>is_isotone X f; b \<in> ubd X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> ubd (f`X) (f`A)"
  by (simp add: ubd_mem_iff isotoneD31)
             
lemma isotoneD42:
  "\<lbrakk>is_isotone X f; b \<in> lbd X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> lbd (f`X) (f`A)"
  by (simp add: lbd_mem_iff isotoneD32)

lemma isotoneD51:
  "\<lbrakk>is_isotone X f; is_least A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_least (f`A) (f x)"
  by (simp add: is_least_def isotoneD2 isotoneD42)   

lemma isotoneD52:
  "\<lbrakk>is_isotone X f; is_greatest A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_greatest (f`A) (f x)"
  by (simp add: is_greatest_def isotoneD2 isotoneD41)

lemma isotoneD61:
  "\<lbrakk>is_isotone X f; is_sup X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f x) ub f`A"
  by (simp add: is_supE1 is_supE2 isotoneD31)

lemma isotoneD62:
  "\<lbrakk>is_isotone X f; is_inf X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f x) lb f`A"
  by (simp add: inf_iff2 is_infE2 isotoneD32)

subsection Extensivity

definition is_extensive::" 'a::order set \<Rightarrow>  ('a::order \<Rightarrow> 'a::order) \<Rightarrow> bool" where
  "is_extensive X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> x \<le> f x)"

lemma extensiveI1:
  "\<lbrakk>(\<And>x. x \<in> X \<Longrightarrow> x \<le> f x)\<rbrakk> \<Longrightarrow> is_extensive X f"
  by (simp add: is_extensive_def)

lemma extensiveD1:
  "\<lbrakk>is_extensive X f; x \<in> X\<rbrakk> \<Longrightarrow> x \<le> f x"
  by (simp add: is_extensive_def)         

lemma extensiveD2:
  "\<lbrakk>is_extensive X f; b ub f`X\<rbrakk> \<Longrightarrow> b ub X"
  by (metis dual_order.trans extensiveD1 imageI ub_def)

lemma extensiveD3:
  "\<lbrakk>is_extensive X f; x \<in> X; y \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> x \<le> f y"
  using extensiveD1 order_trans by blast

lemma extensiveD4:
  "\<lbrakk>is_extensive X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  f x1 \<le> f x2\<rbrakk> \<Longrightarrow> x1  \<le> (f x2)"
  by (meson dual_order.trans extensiveD1)

lemma extensive_ub_imp:
  "\<lbrakk>is_extensive X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd (f`X)  (f`A) \<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  by (metis ubd_mem_iff extensiveD1 extensiveD2 extensiveI1 in_mono)

lemma extensive_ub_imp2:
  "\<lbrakk>is_extensive X f; (f`X \<subseteq> X); A \<subseteq> X; b \<in> ubd X  (f`A)\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  by (metis ubd_mem_iff extensiveD2 in_mono is_extensive_def)

lemma is_iso_extD1:
  "\<lbrakk>is_isotone X f;  is_extensive X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> f x \<le> f (f x)"
  by (simp add: extensiveD3 image_subset_iff)


lemma is_iso_sup:
  "is_isotone X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup X A x \<Longrightarrow> is_sup (f`X) (f`A) y  \<Longrightarrow> y \<le> f x"
  by (simp add: ubd_mem_iff is_sup_def isotoneD31 least_iff)

lemma is_iso_inf:
  "is_isotone X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf A X x \<Longrightarrow> is_inf (f`X) (f`A) y  \<Longrightarrow> f x \<le> y"
  by(simp add: is_inf_def lbd_mem_iff lb_ant2 subsetD greatest_iff isotoneD32)

subsection Idempotency

definition is_idempotent::"'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_idempotent X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x)"

lemma idempotentD1:
  "\<lbrakk>is_idempotent X f; x \<in> X \<rbrakk> \<Longrightarrow>  f (f x) = f x"
  by (simp add: is_idempotent_def)

lemma idempotentD3:
  "\<lbrakk>is_idempotent X f; y \<in> f`X \<rbrakk> \<Longrightarrow>  f y = y"
  by (auto simp add: is_idempotent_def)
          
lemma iso_idemD1:
  "\<lbrakk>is_isotone X f; is_idempotent X f; x \<in> X\<rbrakk> \<Longrightarrow> f x \<le> f (f x)"
  by (simp add: idempotentD1)

lemma iso_idemD2:
  "\<lbrakk>is_isotone X f; is_idempotent X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  x1 \<le> f x2\<rbrakk> \<Longrightarrow> f x1  \<le> (f x2)"
   using idempotentD1[of X f x2] isotoneD1[of X f x1 "f x2"] by simp

lemma iso_idemD3:
  "\<lbrakk>is_isotone X f; is_idempotent X f; f`X \<subseteq> X; x1 \<in> X;x2 \<in> X;   x1 \<le> f x2\<rbrakk> \<Longrightarrow> f x1  \<le> (f x2)"
  by (simp add: image_subset_iff iso_idemD2)

lemma idemp_iff:
  "is_idempotent X f \<longleftrightarrow> (\<forall>x \<in> X. (f \<circ> f) x = f x)"
  using is_idempotent_def by auto

lemma idempotentI2:
  "\<lbrakk>is_extensive X f;is_isotone X f;  f`X \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> f (f x) \<le> f x)\<rbrakk> \<Longrightarrow> is_idempotent X f"
  by (simp add: is_idempotent_def is_iso_extD1 order_class.order_eq_iff)

lemma idempotent_isotoneD1:
  "\<lbrakk>is_idempotent X f; is_isotone X f;  f`X \<subseteq> X;  y \<in> f`X;  x \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> y"
   using rev_subsetD[of "y" "f`X" "X"] isotoneD1[of "X" "f" "x" "y"] idempotentD3[of "X" "f" "y"] by simp

subsection Closures 

definition is_closure::" 'a::order set \<Rightarrow>('a::order \<Rightarrow> 'a::order) \<Rightarrow>  bool" where
  "is_closure X f \<equiv> is_extensive X f \<and> is_idempotent X f \<and> is_isotone X f \<and> (f`X \<subseteq> X)"

definition closure_cond::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order ) \<Rightarrow> bool" where
  "closure_cond X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<longrightarrow> x2 \<in> X \<longrightarrow> x1 \<le> f x2 \<longrightarrow> f x1 \<le> f x2)"

lemma isotoneI2:
  "\<lbrakk>is_extensive X f;  closure_cond X f\<rbrakk> \<Longrightarrow> is_isotone X f"
  by (simp add: closure_cond_def extensiveD3 is_isotone_def)

lemma idempotentI3:
  "\<lbrakk>is_extensive X f;  f`X \<subseteq> X; closure_cond X f\<rbrakk> \<Longrightarrow> is_idempotent X f"
  by (simp add: closure_cond_def idempotentI2 image_subset_iff isotoneI2)

lemma closureI3:
  "\<lbrakk>is_extensive X f; f`X \<subseteq> X;  closure_cond X f\<rbrakk> \<Longrightarrow> is_closure X f"
  by (simp add: is_closure_def idempotentI3 isotoneI2)

lemma closureD1:
  "\<lbrakk>is_closure X f;  x \<in> X\<rbrakk> \<Longrightarrow> f x \<in> X"
  by (simp add: image_subset_iff is_closure_def)

lemma closureD2:
  "\<lbrakk>is_closure X f;  y \<in> f`X\<rbrakk> \<Longrightarrow> y \<in> X"
  by(simp add: is_closure_def[of "X" "f"] subsetD[of "f`X" "X" "y"])

lemma closureD3:
  "is_closure X f \<Longrightarrow> closure_cond X f"
  by(simp add:closure_cond_def[of X f] is_closure_def[of X f] iso_idemD3[of X f])

lemma closureD4:
  "\<lbrakk>is_closure X f; x \<in> X; y \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by(simp add:is_closure_def isotoneD1[of "X" "f" "x" "y"])

lemma closureD5:
  "\<lbrakk>is_closure X f; x \<in> X\<rbrakk> \<Longrightarrow> x \<le> f x"
  by(simp add:is_closure_def is_extensive_def)

lemma closureD7:
  "\<lbrakk>is_closure X f; x \<in> X;  y \<in> (f`X) ;  x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> y"
  by (simp add:is_closure_def[of "X" "f"] idempotent_isotoneD1[of "X" "f" "y" "x"])

lemma closureD8:
  "\<lbrakk>is_closure X f;  x \<in> X;  y \<in> (f`X) ;  f x \<le> y\<rbrakk> \<Longrightarrow>  x \<le> y"
  by (simp add:closureD5[of "X" "f" "x"] order_trans[of "x" "f x" "y"])

lemma closureD9:
  "\<lbrakk>is_closure X f;  y \<in> f`X\<rbrakk>  \<Longrightarrow> f y \<le> y"
  by (metis antisym_conv1 idempotentD3 is_closure_def nless_le)

lemma closureD10:
  "\<lbrakk>is_closure X f;  x \<in> X;  f x \<le> x\<rbrakk> \<Longrightarrow> x = f x"
  by (simp add: closureD5 dual_order.eq_iff)

lemma closureD11:
  "\<lbrakk>is_closure X f;  x \<in> X; f x \<le> x\<rbrakk> \<Longrightarrow> x \<in> f `X"
  using closureD10 by blast

lemma cl_sup_eq_sup_cl1:
  "\<lbrakk>is_closure X f; is_sup X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s) \<in> ubd (f`X) (f`A)"
  by (simp add: is_closure_def is_supD32 isotoneD41)

lemma cl_le_cl_iff_le:
  "\<lbrakk>is_closure X f;  is_inf X A i;  A \<subseteq> X\<rbrakk> \<Longrightarrow> (f i) \<in> lbd (f`X) (f`A)"
  by (simp add: is_closure_def is_infD32 isotoneD42)

lemma cl_sup_eq_sup_cl2:
  "\<lbrakk>is_closure X f;  is_sup X A s; b \<in> ubd (f`X) (f`A); A \<subseteq> X\<rbrakk> \<Longrightarrow> s \<le> b"
  by(simp add: is_closure_def[of "X" "f"] ubdD2[of "b" "f`X" "f`A"]  closureD2[of "X" "f" "b"] extensive_ub_imp[of "X" "f" "A" "b"]  is_supE3[of "X" "A" "s"] )

lemma cl_sup_eq_sup_cl3:
  "\<lbrakk>is_closure X f;  is_sup X A s; b \<in> ubd (f`X) (f`A);A \<subseteq> X\<rbrakk> \<Longrightarrow> f s \<le> b"
  by (meson cl_sup_eq_sup_cl2 closureD7 is_supE1 ubd_mem_iff)

(*
cl_sup_eq_sup and cl_sup_ge_sup_cl have converses in extensiveI4 idempotentI4 and isotoneI4 

*)

lemma cl_sup_eq_sup:
  "\<lbrakk>is_closure X f;  is_sup X A s;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s)"
  by(simp add:is_sup_def[of "f`X" "f`A" "f s"] cl_sup_eq_sup_cl1 cl_sup_eq_sup_cl3 is_least_def lbd_mem_iff2)
         
lemma closure_iff2:
  "is_closure X f \<longleftrightarrow> (f`X \<subseteq> X) \<and> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. x1 \<le> f x2 \<longleftrightarrow> f x1 \<le> f x2)"
  by (meson closureD3 closureI3 closure_cond_def dual_order.trans is_closure_def is_extensive_def order_refl)

lemma cl_sup_ge_sup_cl11:
  "\<lbrakk>is_closure X f; is_sup X A s1; is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> s1 \<le> s2"
  by (meson extensive_ub_imp2 is_closure_def is_supD32 is_supE3)

lemma cl_sup_ge_sup_cl2:
  "\<lbrakk>is_closure X f;  is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq>  X\<rbrakk> \<Longrightarrow> s2  \<le> f s1"
  by (meson closureD1 is_closure_def is_supD42 isotoneD61 sup_iff2)

lemma cl_sup_ge_sup_cl3:
  "\<lbrakk>is_closure X f;  is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s2  \<le> f s1"
  by (simp add: cl_sup_ge_sup_cl2 closureD7 is_supE1)

lemma cl_sup_ge_sup_cl4:
  "\<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  \<le> f s2"
  by (simp add: cl_sup_ge_sup_cl11 closureD4 is_supE1)

lemma cl_sup_ge_sup_cl:
  "\<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2"
  by (simp add: cl_sup_ge_sup_cl3 cl_sup_ge_sup_cl4 dual_order.eq_iff)

subsection ClosureRanges

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least (ubd C {x}) c))"

lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (ubd C {x}) c)) \<rbrakk> \<Longrightarrow> is_clr C X"
  by (simp add:is_clr_def)

lemma clrD2:
  "is_clr C X \<Longrightarrow> C \<subseteq> X"
  by (simp add:is_clr_def)

lemma clrD2b:
  "is_clr C X \<Longrightarrow> x \<in> C \<Longrightarrow>x \<in> X"
  by(drule clrD2,simp add:subsetD)

lemma clrD3:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (ubd C {x}) c))"
  by (simp add:is_clr_def)

lemma clrD4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least (ubd C {x}) c)"
  by (simp add:is_clr_def)

lemma clrD5:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X  \<Longrightarrow> ((ubd C {x}) \<noteq> {}))"
  by (simp add: clrD4 least_exD0)

lemma clrD6:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (ubd C {x}) \<noteq> {}"
  by (simp add: clrD5)

lemma clrD7:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c \<in> C.  x \<le> c)"
  by (simp add: clrD6 upbd_neE3)

(*
lemma clrD7:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c. c \<in> C \<and>  x \<le> c)"
  by(rule_tac ?A="{x}" in upbd_neE1, simp add:clrD5,simp)
*)

lemma is_clr_cofinal1:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> (\<exists>c \<in> C.  m \<le> c)"
  by (simp add: clrD7 greatestD11)

lemma is_clr_cofinal2:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> c \<in> C \<Longrightarrow> m \<le> c \<Longrightarrow> m =c"
  by (simp add: clrD2b greatestD2 order_antisym)

lemma is_clr_cofinal:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> m \<in> C"
  using is_clr_cofinal1 is_clr_cofinal2 by blast

definition cl_from_clr::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "cl_from_clr C \<equiv> (\<lambda>x. Least (ubd C {x}))"

lemma cl_range1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (cl_from_clr C) x \<in> C"
  by(simp add:cl_from_clr_def, auto intro: ubdD2 clrD4 least_exD1)

lemma cl_range2:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`X \<subseteq> C"
  using cl_range1 by blast

lemma cl_range3:
  "is_clr C X  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr C) x = x"
  by (simp add: cl_from_clr_def ub_single_least2)

lemma cl_range3b:
  "is_clr C X  \<Longrightarrow> c \<in> C \<Longrightarrow> (\<exists>x \<in> X.  (cl_from_clr C) x = c)"
  using cl_range3 clrD2b by blast

lemma cl_range4:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`C = C"
  by (simp add: cl_range3)

lemma cl_range5:
  "is_clr C X \<Longrightarrow> x \<in> C  \<Longrightarrow> x \<in>  cl_from_clr C ` X"
  using cl_range3b by blast

lemma clr_induced_closure_id:
  "is_clr C X  \<Longrightarrow>  (cl_from_clr C)`X = C"
   by (rule order_antisym, auto simp add: cl_range2 cl_range5)

lemma cl_ext1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> (cl_from_clr C) x"
  by (metis ubdD1 cl_from_clr_def clrD3 least_exD1 singletonI)

lemma cl_ext2:
  "is_clr C X \<Longrightarrow> is_extensive X (cl_from_clr C)"
  by (simp add: cl_ext1 is_extensive_def)

lemma cl_lt_ub1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> c \<in> ubd C {x} \<Longrightarrow> (cl_from_clr C) x \<le> c"
  by (simp add: cl_from_clr_def clrD3 least_exD2)

lemma cl_lt_ub2:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> c \<in> C \<Longrightarrow> x \<le> c \<Longrightarrow> (cl_from_clr C) x \<le> c"
  by (simp add: ubd_singleton2 cl_lt_ub1)

lemma cl_iso1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X  \<Longrightarrow> x \<le> y \<Longrightarrow> (cl_from_clr C) x \<le> (cl_from_clr C) y"
  by (meson cl_ext2 cl_lt_ub2 cl_range1 extensiveD3)

lemma cl_iso2:
  "is_clr C X \<Longrightarrow> is_isotone X (cl_from_clr C)"
  by (simp add: cl_iso1 is_isotone_def)

lemma cl_ide:
  "is_clr C X \<Longrightarrow> is_idempotent X (cl_from_clr C) "
  by (simp add: cl_range1 cl_range3 is_idempotent_def)

lemma cl_is_closure:
  "is_clr C X \<Longrightarrow> is_closure X (cl_from_clr C)"
  by(simp add:is_closure_def cl_ext2 cl_ide cl_iso2 clr_induced_closure_id clrD2)

lemma closure_of_in_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> (f x) \<in> (ubd (f`X) {x})"
  by (simp add: ubd_singleton2 closureD5)

lemma closure_of_lt_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in>  (ubd (f`X) {x}) \<Longrightarrow> (f x) \<le> y"
  by (simp add: closureD7 ubd_singleton_iff)

lemma closure_of_least_closed1:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> is_least (ubd (f`X) {x}) (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub leastI3)

lemma closure_of_least_closed2:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> Least (ubd (f`X) {x}) =  (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub least_equality2 least_iff)

lemma closure_induced_clr:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> is_clr (f`X) X"
  by (metis closure_iff2 closure_of_least_closed1 clrI1 empty_is_image)

lemma closure_induced_clr_id:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> x  \<in> X \<Longrightarrow> (cl_from_clr (f`X)) x = f x"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

(*
  clr_induced_closure_id 
    is_clr C X  \<Longrightarrow>  (cl_from_clr C)`X = C
  
  and closure_induced_clr_id
    is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> x  \<in> X \<Longrightarrow> (cl_from_clr (f`X)) x = f x

  define 
    F=(\<lambda>C. cl_from_clr C)
  and 
    G=(\<lambda>f. f`X)
  
  Then
     F \<circ> G (f) = f 
  where equality is defined on X and
    G \<circ> F (C) = C

*)

lemma closure_induced_clr_dual:
  "is_closure X f1 \<Longrightarrow> is_closure X f2 \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f1 x \<le> f2 x) \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (metis closureD11 closureD2 idempotentD3 is_closure_def subsetI)
                    
lemma clr_induced_closure_dual:
  "is_clr C1 X \<Longrightarrow> is_clr C2 X \<Longrightarrow> C2 \<subseteq> C1 \<Longrightarrow>  x \<in> X \<Longrightarrow> ((cl_from_clr C1) x) \<le> ((cl_from_clr C2) x)"
  by (simp add: cl_ext1 cl_lt_ub2 cl_range1 subsetD)


(*
  Clunky converses to cl_sup_eq_sup
    \<lbrakk>is_closure X f;  is_sup X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s)
  and to cl_sup_ge_sup_cl. 
    \<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2
  Combined they read that f:X\<longrightarrow>X  is a closure 
  iff A \<subseteq> X has a sup then \<Or>A \<le> f (\<Or>A)              (extensiveI4; trivial)
                                = \<Or>\<^sub>(\<^sub>f\<^sub>X\<^sub>)f(A)            (isotoneI4; cl_sup_eq_sup) 
   and if f(A) has a sup in X then f(\<Or>A) = f(\<Or>(fA))  (idempotentI4; cl_sup_ge_sup_cl) 
*)

lemma extensiveI4:
  "(\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup X A s \<Longrightarrow> s \<le> f s) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> is_extensive X f"
  by (metis empty_subsetI extensiveI1 insert_absorb insert_mono is_supI1 ub_single_least1)

lemma idempotentI4:
  "(\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup X A s1 \<Longrightarrow> is_sup X (f`A) s2 \<Longrightarrow> f s1 = f s2) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> is_idempotent X f"
  apply(auto simp add:is_idempotent_def)
  by (metis empty_subsetI image_empty image_insert image_subset_iff insert_subset sup_singleton)

lemma isotoneI4:
  assumes "(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup X A s\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s))" and "f`X \<subseteq>X "
  shows "is_isotone X f"
proof- 
  have P:"\<And>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> f x1 \<le> f x2"
    proof
      fix x1 x2 assume A2:"x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2"
      have B01:"is_sup X {x1, x2} x2"
        by (simp add: A2 binary_supI1)
      have B02:"is_sup (f`X) (f`{x1, x2}) (f x2)"
        by (meson A2 B01 assms(1) empty_subsetI insert_subset)
      show "f x1 \<le> f x2"
        using B02 is_supD1121 by fastforce
    qed
  show ?thesis
    by (simp add: P isotoneI1)
qed

(*so closure ranges are infimum closed and moreover if the poset is topped then this element is closed*)

lemma clrD8:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow> (cl_from_clr C) i \<in> lbd X A"
  by(simp add: lbdI cl_is_closure cl_lt_ub2 closureD1 in_mono is_infE1 is_infE7)

lemma clrD9:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> is_inf X A i \<Longrightarrow> (cl_from_clr C) i \<le> i"
  by (simp add: clrD8 is_infE3)

lemma clrD10:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow>  (cl_from_clr C) i = i"
  by (simp add: cl_ext1 clrD9 is_infE1 order_antisym)

lemma clrD11:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow>  i \<in> C"
  by (metis cl_range1 clrD10 is_infE1)

lemma moore_clI1:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> x \<in> Pow X \<Longrightarrow> is_least (ubd C {x})  (X \<inter> (\<Inter>(ubd C {x}))) "
  by(auto simp add:is_clr_def is_least_def ubd_def lbd_def ub_def lb_def)

(*
two ways to introduce a moore system; either by demonstrating it is inf closed where the infimum
is taken in the powerset i.e. Inf E=X \<inter> (\<Inter>E) which when {} \<noteq> E \<subseteq> Pow X is simply \<Inter>E but to handle
the case of {} cannot be simplified; or by demonstrating separately that X \<in> C and showing
 nonempty infima closure
*)

lemma moore_clI2:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> is_clr C (Pow X)"
  by (metis empty_iff empty_subsetI is_clr_def moore_clI1)

lemma moore_clI3:
  "C \<subseteq> Pow X \<Longrightarrow> X \<in> C \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> E \<noteq> {} \<Longrightarrow> (\<Inter>E) \<in> C) \<Longrightarrow> is_clr C (Pow X)"
  by (metis Inf_insert insert_not_empty insert_subsetI moore_clI2)

lemma clr_cinf_semilattice1:
  assumes A0:"is_clr C X" and A1:"is_cinf_semilattice X"
  shows "\<And>A. A \<subseteq> C \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf C A x \<and> is_inf X A x)"
  by (meson A0 A1 cinfD2 clrD11 clrD2 dual_order.trans inf_in_subset)

lemma clr_clattice1:
  assumes A0:"is_clr C X" and A1:"is_clattice X"
  shows "\<And>A. A \<subseteq> C \<longrightarrow> (\<exists>x. is_sup C A x \<and> is_inf X (ubd C A) x)"
proof
  fix A assume A2:"A \<subseteq> C"
  obtain x where B0:"is_inf X (ubd C A) x"
    by (meson A0 A1 ubd_sub clatD22 is_clr_def order_trans)
  have B1:"is_sup C A x"
    by (meson A0 A2 B0 ubd_sub clrD11 clrD2 inf_in_subset sup_if_inf_ub)
  show "(\<exists>x. is_sup C A x \<and> is_inf X (ubd C A) x)"
    using B0 B1 by blast
qed

lemma clr_is_clattice:
  "\<lbrakk>is_clr C X; is_clattice X\<rbrakk> \<Longrightarrow> is_clattice C"
  by (metis clr_clattice1 is_clattice_def is_clr_def)

lemma closure_range_is_clattice:
  "\<lbrakk>is_closure X f; is_clattice X\<rbrakk> \<Longrightarrow> is_clattice (f`X)"
  using closure_induced_clr clr_is_clattice is_clattice_def by blast


definition ord_embedding::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "ord_embedding f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<longrightarrow> (x1 \<le> x2  \<longleftrightarrow> f x1 \<le> f x2))"

definition ord_isomorphism::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set  \<Rightarrow>  'b::order set  \<Rightarrow> bool" where
  "ord_isomorphism f X Y \<equiv> ord_embedding f X \<and> f`X=Y"

lemma ord_emb_is_inj:
  "ord_embedding f X \<Longrightarrow> inj_on f X"
  by (simp add: inj_on_def ord_embedding_def order_antisym)  

lemma ord_emb_imp1:
  "ord_embedding f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:ord_embedding_def)

lemma ord_emb_imp2:
  "ord_embedding f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow>  x1 \<le> x2"
  by(simp add:ord_embedding_def)

section Subsets
subsection Directedness
definition is_dir::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_dir X ord \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X. ord a c \<and> ord b c))"

lemma is_updirE1:
  "is_dir (X::'a::order set) (\<le>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<le> c \<and> b \<le> c) "
  by (simp add: is_dir_def)

lemma is_updirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. a \<le> c \<and> b \<le> c)) \<Longrightarrow> is_dir (X::'a::order set) (\<le>)"
  by (simp add: is_dir_def)

lemma is_updirD1:
  "\<lbrakk>is_dir (X::'a::order set) (\<le>);a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. c ub {a, b})"
  by (simp add: is_updirE1 ub_double_iff1)

lemma is_updir_empty:
  "is_dir {} (\<le>)"
  by (simp add: is_dir_def)

lemma is_updir_singleton:
  "is_dir {x::'a::order} (\<le>)"
  by (simp add: is_dir_def)


lemma updir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> (X::'a::order set) \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. a1 \<le> c \<and> a2 \<le> c)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> a \<le> c)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by blast
next
  case (insert x F)
  then show ?case
    by (metis A0 dual_order.trans insert_iff insert_subset)
qed

lemma updir_finite2:
  "\<lbrakk>is_dir (X::'a::order set) (\<le>); A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c ub A)"
  by (metis is_dir_def ubI updir_finite1)

lemma updir_finite_obtain:
  assumes "is_dir (X::'a::order set) (\<le>)" and "A \<in> Fpow_ne X"
  obtains c where "c \<in> X \<and> c ub A"
  using updir_finite2[of X A] fpow_ne_iff2[of A X] assms by blast

lemma updir_finite3:
  "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c ub A)) \<Longrightarrow> is_dir (X::'a::order set) (\<le>)"
  apply(auto simp add:ub_def is_dir_def) 
   by (metis bot_least finite.simps insert_iff insert_not_empty insert_subset)

lemma updir_finite:
  "is_dir (X::'a::order set) (\<le>) \<longleftrightarrow> (\<forall>A. A \<subseteq> X \<and> finite A \<and> A \<noteq> {} \<longrightarrow>  (\<exists>c \<in> X. c ub A))"
  by (meson updir_finite2 updir_finite3)

lemma is_dwdirE1:
  "is_dir (X::'a::order set) (\<ge>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<ge> c \<and> b \<ge> c) "
  by (simp add: is_dir_def)

lemma is_dwdirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. a \<ge> c \<and> b \<ge> c)) \<Longrightarrow> is_dir (X::'a::order set) (\<ge>)"
  by (simp add: is_dir_def)

lemma is_dwdirI2:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>i. is_inf X {a, b} i)) \<Longrightarrow> is_dir (X::'a::order set) (\<ge>)"
  by (metis binary_infD31 binary_infD32 is_dwdirI1 is_infE1)

lemma is_dwdirI3:
  "\<lbrakk>is_inf_semilattice X; (\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (Inf X {a, b} \<in> X))\<rbrakk> \<Longrightarrow> is_dir (X::'a::order set) (\<ge>)"
  by (simp add: is_dwdirI2 is_inf_semilattice_def)

lemma is_dwdirI4:
  "\<lbrakk>is_inf_semilattice X; A \<subseteq> X; (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (Inf X {a, b} \<in> A))\<rbrakk> \<Longrightarrow> is_dir (A::'a::order set) (\<ge>)"
  apply(auto simp add:is_dir_def subset_iff) by (metis binf_leI1 binf_leI2 dual_order.refl)

lemma is_dwdirI5:
  "\<lbrakk>is_inf_semilattice X; A \<subseteq> X; is_finf_closed X A\<rbrakk> \<Longrightarrow> is_dir (A) (\<ge>)"
  by (simp add: is_dwdirI4 is_finf_closed_def)

lemma is_dwdir_empty:
  "is_dir {} (\<ge>)"
  by (simp add: is_dir_def)

lemma is_dwdir_singleton:
  "is_dir {x::'a::order} (\<ge>)"
  by (simp add: is_dir_def)

lemma is_dwdirD1:
  "\<lbrakk>is_dir (X::'a::order set) (\<ge>);a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. c lb {a, b})"
  by (simp add: is_dwdirE1 lb_double_iff1)

lemma dwdir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> (X::'a::order set) \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. a1 \<ge> c \<and> a2 \<ge> c)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> a \<ge> c)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by blast
next
  case (insert x F)
  then show ?case
    by (metis A0 dual_order.trans insert_iff insert_subset)
qed

lemma dwdir_finite2:
  "\<lbrakk>is_dir (X::'a::order set) (\<ge>); A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c lb A)"
  by (metis is_dir_def lbI dwdir_finite1)

lemma dwdir_finite3:
  "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c lb A)) \<Longrightarrow> is_dir (X::'a::order set) (\<ge>)"
  apply(auto simp add:lb_def is_dir_def) 
  by (metis bot_least finite.simps insert_iff insert_not_empty insert_subset)

lemma dwdir_finite:
  "is_dir (X::'a::order set) (\<ge>) \<longleftrightarrow> (\<forall>A. A \<subseteq> X \<and> finite A \<and> A \<noteq> {} \<longrightarrow>  (\<exists>c \<in> X. c lb A))"
  by (metis dwdir_finite2 dwdir_finite3)

lemma csup_updir:
  "is_csup_semilattice X \<Longrightarrow> is_dir X (\<le>)"
  by (metis csupD3 is_updirI1 greatestD11 greatestD2)

lemma sup_updir:
  "\<lbrakk>is_sup_semilattice X; is_greatest X m\<rbrakk> \<Longrightarrow> is_dir X (\<le>)"
  by (meson greatestD1 greatestD2 is_updirI1)

lemma cinf_dwdir:
  "is_cinf_semilattice X \<Longrightarrow> is_dir X (\<ge>)"
  by (metis cinfD3 is_dwdirI1 leastD11 leastD2)

lemma sinf_pair_lb:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X\<rbrakk>  \<Longrightarrow>\<exists>c. c \<in> X \<and> c \<le> a \<and>  c \<le> b"
  by(rule_tac ?x="Inf X {a, b}" in exI, simp add:binf_leI1 binf_leI2 sinfD4)

lemma ex_to_space:
  " \<exists>x. x \<in> X \<and> Q x \<Longrightarrow>  \<exists>x \<in> X. Q x"
  by blast

lemma inf_dwdir:
  "\<lbrakk>is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_dir X (\<ge>)"
  by(simp add:is_dir_def ex_to_space sinf_pair_lb)


subsection OrderClosure

definition is_ord_cl::"'a set \<Rightarrow> 'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_ord_cl X A ord \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and> ord a b \<longrightarrow> b \<in> A )"

lemma is_ord_clE1:
  "is_ord_cl (X::'a::order set) A (\<le>)  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> A "
  by (simp add:is_ord_cl_def)

lemma is_ord_clI1:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; ord a b\<rbrakk> \<Longrightarrow> b \<in> A ) \<Longrightarrow> is_ord_cl  (X::'a::order set) A ord"
  by (auto simp add:is_ord_cl_def)

lemma is_ord_empty:
  "is_ord_cl (X::'a::order set) {} ord "
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_space:
  "is_ord_cl (X::'a::order set) X ord "
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_comp1:
  "is_ord_cl (X::'a::order set) A ord \<Longrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a)"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_comp2:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a) \<Longrightarrow> is_ord_cl (X::'a::order set) A ord"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_iff_comp:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl (X::'a::order set) A ord \<longleftrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a) "
  using is_ord_cl_comp1 is_ord_cl_comp2 by blast

lemma is_ord_cl_un:
  "A \<in> (Pow (Pow (X::'a::order set))) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Union>A) ord "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_in:
  "A \<in> (Pow (Pow (X::'a::order set))) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Inter>A) ord "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_un2:
  "A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Union>A) ord "
  by (simp add: is_ord_cl_un)

lemma is_ord_cl_in2:
  "A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Inter>A) ord "
  by (simp add: is_ord_cl_in)

lemma is_ord_cl_un3:
  "(f`I)\<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>i. i \<in> I \<longrightarrow> is_ord_cl X (f i) ord) \<Longrightarrow>  is_ord_cl X (\<Union>i \<in> I. f i) ord "
  apply (rule un_to_ind_un[of "(\<lambda>A. A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord))"  "\<lambda>B. is_ord_cl X B ord" "f" "I"])
  apply (simp add: is_ord_cl_un)
  by blast

lemma is_ord_cl_in3:
  "(f`I)\<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>i. i \<in> I \<longrightarrow> is_ord_cl X (f i) ord) \<Longrightarrow>  is_ord_cl X (\<Inter>i \<in> I. f i) ord "
  apply (rule int_to_ind_int[of "(\<lambda>A. A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord))"  "\<lambda>B. is_ord_cl X B ord" "f" "I"])
  apply (simp add: is_ord_cl_in)
  by blast

lemma ord_cl_memI1:
  "is_ord_cl (X::'a::order set) A ord \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a. a \<in> A \<and> ord a x) \<Longrightarrow> x \<in> A"
  by(auto simp add:is_ord_cl_def)

lemma ord_cl_dwdir_inf:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A (\<ge>)" and A2:"is_ord_cl X A (\<le>)"
  shows "\<And>a b. (a \<in> A \<and> b \<in> A \<and>  is_inf X {a, b} i) \<longrightarrow> (i \<in> A)"
proof
  fix a b assume A3:" (a \<in> A \<and> b \<in> A \<and> is_inf X {a, b} i)"
  obtain c where B0:"c \<in> A \<and> a \<ge> c \<and> b \<ge> c"
    using A1 A3 is_dwdirE1 by blast
  have B1:"c lb {a, b}"
    by (simp add: B0 lb_def)
  have B2:"c \<le> i"
    using A0 A3 B0 B1 is_infE4 by blast
  show "i \<in> A"
    using A2 A3 B0 B2 is_infE1 is_ord_clE1 by blast
qed

subsection Filters
subsection DefinitionAndBasicProps
definition is_filter::"'a::order set\<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_filter X F \<equiv> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (\<ge>)) \<and> is_ord_cl X F (\<le>)"

lemma filterI1:
  "\<lbrakk> F \<noteq> {}; F \<subseteq> X; (is_dir F (\<ge>));  (is_ord_cl X F (\<le>))\<rbrakk> \<Longrightarrow> is_filter X F"
  by (simp add: is_filter_def)

lemma filterI2:
  "\<lbrakk>is_inf_semilattice X; F \<noteq> {}; F \<subseteq> X; is_finf_closed X F; is_ord_cl X F (\<le>)\<rbrakk> \<Longrightarrow> is_filter X F"
  by (simp add: filterI1 is_dwdirI5)

lemma filterD1:
  "is_filter X F \<Longrightarrow> F \<noteq> {}"
  by (simp add: is_filter_def)

lemma filterD2:
  "is_filter X F \<Longrightarrow> F \<subseteq> X"
  by (simp add: is_filter_def)

lemma filterD21:
  "is_filter X F \<Longrightarrow> x \<in> F \<Longrightarrow> x \<in> X"
  using filterD2 by blast

lemma filterD3:
  "is_filter X F \<Longrightarrow> (is_dir F (\<ge>))"
  by (simp add: is_filter_def)

lemma filterD4:
  "is_filter X F \<Longrightarrow> (is_ord_cl X F (\<le>))"
  by (simp add: is_filter_def)

subsection TopElements

lemma filter_greatestD1:
  "is_greatest X m \<Longrightarrow> is_filter X F \<Longrightarrow>  (\<exists>f. f \<in> F \<and> f \<le> m)"
  by (metis is_filter_def ex_in_conv filterD21 greatestD2)

lemma filter_greatestD2:
  "is_greatest X m \<Longrightarrow> is_filter X F \<Longrightarrow>  m \<in> F"
  using filterD4 greatestD11 filter_greatestD1 is_ord_clE1 by blast

subsection FiniteInfClosure

lemma filter_finf_closed:
  "\<lbrakk>is_filter X F; a \<in> F;  b \<in> F;  is_inf X {a, b} i\<rbrakk>\<Longrightarrow> i \<in> F"
  by (meson is_filter_def ord_cl_dwdir_inf)

lemma filter_finf_closed1:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf X {a, b} \<in> F"
  by (meson filterD21 filter_finf_closed sinfD3)

lemma filter_finf_closed3:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf X A \<in> F"
  by (simp add: is_filter_def filter_finf_closed1 finite_inf_closed2)

lemma filter_finf_closed4:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<in> Fpow_ne F\<rbrakk> \<Longrightarrow> Inf X A \<in> F"
  by (simp add: filter_finf_closed3 fpow_ne_iff2)

lemma min_filter1:
  "is_greatest X top \<Longrightarrow> is_filter X {top}"
  by (simp add: is_filter_def greatest_iff is_dwdir_singleton is_ord_cl_def order_antisym) 

lemma min_filter2:
  "\<lbrakk>is_greatest X top; is_filter X F\<rbrakk> \<Longrightarrow>{top} \<subseteq> F"
  by (simp add: filter_greatestD2)

lemma filters_max0:
  "is_inf_semilattice X \<Longrightarrow> is_filter X X"
  by (simp add: is_filter_def inf_dwdir is_inf_semilattice_def is_ord_cl_space)

lemma filters_max1:
  "is_cinf_semilattice X \<Longrightarrow>is_filter X X"
  by (simp add: is_filter_def cinf_dwdir is_cinf_semilattice_def is_ord_cl_space)

section SetOfFilters

definition filters_on::"'a::order set \<Rightarrow> 'a::order set set" where
  "filters_on X \<equiv> {F. is_filter X F}"

lemma filters_on_iff:
  "F \<in> filters_on X \<longleftrightarrow> is_filter X F"
  by (simp add: filters_on_def)

lemma filters_is_clr1:
  "(filters_on X) \<subseteq> Pow X"
  using filterD2 filters_on_iff by fastforce

lemma filters_is_clr1b:
  "is_inf_semilattice X \<Longrightarrow> X \<in> filters_on X"
  by (simp add: filters_max0 filters_on_iff)

lemma filter_inter_upcl:
  "(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F) \<Longrightarrow> is_ord_cl X (\<Inter>EF) (\<le>)"
  by (simp add: filterD2 filterD4 is_ord_cl_in2 subsetI)

lemma filter_pow_memD:
  "EF \<in> Pow(filters_on X) \<Longrightarrow> (\<And>F. F \<in> EF \<Longrightarrow> is_filter X F)"
  using filters_on_iff by auto 
subsection IntersectionOfFilters
subsubsection Upclosed

lemma filter_inter_upcl2:
  "EF \<in> Pow (filters_on X) \<Longrightarrow> is_ord_cl X (\<Inter>EF) (\<le>)"
  by (simp add: filter_inter_upcl filter_pow_memD)

subsubsection Nonempty

lemma filter_inter_ne:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F);is_greatest X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (metis InterI empty_iff filter_greatestD2)

lemma filter_inter_ne2:
  "\<lbrakk>EF \<in> Pow (filters_on X);is_greatest X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (simp add: filter_inter_ne filters_on_iff subset_iff)

lemma filter_inter_sub1:
  "\<lbrakk>EF \<in> Pow_ne (filters_on X); x \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> x \<in> X"
  by (metis Inter_iff ex_in_conv filterD2 filters_on_iff in_mono pow_ne_iff2)

lemma filter_inter_sub2:
  "\<lbrakk>EF \<in> Pow_ne (filters_on X)\<rbrakk> \<Longrightarrow> \<Inter>EF \<subseteq> X"
  by (simp add: filter_inter_sub1 subset_iff)

subsubsection InfimaClosed

lemma filter_inter_double:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); x \<in> \<Inter>EF; y \<in> \<Inter>EF; F \<in> EF\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> F "
  by (meson Inf_lower filter_finf_closed1 filters_on_iff in_mono pow_neD1)

lemma filter_inter_inf:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); x \<in> \<Inter>EF; y \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> \<Inter>EF "
  by (simp add: filter_inter_double)

lemma filter_inter_dwdir1:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); x \<in> \<Inter>EF; y \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> ( Inf X {x, y} \<in> (\<Inter>EF) \<and>  Inf X {x, y} \<le> x \<and>  Inf X {x, y} \<le> y)"
  by (simp add: binf_leI1 binf_leI2 filter_inter_double filter_inter_sub1)

lemma filter_inter_dwdir2:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); x \<in> \<Inter>EF; y \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> (\<exists>c \<in> \<Inter>EF. c \<le> x \<and> c \<le> y)"
  by (meson filter_inter_dwdir1)

lemma filter_inter_dwdir3:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X)\<rbrakk> \<Longrightarrow>is_dir (\<Inter>EF) (\<ge>)"
  by(rule is_dwdirI5, simp,rule filter_inter_sub2, simp,rule is_finf_closedI1,erule filter_inter_inf, simp+)

lemma filter_inter_dir2:
  "\<lbrakk>is_inf_semilattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (\<Inter>{F1, F2}) (\<ge>)"
  by(rule_tac ?X="X" in filter_inter_dwdir3, simp, simp add: filters_on_iff pow_ne_iff2)

lemma filter_inter_dir3:
  assumes "is_inf_semilattice X" "is_filter X F1" "is_filter X F2"
  shows "is_dir (F1 \<inter> F2) (\<ge>)"
  using assms filter_inter_dir2 by auto

subsubsection ClosedUnderIntersection

lemma filter_inter_closed1:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); is_greatest X top\<rbrakk> \<Longrightarrow>  is_filter X (\<Inter>EF)"
  apply(rule filterI1,metis filter_inter_ne2 pow_ne_iff1, simp add:filter_inter_sub2)
  by(simp add:filter_inter_dwdir3, simp add:filter_inter_upcl2 pow_ne_iff1)


lemma filter_inter_closed2:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (\<And>E. \<lbrakk>E \<subseteq> (filters_on X); E \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Inter>E) \<in> (filters_on X))"
  by (simp add: filter_inter_closed1 filters_on_iff pow_neI)

subsection FilterMembership

lemma filter_memI:
  "\<lbrakk>is_filter X F; x \<in> X\<rbrakk> \<Longrightarrow>y \<in> F \<Longrightarrow> y \<le> x \<Longrightarrow> x \<in> F"
  using filterD4 is_ord_clE1 by blast

lemma filter_bsup_memI1:
  "\<lbrakk>is_sup_semilattice X; x \<in> F; is_filter X F; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F"
  by (meson bsup_geI1 filterD21 filter_memI order_refl ssupD4)

lemma filter_bsup_memI2:
  "\<lbrakk>is_sup_semilattice X; x \<in> F; is_filter X F; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {y, x} \<in> F"
  by (simp add: filter_bsup_memI1 insert_commute)

lemma filter_ex_elem:
  "\<lbrakk>is_filter X F\<rbrakk> \<Longrightarrow> \<exists>f. f \<in> F"
  by (simp add: ex_in_conv filterD1)


subsection FilterClosure

lemma filter_is_clr:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_clr (filters_on X) (Pow X)"
  by (simp add: cinf_sinf filter_inter_closed2 filters_is_clr1 filters_is_clr1b moore_clI3)

lemma filter_closure_of_empty1:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (ubd (filters_on X) {{}}) {top}"
  by (simp add: ubd_mem_iff2 filters_on_def filter_greatestD2 least_iff min_filter1)

lemma filter_closure_of_empty2:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (cl_from_clr (filters_on X)) {} = {top}"
  by (simp add: cl_from_clr_def filter_closure_of_empty1 least_equality2)


definition filter_closure::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure X A \<equiv> if A={} then {Greatest X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x}"


lemma filter_closure_iff:
  "A \<noteq> {} \<Longrightarrow> x \<in> filter_closure X A  \<longleftrightarrow> (x \<in> X \<and> ( \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x))"
  by (simp add: filter_closure_def)

lemma filter_closure_memI1:
  "(x \<in> X \<and> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x)) \<Longrightarrow> x \<in> filter_closure X A"
  using filter_closure_iff by blast

lemma filter_closure_memI2:
  "(x \<in> X \<and>  F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x) \<Longrightarrow> x \<in> filter_closure X A"
  using filter_closure_iff by blast

lemma filter_closure_memD1:
  "\<lbrakk>A \<noteq> {}; x \<in> filter_closure X A\<rbrakk> \<Longrightarrow> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x)"
  by (simp add: filter_closure_iff)

lemma filter_closure_memD2:
  "\<lbrakk>A \<noteq> {}; x \<in> filter_closure X A\<rbrakk> \<Longrightarrow> ( \<exists>F \<in> Fpow_ne A. Inf X F \<le> x)"
  by (meson filter_closure_memD1 fpow_neI)

lemma filter_closure_memD3:
  "\<lbrakk>is_greatest X top; x \<in> filter_closure X A\<rbrakk> \<Longrightarrow> (\<exists>F \<in> Fpow_ne A. Inf X F \<le> x) \<or> (x=top)"
  by (metis filter_closure_def filter_closure_memD2 greatestI1 greatest_equality2 greatest_ub)

lemma filter_closure_ne_simp:
  "A \<noteq> {} \<Longrightarrow> filter_closure X A = {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x}"
  by (simp add: filter_closure_def)

lemma filter_closure_singleton:
  "\<lbrakk>A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> filter_closure X A"
  apply(rule_tac ?F="{a}"  in filter_closure_memI2, simp)
  by (metis in_mono inf_equality inf_singleton order_refl)

lemma filter_closure_obtains:
  assumes "A \<noteq> {}" and "x \<in> filter_closure X A"
  obtains Fx where "Fx \<subseteq> A \<and> finite Fx \<and> Fx \<noteq> {}  \<and> Inf X Fx \<le> x"
  by (meson assms filter_closure_iff)

lemma filter_closure_empty:
  "is_greatest X top \<Longrightarrow> filter_closure X {} = {top}"
  by (simp add: filter_closure_def greatest_equality2)

lemma filter_closure_ne:
  "\<lbrakk>X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> filter_closure X A \<noteq> {}"
  by (metis empty_iff filter_closure_def filter_closure_singleton insert_subset subset_empty subset_emptyI)

lemma filter_closure_superset:
  "\<lbrakk>X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure X A"
  using filter_closure_singleton by auto

lemma ne_filter_cl1:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {};is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X A) (\<le>)"
  apply(simp add:filter_closure_ne_simp is_ord_cl_def order.trans) by (meson order.trans)

lemma filter_cl0:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> filter_closure X A"
  by (simp add: filter_closure_singleton subsetI)

lemma filter_cl1:
  "\<lbrakk>is_inf_semilattice X; is_greatest X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X A) (\<le>)"
  by (metis filterD4 filter_closure_empty min_filter1 ne_filter_cl1)

lemma filter_cl_empty:
  "is_dir (filter_closure X {}) (\<ge>)"
  by (simp add: filter_closure_def is_dwdir_singleton)

lemma filter_cl2a:
  assumes csinf:"is_inf_semilattice X" and 
          A0:"A \<subseteq> X" and A1:"A \<noteq> {}"
  shows "is_dir (filter_closure X A) (\<ge>)"
proof-
  have B0:"\<And>a b. a \<in> filter_closure X A \<and> b \<in> filter_closure X A \<longrightarrow> (\<exists>c\<in>filter_closure X A. c \<le> a \<and> c \<le> b)"
  proof
    fix a b assume A1:"a \<in> filter_closure X A \<and> b \<in> filter_closure X A"
    obtain Fa Fb where B1:"Fa \<subseteq> A" "finite Fa" "Fa \<noteq> {}" "Inf X Fa \<le> a" and 
                       B2:"Fb \<subseteq> A" "finite Fb" "Fb \<noteq> {}" "Inf X Fb \<le> b"
      by (meson A1 assms(3) filter_closure_obtains)
    have B3:"Fa \<union> Fb \<subseteq>A \<and> finite (Fa \<union> Fb) \<and> (Fa \<union> Fb) \<noteq> {}"
      by (simp add: B1(1) B1(2) B2(1) B2(2) B2(3))
    have B4:"Fa \<union> Fb \<subseteq> X"
      by (meson A0 B3 dual_order.trans)
    have B5:"Inf X (Fa \<union> Fb) \<in>  (filter_closure X A)"
      by (meson B3 B4 binf_finite2 csinf dual_order.refl filter_closure_memI1 is_infE1)
    have B6:"Inf X (Fa \<union> Fb) \<le> a"
      by (meson A0 B1(2-4) B3 binf_finite2 csinf dual_order.trans is_inf_ant1 semilattice_sup_class.sup_ge1)
    have B7:"Inf X (Fa \<union> Fb) \<le> b"
      by (meson A0 B2(2-4) B3 Un_upper2 binf_finite2 csinf dual_order.trans is_inf_ant1)
    show "(\<exists>c\<in>filter_closure X A. c \<le> a \<and> c \<le> b)"
      using B5 B6 B7 by blast
  qed
  show ?thesis
    by (simp add: B0 is_dwdirI1) 
qed

lemma filter_cl2:
  assumes toped:"is_greatest X top" and
          csinf:"is_inf_semilattice X" and 
          A0:"A \<subseteq> X"
  shows "is_dir (filter_closure X A) (\<ge>)"
proof(cases "A={}")
  case True
  then show ?thesis
    by (simp add: filter_cl_empty)
next
  case False
  then show ?thesis
    using A0 csinf filter_cl2a toped by auto
qed

lemma filter_cl_range:
  "\<lbrakk>is_greatest X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure X A) \<subseteq> X"
  by (metis filterD2 filter_closure_empty filter_closure_iff min_filter1 subsetI)

lemma filter_cl3a:
  "\<lbrakk>is_inf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter X (filter_closure X A)"
  by (metis is_filter_def filter_cl2a filter_closure_iff filter_closure_ne ne_filter_cl1 ne_subset_ne subsetI)

lemma filter_cl3:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_filter X (filter_closure X A)"
  by (simp add: filterI1 filter_cl1 filter_cl2 filter_cl_range filter_closure_ne is_inf_semilattice_def)

lemma filter_cl_least1a:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure X A)\<rbrakk> \<Longrightarrow> \<exists>Fx. Fx \<in> Fpow_ne A \<and> Inf X Fx \<le> x \<and> Inf X Fx \<in> F"
  by (meson filter_closure_memD1 filter_finf_closed3 fpow_neI order.trans)

lemma filter_cl_least1b:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure X A)\<rbrakk> \<Longrightarrow> x \<in> F"
  by (meson filter_cl_least1a filter_closure_iff filter_memI)

lemma filter_cl_least1:
  assumes A0:"is_greatest X top" and A1:" is_inf_semilattice X" and A2:"is_filter X F" and A3:"A \<subseteq> F" and 
  A4:"x \<in>  (filter_closure X A)"
  shows " x \<in>F"
proof(cases "A={}")
  case True
  then show ?thesis
    by (metis A0 A2 A4 filter_closure_empty filter_greatestD2 singleton_iff)
next
  case False
  then show ?thesis
    using A1 A2 A3 A4 filter_cl_least1b by blast
qed

lemma filter_cl_least2a:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<subseteq> F; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure X A) \<subseteq> F"
  using filter_cl_least1b by blast

lemma filter_cl_least2:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X; is_filter X F; A \<subseteq> F\<rbrakk> \<Longrightarrow> (filter_closure X A) \<subseteq> F"
  using filter_cl_least1 by blast

lemma filter_cl_is_ub_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure X A) \<in>  (ubd (filters_on X) {A})"
  by (simp add: filter_cl0 filter_cl3a filters_on_iff ubd_singleton2)

lemma filter_cl_is_ub:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure X A) \<in>  (ubd (filters_on X) {A})"
  by (simp add: ubd_singleton2 filter_cl0 filter_cl3 filters_on_def)

lemma filter_cl_lt_ub_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> X; A \<noteq> {}\<rbrakk>  \<Longrightarrow> F \<in>  (ubd (filters_on X) {A}) \<Longrightarrow> (filter_closure X A) \<le> F"
  by (meson filter_cl_least2a filters_on_iff ubdD2 ubd_mem_singleE)

lemma filter_cl_lt_ub:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> F \<in>  (ubd (filters_on X) {A}) \<Longrightarrow> (filter_closure X A) \<le> F"
  by (meson ubdD1 ubd_mem_iff filter_cl_least2 filters_on_iff insertI1)

lemma filter_cl_is_lub_ne:
  "\<lbrakk>A \<noteq> {}; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_inf (Pow X) (ubd (filters_on X) {A}) (filter_closure X A)"
  by (simp add: filter_cl_is_ub_ne filter_cl_lt_ub_ne filters_is_clr1b inf_minE1 least_iff ubd_singleton2)

lemma filter_cl_is_lub:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_inf (Pow X) (ubd (filters_on X) {A}) (filter_closure X A) "
  by (simp add: filterD2 filter_cl3 filter_cl_is_ub filter_cl_lt_ub inf_minE1 leastI3)

lemma filter_cl_is_lub_ne2:
  "\<lbrakk>A \<noteq> {}; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (ubd (filters_on X) {A}) (filter_closure X A)"
  by (simp add: filter_cl_is_ub_ne filter_cl_lt_ub_ne leastI3)

lemma filter_cl_is_lcl:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (ubd (filters_on X) {A}) (filter_closure X A) "
  by (simp add: filter_cl_is_ub filter_cl_lt_ub leastI3)

lemma filter_closure_eq_closure:                                      
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> filter_closure X A = (cl_from_clr (filters_on X)) A "
  by (metis cl_from_clr_def filter_cl_is_lcl least_equality2)

lemma filter_closure_of_filters1:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> F \<in> A \<Longrightarrow> F \<subseteq> (filter_closure X (\<Union>A))"
  by (metis Union_Pow_eq Union_mono Union_upper filter_cl0 filters_is_clr1 order.trans)

lemma filter_closure_of_filters2_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>filters_on X"
  by (metis all_not_in_conv cSup_least empty_Union_conv filterD1 filterD2 filter_cl3a filters_on_iff in_mono)

lemma filter_closure_of_filters2:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X;is_greatest X top\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>filters_on X"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1)

lemma filter_closure_of_filters3_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>ubd (filters_on X) A"
  by (simp add: filter_closure_of_filters1 filter_closure_of_filters2_ne ubdI)

lemma filter_closure_of_filters3:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>ubd (filters_on X) A"
  by (simp add: filter_closure_of_filters1 filter_closure_of_filters2 ubdI)

lemma filter_closure_of_filters4_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}; G \<in> ubd (filters_on X) A\<rbrakk> \<Longrightarrow> (filter_closure X (\<Union>A)) \<subseteq> G"
  by (metis UnionI Union_least basic_trans_rules(31) ex_in_conv filterD1 filter_cl_least2a filters_on_iff ubd_mem_iff2)

lemma filter_closure_of_filters4:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X;is_greatest X top; G \<in> ubd (filters_on X) A\<rbrakk> \<Longrightarrow> (filter_closure X (\<Union>A)) \<subseteq> G"
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

lemma filters_on_lattice_inf02:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  using filterD4[of "X" "F1"] is_ord_clE1[of "X" "F1" "f1" "z"] filterD4[of "X" "F2"] is_ord_clE1[of "X" "F2" "f2" "z"]
  by (metis Int_iff bsup_geI1 bsup_geI2 dual_order.refl filterD21 lattD42 ssupD4)

lemma filters_on_lattice_inf03:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup X {f1, f2} \<in> F1 \<inter> F2 "
  using filters_on_lattice_inf02 by blast

lemma filter_on_lattice_sup01:
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F "
  by (simp add: filter_bsup_memI2 lattD42)

lemma filter_on_lattice_top0:
  "is_lattice X \<Longrightarrow> is_filter X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> a \<le> x"
  by (meson is_filter_def bsup_iff filter_on_lattice_sup01 insertI1 latt_iff subsetD ubD ub_singleton)

lemma filter_on_lattice_top:
  "\<lbrakk>is_lattice X;  is_filter X {x}\<rbrakk> \<Longrightarrow>  is_greatest X x"
  by(rule greatestI1, rule ubdI, simp add: filter_on_lattice_top0, simp add:filterD21)

lemma filter_on_lattice_eq:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup X {f1, f2})}"
  apply(auto simp add:set_eq_iff)  apply (metis bsup_idem1 filterD21) 
  using filters_on_lattice_inf03[of "X" "F1" "F2"]  by blast+

lemma filters_on_lattice_inf2b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (\<ge>)"
  using filter_inter_dir3 lattD41 by blast

lemma filters_upcl:
  "\<lbrakk>is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (\<le>)"
  apply(auto simp add:is_ord_cl_def) using filterD4 is_ord_clE1 by blast+

lemma filter_on_lattice_inf4b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (metis empty_iff equals0I filterD1 filters_on_lattice_inf02)

lemma filters_on_lattice_inf5b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_filter X (F1 \<inter> F2)"
  by (meson filterD2 filterI1 filter_on_lattice_inf4b filters_on_lattice_inf2b filters_upcl inf.coboundedI2) 

lemma filters_on_lattice_inf6b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd (filters_on X) {F1, F2})"
  by (simp add: lbd_mem_iff filters_on_iff filters_on_lattice_inf5b lb_double_iff1)

lemma filters_on_lattice_inf7b:
  "\<lbrakk>is_filter X F1; is_filter X F2; G \<in> (lbd (filters_on X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: lbd_mem_iff lb_double_iff1)

lemma filters_on_lattice_inf8b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk>\<Longrightarrow> is_inf (filters_on X) {F1, F2} (F1 \<inter> F2)"
  by (meson filters_on_lattice_inf6b filters_on_lattice_inf7b is_infI5)

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
  shows "(\<exists>c \<in> (filter_closure X (\<Union>EF)).  a \<ge> c \<and>  b \<ge> c)"
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
  shows "(\<exists>c \<in> (binary_filter_sup X F1 F2).  a \<ge> c \<and>  b \<ge> c)"
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
  show "(\<exists>c \<in> (binary_filter_sup X F1 F2).  a \<ge> c \<and>  b \<ge> c)"
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
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<in> ubd (filters_on X) {F1, F2}"
  by (simp add: filters_on_lattice_bsup03 filters_on_lattice_bsup04 filters_on_lattice_bsup4 ubd_mem_doubleI)

lemma filters_on_lattice_bsup6:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"G \<in> (ubd (filters_on X) {F1, F2})"
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
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> F; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F"
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
  "[a)\<^sub>X \<equiv> {y \<in> X. a \<le> y} "

lemma lorcI1:
  "y \<in> X \<Longrightarrow> a \<le> y \<Longrightarrow> y \<in> [a)\<^sub>X" 
  by (simp add:lorc_def)

lemma lorcD1:
  "y \<in> [a)\<^sub>X \<Longrightarrow> y \<in> X \<and> a \<le> y"
   by (simp add:lorc_def)

lemma lorcD11:
  "y \<in> [a)\<^sub>X \<Longrightarrow> y \<in> X "
   by (simp add:lorc_def)

lemma lorcD12:
  "y \<in> [a)\<^sub>X \<Longrightarrow> a \<le> y" 
  by (simp add:lorc_def)

lemma lorcD2:"x \<in> X \<Longrightarrow> y \<in> [a)\<^sub>X \<Longrightarrow>  y \<le> x \<Longrightarrow> x \<in> [a)\<^sub>X"
  by(drule lorcD12, erule lorcI1, simp)

lemma lorcD3:
  "(\<exists>b. b \<le> x \<and> b \<in> [a)\<^sub>X) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> [a)\<^sub>X"
  using lorcD2 by blast

lemma lorc_mem_iff1:
  "y \<in> ([a)\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> a \<le> y)" by (simp add:lorc_def)

lemma lorc_mem_iff2:
  "y \<in> ([a)\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> y ub {a})" by (simp add:lorc_def ub_def)

lemma lorc_eq_upbd:
  "([a)\<^sub>X) = (ubd X {a})"
  by(simp add: set_eq_iff ubd_mem_iff lorc_mem_iff2)

lemma lorc_eq_upbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. [a)\<^sub>X) = ubd X A"
  by(auto simp add:ubd_mem_iff2 lorc_mem_iff1)

lemma lorc_memI1:
  "a \<in> X \<Longrightarrow> a \<in> [a)\<^sub>X "
  by (simp add: lorcI1)

lemma lorc_mem_point1:
  "a \<in> X \<longleftrightarrow> a \<in> ([a)\<^sub>X)"
  by (simp add: lorc_def)

lemma lorc_subset1:
  "([a)\<^sub>X) \<subseteq> X"
  by (simp add: ubd_sub lorc_eq_upbd)

lemma lorc_top:
  "is_greatest X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> [a)\<^sub>X"
  by (simp add: greatestD11 greatestD2 lorcI1)

lemma lorc_sup_latticeD1:
  "\<lbrakk>is_sup_semilattice X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup X {x, y} \<in> ([x)\<^sub>X)"
  by (simp add: bsup_geI1 lorcI1 ssupD4)

lemma lorc_inf_latticeD1:
  "\<lbrakk>is_least X bot\<rbrakk> \<Longrightarrow> ([bot)\<^sub>X) = X"
  by(auto simp add: lorc_mem_iff1 least_iff)

lemma lorc_dual_iso:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ([a)\<^sub>X) \<subseteq> ([b)\<^sub>X)  \<longleftrightarrow> b \<le> a"
  by(auto simp add:lorc_mem_iff1) 

lemma lorc_upclI:
  "a \<in> X \<Longrightarrow> is_ord_cl X ([a)\<^sub>X) (\<le>)"
  by (simp add: is_ord_clI1 lorcD2)

lemma lorc_upclD:
  "U \<subseteq> X \<Longrightarrow> is_ord_cl X U (\<le>) \<Longrightarrow> is_least U x \<Longrightarrow> U = [x)\<^sub>X"
  apply (auto simp add: in_mono leastD2 lorcI1)
  by (meson is_ord_clE1 leastD11 lorcD1)

lemma lorc_upcl1:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. [a)\<^sub>X)"
  by (simp add: greatestD11 greatestD2 in_mono lorcI1)

lemma lorc_upcl3:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. [a)\<^sub>X) (\<le>)"
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
  "\<lbrakk>is_lattice X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ([a)\<^sub>X) \<inter> ([b)\<^sub>X) = [Sup X {a, b})\<^sub>X"
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

lemma rolcD2:"x \<in> X \<Longrightarrow> y \<in> (a]\<^sub>X \<Longrightarrow>  x \<le> y \<Longrightarrow> x \<in> (a]\<^sub>X"
  by(drule rolcD12, erule rolcI1, simp)

lemma rolcD3:
  "(\<exists>b. x \<le> b \<and> b \<in> (a]\<^sub>X) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> (a]\<^sub>X"
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
  "((a]\<^sub>X) = (lbd X {a})"
  by(simp add: set_eq_iff lbd_mem_iff rolc_mem_iff2)

lemma rolc_eq_lbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. (a]\<^sub>X) = lbd X A"
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
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ((a]\<^sub>X) \<subseteq> ((b]\<^sub>X)  \<longleftrightarrow> a \<le> b"
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
  "up_cl X A = {x \<in> X. \<exists>a \<in> A. a \<le> x}"

lemma up_cl_mem_iff:
  "x \<in> up_cl X A \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. a \<le> x))"
  by (simp add: up_cl_def)

lemma up_cl_memD1:
  "x \<in> up_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: up_cl_def)

lemma up_cl_memD2:
  "x \<in> up_cl X A \<Longrightarrow> \<exists>a \<in> A. a \<le> x"
  by (simp add: up_cl_def)

lemma up_cl_memI1:
  "x \<in> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<le> x \<Longrightarrow> x \<in> up_cl X A"
   using up_cl_def by auto 

lemma up_cl_memI2:
  "x \<in> X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x) \<Longrightarrow> x \<in> up_cl X A"
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
  "x \<in> up_cl X {a}  \<longleftrightarrow> (x \<in> X \<and> a \<le> x)"
  by (simp add: up_cl_mem_iff)

lemma up_cl_lorc:
  "up_cl X {a} = [a)\<^sub>X"
  by (simp add: lorc_mem_iff1 set_eq_iff up_cl_singleton)

lemma up_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_extensive_def up_cl_sub2)

lemma up_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_isotone_def up_cl_iso1)

lemma up_cl_idem:
  "is_idempotent (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_idempotent_def up_cl_idem3)

lemma up_cl_cl:
  "is_closure (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: image_subsetI is_closure_def up_cl_ext up_cl_idem up_cl_iso up_cl_sub3)

lemma up_cl_memI3:
  "\<And>a b. \<lbrakk>a \<in> (up_cl X A); b \<in> X; a \<le> b\<rbrakk> \<Longrightarrow> b \<in> (up_cl X A)"
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
  "is_extensive (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_extensive_def dw_cl_sub2)

lemma dw_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_isotone_def dw_cl_iso1)

lemma dw_cl_idem:
  "is_idempotent (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_idempotent_def dw_cl_idem3)

lemma dw_cl_cl:
  "is_closure (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: image_subsetI is_closure_def dw_cl_ext dw_cl_idem dw_cl_iso dw_cl_sub3)

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
  have B0:"\<And>a b.  a \<in> dw_cl X A \<and> b \<in> dw_cl X A \<longrightarrow> (\<exists>c\<in>dw_cl X A. c \<ge> a \<and> c \<ge> b)"
  proof
    fix a b assume A2:"a \<in> dw_cl X A \<and> b \<in> dw_cl X A"
    obtain a1 b1 where B1:"a1 \<in> A \<and> b1 \<in> A \<and> a1 \<ge> a \<and> b1 \<ge> b"  by (meson A2 dw_cl_memD2)
    obtain c where B2:"c \<in> A \<and> c \<ge> a1 \<and> c \<ge> b1" using A0 B1 is_updirE1 by blast
    have B3:"c \<in> dw_cl X A \<and> c \<ge> a \<and> c \<ge> b" by (metis A1 B1 B2 dual_order.trans dw_cl_sub1)
    show "\<exists>c\<in>dw_cl X A. c \<ge> a \<and> c \<ge> b"
      using B3 by auto
  qed
  show ?thesis
    by (simp add: B0 is_updirI1)
qed

lemma dwcl_updir_is_updir:
  assumes A0:"is_dir (dw_cl X A) (\<le>)" and A1:"A \<subseteq> X"
  shows "is_dir A (\<le>)"
proof-
  have B0:" \<And>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>c\<in>A. c \<ge> a \<and> c \<ge> b)"
  proof
    fix a b assume A2:"a \<in> A \<and> b \<in> A"
    have B1:"a \<in> dw_cl X A \<and> b \<in> dw_cl X A" by (simp add: A1 A2 dw_cl_sub1)
    obtain c where B2:"c \<in> dw_cl X A \<and> c \<ge> a \<and> c \<ge> b"  using A0 B1 is_updirE1 by blast
    obtain d where B3:"d \<in> A \<and> d \<ge> c" using B2 dw_cl_memD2 by blast
    have B4:"d \<in> A \<and> d \<ge> a \<and> d \<ge> b" using B2 B3 order.trans by blast
    show "\<exists>c\<in>A. c \<ge> a \<and> c \<ge> b" using B4 by auto
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
  "\<lbrakk>is_antitone Y g; is_extensive X (g \<circ> f); f x \<in> Y; g`Y \<subseteq> X; x \<in> X; y \<in> Y; y \<le> f x \<rbrakk> \<Longrightarrow> x \<le> g y"
  using antitoneD[of Y g y "f x"] extensiveD1[of X "(g \<circ> f)" x] order.trans by simp

lemma gcI:
  "\<lbrakk>is_antitone X f; is_extensive X (g \<circ> f);
      is_antitone Y g;  is_extensive Y (f \<circ> g); 
        f`X \<subseteq> Y; g`Y \<subseteq> X \<rbrakk> \<Longrightarrow>  galois_conn f X g Y"
  by(auto simp add:galois_conn_def anti_ext_gc)

lemma gcD:
  "galois_conn f X g Y \<Longrightarrow>is_antitone X f \<and> is_extensive X (g \<circ> f) \<and>
                           is_antitone Y g \<and>  is_extensive Y (f \<circ> g) \<and> f`X \<subseteq> Y \<and> g`Y \<subseteq> X"
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
  "galois_conn f X g Y \<Longrightarrow> is_idempotent X (g \<circ> f)"
  by (simp add: gc_idem1a is_idempotent_def)

lemma gc_idem2a:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> f (g ( f (g y) ) ) = f (g y)"
  by (simp add: gc_triple2)

lemma gc_idem2b:
  "galois_conn f X g Y \<Longrightarrow> is_idempotent Y (f \<circ> g)"
  by (simp add: gc_idem2a is_idempotent_def)

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
  "galois_conn f X g Y \<Longrightarrow> is_extensive X (g \<circ> f)"
  by (simp add: gcD)

lemma gc_ext2:
  "galois_conn f X g Y \<Longrightarrow> is_extensive Y (f \<circ> g)"
  by (simp add: gcD)
    
lemma gc_sub1:
  "galois_conn f X g Y \<Longrightarrow>(\<lambda>x.  g (f x)) ` X \<subseteq> X"
  by (simp add: galois_connD12 galois_connD22 image_subset_iff)       
    
lemma gc_sub2:
  "galois_conn f X g Y \<Longrightarrow>(\<lambda>y. f (g y)) ` Y \<subseteq> Y"
  by (simp add: galois_connD12 galois_connD22 image_subset_iff)       

lemma gc_closure1:
  "galois_conn f X g Y \<Longrightarrow> is_closure X (g \<circ> f)"
  by (simp add: is_closure_def gc_sub1 gc_ext1 gc_iso1b gc_idem1b)

lemma gc_closure2:
  "galois_conn f X g Y \<Longrightarrow> is_closure Y (f \<circ> g)"
  by (simp add: is_closure_def gc_sub2 gc_ext2 gc_iso2b gc_idem2b)

lemma ul_galois:
  "galois_conn (\<lambda>A. ubd X A) (Pow X) (\<lambda>A. lbd X A) (Pow X)"
  apply(rule gcI) 
  apply(simp add: ubd_ant1 is_antitone_def)
  apply(simp add: lubd_comp1 is_extensive_def)
  apply(simp add: lbd_ant1 is_antitone_def)
  apply(simp add: ulbd_comp1 is_extensive_def)
  apply (simp add: ubd_sub image_subset_iff)
  by (simp add: lbd_sub image_subset_iff)

lemma ul_closure:
  "is_closure (Pow X) ((\<lambda>A. ubd X A) \<circ> (\<lambda>A. lbd X A))"
  using gc_closure2 ul_galois by blast

lemma lu_closure:
  "is_closure (Pow X) ((\<lambda>A. lbd X A) \<circ> (\<lambda>A. ubd X A))"
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
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_sup X A s\<rbrakk> \<Longrightarrow> f s lb f`A"
  by (simp add: gc_anti1 is_supE1 is_supE7 lb_imageI subsetD)

lemma gc_sup_lb2:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_sup Y B s\<rbrakk> \<Longrightarrow> g s lb g`B"
  by (simp add: gc_anti2 is_supE1 is_supE7 lb_imageI subsetD)

lemma gc_reverse1:
  "\<lbrakk>galois_conn f X g Y;y \<in> Y; A \<subseteq> X; y lb f`A\<rbrakk> \<Longrightarrow> g y ub A"
  by (simp add: galois_conn_def in_mono lbE ub_def)

lemma gc_reverse11:
  "\<lbrakk>galois_conn f X g Y; x \<in> X; B \<subseteq> Y; x lb g`B\<rbrakk> \<Longrightarrow> f x ub B"
  by (meson gcD gcI gc_reverse1)

lemma gc_reverse2:
  "\<lbrakk>galois_conn f X g Y;y \<in> Y; A \<subseteq> X; g y ub A\<rbrakk> \<Longrightarrow> y lb f`A"
  by (simp add: galois_connD11 in_mono lb_imageI ubE)

lemma gc_reverse21:
  "\<lbrakk>galois_conn f X g Y; x \<in> X; B \<subseteq> Y; f x ub B\<rbrakk> \<Longrightarrow> x lb g`B"
  by (simp add: galois_connD21 in_mono lb_imageI ub_def)

lemma gc_sup_inf11:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; y \<in> Y; is_inf Y (f`A) i; is_sup X A s;y \<le> i\<rbrakk> \<Longrightarrow> y \<le> f s"
  by (simp add: galois_connD11 galois_connD12 gc_reverse1 is_infE6 is_supE1 is_supE4)

lemma gc_sup_inf12:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; x \<in> X; is_inf X (g`B) i; is_sup Y B s; x \<le> i\<rbrakk> \<Longrightarrow> x \<le> g s"
  by (simp add: galois_connD21 galois_connD22 gc_reverse11 is_infE6 is_supE1 is_supE4)

lemma gc_sup_inf21:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; y \<in> Y; is_inf Y (f`A) i; is_sup X A s; y \<le> f s\<rbrakk> \<Longrightarrow> y \<le> i"
  by (meson gc_sup_lb1 is_infD42 lb_iso1)

lemma gc_sup_inf22:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; x \<in> X; is_inf X (g`B) i; is_sup Y B s; x \<le> g s\<rbrakk> \<Longrightarrow> x \<le> i"
  by (meson gc_sup_lb2 is_infE4 lb_iso1)

lemma gc_sup_inf31:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_inf Y (f`A) i; is_sup X A s\<rbrakk> \<Longrightarrow> (\<forall>y \<in> Y. y \<le> i \<longleftrightarrow> y \<le> f s)"
  by (meson gc_sup_inf11 gc_sup_inf21)

lemma gc_sup_inf32:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_inf X (g`B) i; is_sup Y B s\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. x \<le> i \<longleftrightarrow> x \<le> g s)"
  by (meson gc_sup_inf12 gc_sup_inf22)

lemma gc_sup_inf41:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_inf Y (f`A) i; is_sup X A s\<rbrakk> \<Longrightarrow>f s = i"
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
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_extensive X ((dual_adj f X Y) \<circ> f)"
  by (simp add: extensiveI1 extrema_dual_cext1)

lemma im_le2:
  "f`X \<subseteq> Y \<Longrightarrow> y lb f`{x \<in> X. y \<le> f x}"
  by (metis (no_types, lifting) lb_imageI mem_Collect_eq)

lemma im_le3:
  "f`X \<subseteq> Y \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<in> lbd Y (f`{x \<in> X. y \<le> f x})"
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
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_extensive Y (f \<circ> (dual_adj f X Y))"
  by (simp add: extensiveI1 extrema_dual_cext2)

lemma adj_range: 
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> (dual_adj f X Y)`Y \<subseteq> X"
  apply(auto simp add:dual_adj_def)  by (metis (full_types) Collect_subset clatD21 is_supE1 sup_equality)

lemma extrema_dual_gc:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> galois_conn f X (dual_adj f X Y) Y"
  by(rule gcI; simp add:extrema_dual_antitone1c extrema_dual_cext1b extrema_dual_antitone2b extrema_dual_cext2b adj_range)


subsection SomeClosures

definition sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
 "sup_cl X A \<equiv> {x \<in> X. \<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup X E x}"

definition inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "inf_cl X A \<equiv> {x \<in> X. \<exists>E \<in> Pow A. E \<noteq> {} \<and> is_inf X E x}"

definition fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_inf_cl X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_inf X F x}"

definition fne_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_sup_cl X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup X F x}"

definition fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fin_inf_cl X A \<equiv> {x \<in> X. \<exists>F \<in> Fpow A. is_inf X F x}"


abbreviation sup_inv where  "sup_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup X E y)"

abbreviation inf_inv where "inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E y)"

abbreviation fne_inf_inv where "fne_inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E y)"

abbreviation fne_sup_inv where "fne_sup_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup X E y)"

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
  "x \<in> sup_cl X A \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup X E x)"
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
  "x \<in> fne_sup_cl X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup X F x)"
  by (simp add: fne_sup_cl_def)

lemma sup_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup X E x) \<Longrightarrow> x \<in> sup_cl X A"
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
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_sup X F x) \<Longrightarrow> x \<in> fne_sup_cl X A"
  by (simp add: fne_sup_cl_def)

lemma sup_cl_obtains:
  assumes "x \<in> sup_cl X A"
  obtains Ex where "Ex \<in> Pow A \<and> Ex \<noteq> {}  \<and>is_sup X Ex x"
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
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup X F x"
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
  "is_sup_cl X A\<equiv> (\<forall>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup X E x \<longrightarrow> x \<in> A)"

definition is_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E x \<longrightarrow> x \<in> A)"

definition is_fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fin_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Pow A \<and>  is_inf X E x \<longrightarrow> x \<in> A)"

definition is_fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fne_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E x \<longrightarrow> x \<in> A)"

lemma up_closed_supin_closed0:
  "is_ord_cl X A (\<le>) \<Longrightarrow> E \<in> Pow A \<Longrightarrow> E \<noteq> {} \<Longrightarrow> is_sup X E x  \<Longrightarrow> x \<in> A"
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
  have B0: "is_sup X {a} a"
    using A1 assms sup_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fne_sup_cl X A"
    apply(simp add:fne_sup_cl_def)
    using A1 B0 B2 assms by blast
qed

lemma sup_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. sup_cl X A)"
  by (meson PowD extensiveI1 sup_cl_extensive)

lemma inf_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. inf_cl X A)"
  by (meson PowD extensiveI1 inf_cl_extensive)

lemma fin_inf_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (meson PowD extensiveI1 fin_inf_cl_extensive)

lemma fne_inf_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (meson PowD extensiveI1 fne_inf_cl_extensive)

lemma fne_sup_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. fne_sup_cl X A)"
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
  "s \<in> sup_cl X (sup_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Pow (sup_cl X A) \<and> E \<noteq> {} \<and> is_sup X E s)"
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
  "s \<in> fne_sup_cl X (fne_sup_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_sup_cl X A) \<and> E \<noteq> {} \<and> is_sup X E s)"
  by (meson fne_sup_cl_imp1)

lemma sup_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (sup_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_sup X Ex x)"
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
  "\<lbrakk>E \<in> Pow (fne_sup_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_sup X Ex x)"
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
      let ?P="\<lambda>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow (?L1) \<and> E \<noteq> {} \<and> is_sup X E s"
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
      obtain se where B11A0:"is_sup X E se"
        using P1 by blast
      obtain ss where B11A1:"is_sup X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup X Ai ti)"
        using B1 by blast
      have B12:"?fE \<noteq> {}"
        by (simp add: P1)
      have B13:"is_sup X ((\<lambda>Ai. Sup X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_sup X (\<Union>?fE) ss"
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
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> E \<noteq> {} \<and> is_sup X E s"
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
      obtain se where B11A0:"is_sup X E se"
        using P1 by blast
      obtain ss where B11A1:"is_sup X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup X Ai ti)"
        using B1 by blast
      have B13:"is_sup X ((\<lambda>Ai. Sup X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_sup X (\<Union>?fE) ss"
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
  "is_idempotent (Pow X) (\<lambda>A. sup_cl X A)"
  by (simp add: is_idempotent_def sup_cl_idempotent)

lemma inf_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. inf_cl X A)"
  by (simp add: is_idempotent_def inf_cl_idempotent)

lemma fin_inf_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (simp add: is_idempotent_def fin_inf_cl_idempotent)

lemma fne_inf_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (simp add: is_idempotent_def fne_inf_cl_idempotent)

lemma fne_sup_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (simp add: is_idempotent_def fne_sup_cl_idempotent)

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
  "is_closure (Pow X) (\<lambda>A. sup_cl X A)"
  by (simp add: is_closure_def sup_cl_ext sup_cl_ide sup_cl_iso sup_cl_range)

lemma inf_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. inf_cl X A)"
  by (simp add: inf_cl_ext inf_cl_ide inf_cl_iso inf_cl_range is_closure_def)

lemma fin_inf_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (simp add: fin_inf_cl_ext fin_inf_cl_ide fin_inf_cl_iso fin_inf_cl_range is_closure_def)

lemma fne_inf_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (simp add: fne_inf_cl_ext fne_inf_cl_ide fne_inf_cl_iso fne_inf_cl_range is_closure_def)

lemma fne_sup_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (simp add: fne_sup_cl_ext fne_sup_cl_ide fne_sup_cl_iso fne_sup_cl_range is_closure_def)

lemma fne_sup_cl_dir:
  assumes A0:"is_sup_semilattice X" and A1:"A \<subseteq> X"
  shows  "is_dir (fne_sup_cl X A) (\<le>)"
proof-
  have B0:"\<And>a b. a \<in> fne_sup_cl X A \<and> b \<in> fne_sup_cl X A \<longrightarrow> (\<exists>c\<in>fne_sup_cl X A. a \<le> c \<and> b \<le> c)"
  proof
    fix a b assume A2:"a \<in> fne_sup_cl X A \<and> b \<in> fne_sup_cl X A "
    obtain Ea where A3:"Ea \<in> Fpow A \<and> Ea \<noteq> {} \<and> is_sup X Ea a"
      using A2 fne_sup_cl_imp1 by blast
    obtain Eb where A4:"Eb \<in> Fpow A \<and> Eb \<noteq> {} \<and> is_sup X Eb b"
      using A2 fne_sup_cl_imp1 by blast
    have B1:"Ea \<union> Eb \<in> Fpow A \<and> Ea \<union> Eb \<noteq> {}"
      by (metis A3 A4 Fpow_Pow_finite Int_Collect Pow_iff Un_empty Un_subset_iff finite_UnI)
    have B2:"(Ea \<union> Eb) \<subseteq> X"
      by (metis A1 A3 A4 Fpow_Pow_finite Int_Collect Pow_iff dual_order.trans sup.boundedI)
    obtain c where A5:"is_sup X (Ea \<union> Eb) c"
      by (metis A0 B1 B2 Fpow_Pow_finite Int_Collect bsup_finite2)
    have B3:"c \<in> fne_sup_cl X A \<and> a \<le> c \<and> b \<le> c"
      by (meson A3 A4 A5 B1 Un_upper2 fne_sup_cl_if1 is_supE1 is_sup_iso1 sup.cobounded1)
    show "(\<exists>c\<in>fne_sup_cl X A. a \<le> c \<and> b \<le> c)"
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
  "compactly_generated X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow (compact_elements X). is_sup X C x))"


lemma compactI:
  "\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))\<rbrakk> \<Longrightarrow> is_compact X c"
  by(simp add:is_compact_def)

lemma compactD:
  "\<lbrakk>is_compact X c; A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
  by(simp add:is_compact_def)

lemma compact_elements_mem_iff1:
  "x \<in> compact_elements X \<longleftrightarrow> is_compact X x"
  by (simp add: compact_elements_def)

lemma compactly_generatedD1:
  "compactly_generated X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>C \<in> Pow (compact_elements X). is_sup X C x)"
  by(simp add:compactly_generated_def)

lemma compactly_generatedI1:
  "(\<And>x. x \<in> X \<Longrightarrow>  (\<exists>C \<in> Pow (compact_elements X). is_sup X C x)) \<Longrightarrow> compactly_generated X"
  by(simp add:compactly_generated_def)

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
  assumes A0:"is_sup_semilattice X" and
          A1:"is_compact X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"c \<le> Sup X A" and
          A4:"is_dir A (\<le>)"
  shows "\<exists>a \<in> A. c \<le> a"
proof-
  obtain A0 a where A5:"a \<in> A \<and> a ub A0 \<and> A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0"
    using A1 A2 A3 A4 compactD1 by blast
  have A7:"a \<in> ubd X A0"
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
  have B6:"a \<in> ubd C {{x}}"
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
    have B11c:"E \<in> ubd C ?A"
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
  "sup_prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

definition inf_prime::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "inf_prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Inf X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

lemma sup_primeD1:
  "\<lbrakk>sup_prime X A; a \<in> X; b \<in> X; Sup X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:sup_prime_def)

lemma inf_primeD1:
  "\<lbrakk>inf_prime X A; a \<in> X; b \<in> X; Inf X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:inf_prime_def)

lemma sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Sup X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> sup_prime X A"
  by (simp add:sup_prime_def)

lemma inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Inf X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> inf_prime X A"
  by (simp add:inf_prime_def)

definition elem_sup_prime::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "elem_sup_prime X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x \<le> Sup X {a, b} \<longrightarrow> (x \<le> a \<or> x \<le> b))"

definition elem_inf_prime::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "elem_inf_prime X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x \<ge> Inf X {a, b} \<longrightarrow> (x \<ge> a \<or> x \<ge> b))"

lemma elem_sup_primeD1:
  "\<lbrakk>elem_sup_prime X x; a \<in> X; b \<in> X; x \<le> Sup X {a, b}\<rbrakk> \<Longrightarrow> (x \<le> a \<or> x \<le> b)"
  by(simp add:elem_sup_prime_def)

lemma elem_inf_primeD1:
  "\<lbrakk>elem_inf_prime X x; a \<in> X; b \<in> X; x \<ge> Inf X {a, b}\<rbrakk> \<Longrightarrow> (x \<ge> a \<or> x \<ge> b)"
  by(simp add:elem_inf_prime_def)

lemma elem_sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x \<le> Sup X {a, b}\<rbrakk> \<Longrightarrow> (x \<le> a \<or> x \<le> b)) \<Longrightarrow> elem_sup_prime X x"
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
  "\<lbrakk>x \<in> X;sup_prime X ([x)\<^sub>X); is_sup_semilattice X\<rbrakk> \<Longrightarrow> elem_sup_prime X x"
  by (metis elem_sup_prime_def lorcD12 lorcI1 ssupD4 sup_prime_def)

lemma elem_inf_primeI2:
  "\<lbrakk>x \<in> X; inf_prime X ((x]\<^sub>X); is_inf_semilattice X\<rbrakk> \<Longrightarrow> elem_inf_prime X x"
  by (metis elem_inf_prime_def rolcD12 rolcI1 sinfD4 inf_prime_def)


definition fin_sup_irr::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "fin_sup_irr X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Sup X {a, b} \<longrightarrow> (x = a \<or> x = b))" 

definition fin_inf_irr::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where 
  "fin_inf_irr X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Inf X {a, b} \<longrightarrow> x = a \<or> x =b)"

lemma fin_sup_irrD1:
  "\<lbrakk>fin_sup_irr X x; a \<in> X; b \<in> X; x=Sup X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_sup_irr_def)

lemma fin_inf_irrD1:
  "\<lbrakk>fin_inf_irr X x; a \<in> X; b \<in> X; x=Inf X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_inf_irr_def)

lemma fin_sup_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Sup X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_sup_irr X x"
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
(*(\<forall>a \<in> X. \<forall>b \<in> X. x \<le> Sup X {a, b} \<longrightarrow> (x \<le> a \<or> x \<le> b))*)
(*(\<forall>a \<in> X. \<forall>b \<in> X. x = Sup X {a, b} \<longrightarrow> (x = a \<or> x = b)*)

(*
  x \<le> a \<or> b \<longleftrightarrow> x \<and> (a \<or> b) = x \<longleftrightarrow> (x \<and> a) \<or> (x \<and> b) = x \<longleftrightarrow> (x \<and> a) = a \<or> (x \<and> b) = x \<longleftrightarrow> x \<le> a \<or> x \<le> b
*)

lemma elem_sup_primeI3:
  assumes A0:"distributive_lattice X" and A1:"x \<in> X" and A2: "fin_sup_irr X x"
  shows "elem_sup_prime X x"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> x \<le> Sup X {a, b} \<longrightarrow> (x \<le> a \<or> x \<le> b)"
  proof
    fix a b assume P:"a \<in> X \<and>b \<in> X \<and> x \<le> Sup X {a, b}"
    have B1:"x = Inf X {x, Sup X {a, b}}"
      using A0 A1 P distributive_lattice_def lattD42 le_inf1 ssupD4 by fastforce
    have B2:"... = Sup X {Inf X {x, a}, Inf X {x, b}}"
      by (simp add: A0 A1 P distr_latticeD3)
    have B3:"x = Inf X {x, a} \<or> x = Inf X {x, b}"
      by (metis A0 A1 A2 B1 B2 P distributive_lattice_def fin_sup_irr_def lattD41 sinfD4)
    show "x \<le>a \<or> x \<le> b"
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


abbreviation pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "pfilter X A \<equiv> (is_filter X A) \<and> X \<noteq> A"

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
  "\<lbrakk>sup_prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma primefilterD2:
  "\<lbrakk>is_lattice X; sup_prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup X {a, b}) \<in> A)"
  by (metis doubleton_eq_iff filter_on_lattice_sup01)

lemma primefilterD3:
  "\<lbrakk>is_lattice X; sup_prime X F; pfilter X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  apply(auto simp add:sup_prime_def) apply (meson filterD2 filters_on_lattice_inf02 in_mono) using filterD21 by blast

lemma notprimeobtain:
  assumes A0:"is_lattice X" and A1:"pfilter X F" and A2:"\<not>(sup_prime X F)"
  obtains x y where "x \<in> X \<and> y \<in> X \<and> Sup X {x, y} \<in> F \<and> x \<notin> F \<and> y \<notin> F"
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
    have B4:"Inf X {Inf X {y1, y2}, a} \<le> Inf X {x1, x2}"
      by (smt (verit) A0 A1 A2 A3 B0 B2 binf_assoc1 binf_leI2 binf_leI3 filterD21 in_mono insert_commute lattD41 sinfD4)
    have B5:"\<exists>y \<in> F. Inf X {a, y} \<le> Inf X {x1, x2}"
      by (metis B3 B4 doubleton_eq_iff)
    show "Inf X {x1, x2} \<in> G"
      using A0 A3 B5 G_def lattD41 sinfD4 by auto
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
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> (Sup X {a, b}) \<in> F \<longrightarrow> (a \<in> F \<or> b \<in> F)"
  proof
    fix a b assume A3:" a \<in> X \<and> b \<in> X \<and> (Sup X {a, b}) \<in> F"
    have B1:"(([a)\<^sub>X) \<inter> ([b)\<^sub>X)) \<subseteq> F"
      apply(auto simp add:lorc_def)  by (meson A0 A1 A3 binary_supD4 filterD4 is_ord_clE1 lattD32 latt_iff ssupD4)
    have B2:"([a)\<^sub>X) \<subseteq> F \<or> ([b)\<^sub>X) \<subseteq> F"
      by (simp add: A2 A3 B1 lorc_filter)
    show "(a \<in> F \<or> b \<in> F)"
      using A3 B2 lorc_memI1 by blast
  qed
  show ?thesis
    by (simp add: B0 sup_prime_def)
qed


lemma primefilterI1:
  "\<lbrakk>is_lattice X;  pfilter X A; (\<forall>a b. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup X {a, b}) \<in> A)) \<rbrakk> \<Longrightarrow> sup_prime X A"
  by (simp add: sup_prime_def)

lemma primefilter_iff1:
  "is_lattice X \<Longrightarrow> ( sup_prime X A \<and> pfilter X A) \<longleftrightarrow> (pfilter X A \<and>  (\<forall>a \<in> X. \<forall>b \<in> X. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup X {a, b}) \<in> A)))"
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
  "\<lbrakk>pfilter X [a)\<^sub>X; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup X {x, y}\<rbrakk> \<Longrightarrow> a \<le> x \<or> a \<le> y)\<rbrakk> \<Longrightarrow> sup_prime X [a)\<^sub>X"
  by (metis lorcD12 lorcI1 sup_prime_def)

lemma proper_principal_prime2:
  "\<lbrakk>is_lattice X; pfilter X [a)\<^sub>X; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup X {x, y}\<rbrakk> \<Longrightarrow> a \<le> x \<or> a \<le> y)\<rbrakk> \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a = Sup X {x, y}\<rbrakk> \<Longrightarrow> a =x \<or> a=y)"
  by (metis binary_supD31 binary_supD32 is_supE1 lattD32 order_class.order_eq_iff)

lemma proper_principal_fin_irr:
  "\<lbrakk>is_lattice X; pfilter X [a)\<^sub>X; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup X {x, y}\<rbrakk> \<Longrightarrow> a \<le> x \<or> a \<le> y)\<rbrakk> \<Longrightarrow>fin_inf_irr (filters_on X) [a)\<^sub>X"
  by (simp add: prime_filter_irr3 proper_principal_prime)


lemma fin_irr_filter_prime:
  "\<lbrakk>distributive_lattice X;pfilter X F;fin_inf_irr (filters_on X) F\<rbrakk> \<Longrightarrow> inf_prime X F"
  by (meson distributive_lattice_def filterD4 inf_primeI1 is_ord_clE1 lattD41 rolcD1 rolc_inf_latticeD1)


lemma distr_lattice_maximal_prime:
  assumes A0:"distributive_lattice X" and A1:"is_maximal (pfilters_on X) F" 
  shows "sup_prime X F"
proof-
  have B0:"pfilter X F"
    using A1 maximalD1 by auto
  have P:"\<And>a b. a \<in> X \<and> b \<in> X \<and> Sup X {a, b} \<in> F \<and>  a \<notin> F \<longrightarrow> b \<in> F"
  proof
    fix a b assume A2:"a \<in> X \<and> b \<in> X \<and> Sup X {a, b} \<in> F \<and> a \<notin> F"
    let ?Fa="binary_filter_sup X F [a)\<^sub>X"
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
    obtain f c where B7:"f \<in> F \<and> c \<in> ([a)\<^sub>X) \<and> b \<ge> Inf X {f, c}"
      using B6 binary_filter_sup_obtains by blast
    have B8:"b = Sup X {b, Inf X {f, c}}"
      by (metis A0 A2 B0 B7 distributive_lattice_def filterD2 ge_sup2 lattD41 lorc_filter sinfD4 subset_iff)
    have B9:"... = Inf X {Sup X {b, f}, Sup X {b, c}}"
      by (meson A0 A2 B0 B7 distr_latticeD1 filterD21 lorcD11)
    have B10:"Sup X {b, f} \<in> F \<and> Sup X {b, c} \<in> ([a)\<^sub>X) \<and> b = Inf X {Sup X {b, f}, Sup X {b, c}}"
      by (metis A0 A2 B0 B7 B8 B9 distributive_lattice_def filter_on_lattice_sup01 lorc_filter)
    let ?f="Sup X {b, f}" and ?c="Sup X {b, c}"
    have B11:"?c \<ge> a"
      using B10 lorcD12 by blast
    have B12:"b = Sup X {b, Inf X {?f, ?c}}"
      using A2 B10 bsup_idem1 by force
    have B13:"... = Inf X {Sup X {b, ?f}, Sup X {b, ?c}}"
      by (meson A0 A2 B0 B10 distr_latticeD1 filterD21 lorcD11)
    have B14:"... \<ge> Inf X {?f, Sup X {b, a}}"
      by (smt (verit, ccfv_threshold) A0 A2 B0 B10 B11 B7 binf_leI5 bsup_assoc1 distributive_lattice_def dual_order.refl filterD21 insert_commute latt_ge_iff1 latt_iff lorcD11)
    have B15:"... \<in> F"
      by (smt (verit, ccfv_SIG) A0 A2 B0 B10 B14 distributive_lattice_def filterD21 filter_finf_closed1 insert_commute latt_ge_iff1 latt_iff lattice_absorb1 lorcD11)
    show "b \<in> F"
      using B12 B13 B15 by presburger
  qed
  show ?thesis
    by (meson P sup_primeI1)
qed


 

end

