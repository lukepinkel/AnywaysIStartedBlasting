theory FiltersAndIdeals
  imports Main "./Posets_Trimmed"
begin


locale system_of_sets = 
  fixes X::"'X set" and A::"'X set set"
  assumes "A \<in> Pow(Pow X)"

locale pi_system = system_of_sets + 
  assumes f_int_closed[intro]:"\<And>a1 a2. a1 \<in> A  \<Longrightarrow>  a2 \<in> A \<Longrightarrow>  a1 \<inter> a2 \<in> A "

definition FinPow::"'X set \<Rightarrow> 'X set set" where
  "FinPow(X) = {A \<in> Pow X. finite A}"

lemma (in pi_system) inter_finite[intro]:
  assumes "finite I" "I \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow>  E i \<in> A"
  shows "(\<Inter>i\<in>I. E i) \<in> A"      
  using assms by (induct rule: finite_ne_induct) auto (*this is okay for some reason*)

(*
declare[[simp_trace]]

lemma inter_finite2:  
  fixes X::"'X set" and A::"'X set set"
  assumes A1:"A \<in> Pow(Pow X)" and
          A2[intro]:"\<And>a1 a2. a1 \<in> A  \<Longrightarrow>  a2 \<in> A \<Longrightarrow>  a1 \<inter> a2 \<in> A " and
          A3:"finite I" and
          A4:"I \<noteq> {}" and
          A5: "\<And>i. i \<in> I \<Longrightarrow>  E i \<in> A"
  shows "(\<Inter>i\<in>I. E i) \<in> A" 
  using A1 A2 A3 A4 A4 by (induct rule: finite_ne_induct) auto (*
      this fails
    *)
 *)      








end