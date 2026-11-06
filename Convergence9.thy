theory Convergence9
  imports Posets9
begin



context powerset
begin

abbreviation pfilters::"'a set set set"
  where "pfilters \<equiv> {F. pow.pfilter F}"

abbreviation finer_ultrafilters::"'a set set \<Rightarrow> 'a set set set"
  where "finer_ultrafilters \<F> \<equiv> {\<U>. ultrafilter \<U> \<and> \<F> \<subseteq> \<U>}"

definition ClN::"('a \<times> 'a set) set \<Rightarrow> ('a set \<times> 'a) set"
  where "ClN N = {(B, x). B \<in> Pow X \<and> x \<in> X \<and> {B} # N``{x}}"

definition NCl::"('a set \<times> 'a) set \<Rightarrow> ('a \<times> 'a set) set"
  where "NCl Cl = {(x, A). A \<in> Pow X \<and> x \<in> X \<and> {A} # (dual Cl)``{x}}"

definition NAdh::"('a set set \<times> 'a) set \<Rightarrow> ('a \<times> 'a set) set"
  where "NAdh Adh = {(x, A). A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>\<in>pfilters. (\<E>, x) \<in> Adh \<longrightarrow> {A} # \<E>)}"

definition AdhN::"('a \<times> 'a set) set \<Rightarrow> ('a set set \<times> 'a) set"
  where "AdhN N = {(\<E>, x). \<E> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> (x, A) \<in> N \<longrightarrow> {A} # \<E>)}"

definition AdhCl::"('a set \<times> 'a) set \<Rightarrow> ('a set set \<times> 'a) set"
  where "AdhCl Cl = {(\<F>, x). \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClAdh::"('a set set \<times> 'a) set \<Rightarrow> ('a set \<times> 'a) set"
  where "ClAdh Adh = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Adh)}"

definition NLim::"('a set set \<times> 'a) set \<Rightarrow> ('a \<times> 'a set) set"
  where "NLim Lim = {(x, A). A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters \<and> (\<E>, x) \<in> Lim \<longrightarrow> A \<in> \<E>)}"

definition LimN::"('a \<times> 'a set) set \<Rightarrow> ('a set set \<times> 'a) set"
  where "LimN N = {(\<E>, x). \<E> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A\<in>Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>)}"

definition LimCl::"('a set \<times> 'a) set \<Rightarrow> ('a set set \<times> 'a) set"
  where "LimCl Cl = {(\<F>, x). \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> {A} # \<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClLim::"('a set set \<times> 'a) set \<Rightarrow> ('a set \<times> 'a) set"
  where "ClLim Lim = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim)}"

definition AdhLim::"('a set set \<times> 'a) set \<Rightarrow> ('a set set \<times> 'a) set"
  where "AdhLim Lim = {(\<F>, x). \<F> \<in> pfilters \<and> x \<in> X \<and> (\<exists>\<G>\<in>pfilters. \<G> # \<F> \<and> (\<G>, x) \<in> Lim)}"

definition LimAdh::"('a set set \<times> 'a) set \<Rightarrow> ('a set set \<times> 'a) set"
  where "LimAdh Adh = {(\<F>, x). \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters \<and> \<G> # \<F> \<longrightarrow> (\<G>, x) \<in> Adh)}"

definition centered::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "centered q \<longleftrightarrow> (\<forall>x. x \<in> X \<longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> q)"

definition isoconv::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "isoconv q \<longleftrightarrow> (\<forall>\<G> \<F> x. \<G> \<in> pfilters \<and> (\<F>, x) \<in> q \<and> \<F> \<subseteq> \<G> \<longrightarrow> (\<G>, x) \<in> q)"

definition onpconv::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "onpconv q \<longleftrightarrow> (\<forall>x. x \<in> X \<longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q)"

definition ufdetconv::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "ufdetconv q \<longleftrightarrow> (\<forall>\<F> x. (x \<in> X \<and> \<F> \<in> pfilters \<and> (\<forall>\<U>. \<U> \<in> finer_ultrafilters \<F> \<longrightarrow> (\<U>, x) \<in> q)) \<longrightarrow> (\<F>, x) \<in> q)"

definition antiadh::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "antiadh Adh \<longleftrightarrow> (\<forall>\<G> \<F> x. \<G> \<in> pfilters \<and> (\<F>, x) \<in> Adh \<and> \<G> \<subseteq> \<F> \<longrightarrow> (\<G>, x) \<in> Adh)"

definition ufdetadh::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "ufdetadh Adh \<longleftrightarrow> (\<forall>\<F>. \<F> \<in> pfilters \<longrightarrow> Adh``{\<F>} = \<Union>{Adh``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>})"

definition prdetadh::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "prdetadh Adh \<longleftrightarrow> (\<forall>\<F>. \<F> \<in> pfilters \<longrightarrow> Adh``{\<F>} = \<Inter>{Adh``{lcro subset_order (Pow X) F}|F. F \<in> \<F>})"

definition isconvs::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "isconvs q \<longleftrightarrow> q \<subseteq> pfilters \<times> X"

definition ispsmap::"('a \<times> 'a set) set \<Rightarrow> bool"
  where "ispsmap N \<longleftrightarrow> N \<subseteq> X \<times> Pow X"

definition isspmap::"('a set \<times> 'a) set \<Rightarrow> bool"
  where "isspmap Cl \<longleftrightarrow> Cl \<subseteq> Pow X \<times> X"

definition is_gconv::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "is_gconv q \<longleftrightarrow> isconvs q \<and> centered q \<and> isoconv q"

abbreviation gconvs::"('a set set \<times> 'a) set set"
  where "gconvs \<equiv> {q. is_gconv q}"

definition is_prtop::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "is_prtop q \<longleftrightarrow> isconvs q \<and> centered q \<and> isoconv q \<and> onpconv q"

abbreviation prtops::"('a set set \<times> 'a) set set"
  where "prtops \<equiv> {q. is_prtop q}"

definition is_pseudotop::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "is_pseudotop q \<longleftrightarrow> isconvs q \<and> centered q \<and> isoconv q \<and> ufdetconv q"

definition pseudotop_adh::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "pseudotop_adh Adh \<longleftrightarrow> isconvs Adh \<and> centered Adh \<and> ufdetadh Adh"

definition prdet_adh::"('a set set \<times> 'a) set \<Rightarrow> bool"
  where "prdet_adh Adh \<longleftrightarrow> isconvs Adh \<and> prdetadh Adh"

definition prtop_nh::"('a \<times> 'a set) set \<Rightarrow> bool"
  where "prtop_nh N \<longleftrightarrow> (\<forall>x\<in>X. N``{x} \<in> pfilters) \<and> (\<forall>A x. x \<in> X \<and> A \<in> Pow X \<and> (x, A) \<in> N \<longrightarrow> x \<in> A)"

definition prtop_cl::"('a set \<times> 'a) set \<Rightarrow> bool"
  where "prtop_cl Cl \<longleftrightarrow> (Cl``{{}} = {}) \<and> (\<forall>A\<in>Pow X. A \<subseteq> Cl``{A}) \<and> (\<forall>A\<in>Pow X. \<forall>B\<in>Pow X. Cl``{A \<union> B} = Cl``{A} \<union> Cl``{B})"

definition iso_spmap::"('a set \<times> 'a) set \<Rightarrow> bool"
  where "iso_spmap Cl \<longleftrightarrow> isotone subset_order (Pow X) subset_order (\<lambda>A. Cl``{A})"

definition iso_psmap::"('a \<times> 'a set) set \<Rightarrow> bool"
  where "iso_psmap N \<longleftrightarrow> (\<forall>x\<in>X. up_closed subset_order (Pow X) (N``{x}))"


lemma ClN_memI1:"\<lbrakk>B \<in> Pow X; x \<in> X; {B} # N``{x}\<rbrakk> \<Longrightarrow> (B, x) \<in> ClN N"
  and ClN_Im_memI1:"\<lbrakk>B \<in> Pow X; x \<in> X; {B} # N``{x}\<rbrakk> \<Longrightarrow> x \<in> (ClN N)``{B}"
  and ClN_memD1:"(B, x) \<in> ClN N \<Longrightarrow> B \<in> Pow X \<and> x \<in> X \<and> {B} # N``{x}"
  and ClN_Im_memD1:"x \<in> (ClN N)``{B} \<Longrightarrow> B \<in> Pow X \<and> x \<in> X \<and> {B} # N``{x}"
  by (simp_all add:ClN_def)

lemma NCl_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; {A} # (dual Cl)``{x}\<rbrakk> \<Longrightarrow> (x, A) \<in> NCl Cl"
  and NCl_Im_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; {A} # (dual Cl)``{x}\<rbrakk> \<Longrightarrow> A \<in> (NCl Cl)``{x}"
  and NCl_memD:"(x, A) \<in> NCl Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> {A} # (dual Cl)``{x}"
  and NCl_Im_memD:"A \<in> (NCl Cl)``{x} \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> {A} # (dual Cl)``{x}"
  by (simp_all add:NCl_def)

lemma NCl_space:"NCl Cl \<subseteq> X \<times> Pow X"
  by (auto simp:NCl_def)

lemma NAdh_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<And>\<E>. \<lbrakk>\<E> \<in> pfilters; (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A} # \<E>\<rbrakk> \<Longrightarrow> (x, A) \<in> NAdh Adh"
  and NAdh_Im_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<And>\<E>. \<lbrakk>\<E> \<in> pfilters; (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A} # \<E>\<rbrakk> \<Longrightarrow> A \<in> (NAdh Adh)``{x}"
  and NAdh_memD1:"(x, A) \<in> NAdh Adh \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters \<and> (\<E>, x) \<in> Adh \<longrightarrow> {A} # \<E>)"
  and NAdh_memD2:"\<lbrakk>(x, A) \<in> NAdh Adh; \<E> \<in> pfilters; (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A} # \<E>"
  and NAdh_Im_memD:"A \<in> (NAdh Adh)``{x} \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters \<and> (\<E>, x) \<in> Adh \<longrightarrow> {A} # \<E>)"
  by (simp_all add:NAdh_def)

lemma AdhN_memI:"\<lbrakk>\<E> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> {A} # \<E>\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> AdhN N"
  and AdhN_memD:"(\<E>, x) \<in> AdhN N \<Longrightarrow> \<E> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> (x, A) \<in> N \<longrightarrow> {A} # \<E>)"
  and AdhN_Im_memI:"\<lbrakk>\<E> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> {A} # \<E>\<rbrakk> \<Longrightarrow> x \<in> (AdhN N)``{\<E>}"
  and AdhN_Im_memD:"x \<in> (AdhN N)``{\<E>} \<Longrightarrow> \<E> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> (x, A) \<in> N \<longrightarrow> {A} # \<E>)"
  by (simp_all add:AdhN_def)

lemma AdhCl_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> AdhCl Cl"
  and AdhCl_memD:"(\<F>, x) \<in> AdhCl Cl \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl)"
  and AdhCl_Im_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl\<rbrakk> \<Longrightarrow> x \<in> (AdhCl Cl)``{\<F>}"
  and AdhCl_Im_memD:"x \<in> (AdhCl Cl)``{\<F>} \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl)"
  by (simp_all add:AdhCl_def)

lemma ClAdh_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> (A, x) \<in> ClAdh Adh"
  and ClAdh_memD:"(A, x) \<in> ClAdh Adh \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Adh)"
  and ClAdh_Im_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> x \<in> (ClAdh Adh)``{A}"
  and ClAdh_Im_memD:"x \<in> (ClAdh Adh)``{A} \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Adh)"
  by (simp_all add:ClAdh_def)

lemma NLim_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<And>\<E>. \<lbrakk>\<E> \<in> pfilters; (\<E>, x) \<in> Lim\<rbrakk> \<Longrightarrow> A \<in> \<E>\<rbrakk> \<Longrightarrow> (x, A) \<in> NLim Lim"
  and NLim_memD:"(x, A) \<in> NLim Lim \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters \<and> (\<E>, x) \<in> Lim \<longrightarrow> A \<in> \<E>)"
  and NLim_Im_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<And>\<E>. \<lbrakk>\<E> \<in> pfilters; (\<E>, x) \<in> Lim\<rbrakk> \<Longrightarrow> A \<in> \<E>\<rbrakk> \<Longrightarrow> A \<in> (NLim Lim)``{x}"
  and NLim_Im_memD:"A \<in> (NLim Lim)``{x} \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters \<and> (\<E>, x) \<in> Lim \<longrightarrow> A \<in> \<E>)"
  by (simp_all add:NLim_def)

lemma LimN_memI:"\<lbrakk>\<E> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> A \<in> \<E>\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> LimN N"
  and LimN_memD:"(\<E>, x) \<in> LimN N \<Longrightarrow> \<E> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A\<in>Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>)"
  and LimN_Im_memI:"\<lbrakk>\<E> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> A \<in> \<E>\<rbrakk> \<Longrightarrow> x \<in> (LimN N)``{\<E>}"
  and LimN_Im_memD:"x \<in> (LimN N)``{\<E>} \<Longrightarrow> \<E> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A\<in>Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>)"
  by (simp_all add:LimN_def)

lemma LimCl_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; {A} # \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> LimCl Cl"
  and LimCl_memD:"(\<F>, x) \<in> LimCl Cl \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> {A} # \<F> \<longrightarrow> (A, x) \<in> Cl)"
  and LimCl_Im_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<And>A. \<lbrakk>A \<in> Pow X; {A} # \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl\<rbrakk> \<Longrightarrow> x \<in> (LimCl Cl)``{\<F>}"
  and LimCl_Im_memD:"x \<in> (LimCl Cl)``{\<F>} \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>A. A \<in> Pow X \<and> {A} # \<F> \<longrightarrow> (A, x) \<in> Cl)"
  by (simp_all add:LimCl_def)

lemma ClLim_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim\<rbrakk> \<Longrightarrow> (A, x) \<in> ClLim Lim"
  and ClLim_memD:"(A, x) \<in> ClLim Lim \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim)"
  and ClLim_Im_memI:"\<lbrakk>A \<in> Pow X; x \<in> X; \<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim\<rbrakk> \<Longrightarrow> x \<in> (ClLim Lim)``{A}"
  and ClLim_Im_memD:"x \<in> (ClLim Lim)``{A} \<Longrightarrow> A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim)"
  by (simp_all add:ClLim_def)

lemma AdhLim_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<exists>\<G>\<in>pfilters. \<G> # \<F> \<and> (\<G>, x) \<in> Lim\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> AdhLim Lim"
  and AdhLim_memD:"(\<F>, x) \<in> AdhLim Lim \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<exists>\<G>\<in>pfilters. \<G> # \<F> \<and> (\<G>, x) \<in> Lim)"
  and AdhLim_Im_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<exists>\<G>\<in>pfilters. \<G> # \<F> \<and> (\<G>, x) \<in> Lim\<rbrakk> \<Longrightarrow> x \<in> (AdhLim Lim)``{\<F>}"
  and AdhLim_Im_memD:"x \<in> (AdhLim Lim)``{\<F>} \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<exists>\<G>\<in>pfilters. \<G> # \<F> \<and> (\<G>, x) \<in> Lim)"
  by (simp_all add:AdhLim_def)

lemma LimAdh_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<And>\<G>. \<lbrakk>\<G> \<in> pfilters; \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> LimAdh Adh"
  and LimAdh_memD:"(\<F>, x) \<in> LimAdh Adh \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters \<and> \<G> # \<F> \<longrightarrow> (\<G>, x) \<in> Adh)"
  and LimAdh_Im_memI:"\<lbrakk>\<F> \<in> pfilters; x \<in> X; \<And>\<G>. \<lbrakk>\<G> \<in> pfilters; \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh\<rbrakk> \<Longrightarrow> x \<in> (LimAdh Adh)``{\<F>}"
  and LimAdh_Im_memD:"x \<in> (LimAdh Adh)``{\<F>} \<Longrightarrow> \<F> \<in> pfilters \<and> x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters \<and> \<G> # \<F> \<longrightarrow> (\<G>, x) \<in> Adh)"
  by (simp_all add:LimAdh_def)

lemma centeredI1:"(\<And>x. x \<in> X \<Longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> q) \<Longrightarrow> centered q"
  and centeredD1:"\<lbrakk>centered q; x \<in> X\<rbrakk> \<Longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> q"
  by (simp_all add:centered_def)

lemma centeredD2:"\<lbrakk>centered q; x \<in> X\<rbrakk> \<Longrightarrow> (dual q)``{x} \<noteq> {}"
  using centeredD1 by fastforce

lemma isoconvI1:"(\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters; (\<F>, x) \<in> q; \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q) \<Longrightarrow> isoconv q"
  and isoconvD1:"\<lbrakk>isoconv q; \<G> \<in> pfilters; (\<F>, x) \<in> q; \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q"
  unfolding isoconv_def by blast+

lemma isoconvI2:"(\<And>\<G> \<F> x. \<lbrakk>pow.pfilter \<G>; (\<F>, x) \<in> q; \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q) \<Longrightarrow> isoconv q"
  and isoconvI3:"(\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters; (\<F>, x) \<in> q; (\<F>, \<G>) \<in> subset_order\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q) \<Longrightarrow> isoconv q"
  unfolding isoconv_def by (simp, blast)+

lemma antiadhI1:"(\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters; (\<F>, x) \<in> Adh; \<G> \<subseteq> \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh) \<Longrightarrow> antiadh Adh"
  and antiadhD1:"\<lbrakk>antiadh Adh; \<G> \<in> pfilters; (\<F>, x) \<in> Adh; \<G> \<subseteq> \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh"
  unfolding antiadh_def by blast+

lemma onpconvI1:"(\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q) \<Longrightarrow> onpconv q"
  and onpconvD1:"\<lbrakk>onpconv q; x \<in> X\<rbrakk> \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q"
  by (simp_all add:onpconv_def)

lemma isgconvD1:"\<lbrakk>isconvs q; (\<E>, x) \<in> q\<rbrakk> \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
  and isconvsI1:"(\<And>\<E> x. (\<E>, x) \<in> q \<Longrightarrow> \<E> \<in> pfilters \<and> x \<in> X) \<Longrightarrow> isconvs q"
  by (auto simp:isconvs_def)

lemma ispsmapD2:"\<lbrakk>ispsmap N; (x, V) \<in> N\<rbrakk> \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  and ispsmapI1:"(\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X) \<Longrightarrow> ispsmap N"
  by (auto simp:ispsmap_def)

lemma isspmapD1:"\<lbrakk>isspmap Cl; (V, x) \<in> Cl\<rbrakk> \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  and isspmapI1:"(\<And>V x. (V, x) \<in> Cl \<Longrightarrow> V \<in> Pow X \<and> x \<in> X) \<Longrightarrow> isspmap Cl"
  by (auto simp:isspmap_def)

lemma iso_spmapI1:"(\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}) \<Longrightarrow> iso_spmap Cl"
  by (auto simp:iso_spmap_def isotone_def)

lemma iso_spmapD1:
  assumes A0:"iso_spmap Cl" and A2:"B \<in> Pow X" and A3:"A \<subseteq> B"
  shows "Cl``{A} \<subseteq> Cl``{B}"
proof-
  have "A \<in> Pow X"
    using A2 A3 by auto
  then show ?thesis
    using A0 A2 A3 by (simp add:iso_spmap_def isotone_def)
qed

lemma iso_spmapD2:
  assumes A0:"isspmap Cl" and A1:"iso_spmap Cl"
  shows "up_closed subset_order (Pow X) ((dual Cl)``{x})"
proof(rule up_closedI)
  fix A B assume A2:"A \<in> (dual Cl)``{x}" and A3:"B \<in> Pow X" and A4:"(A, B) \<in> subset_order"
  then obtain B0:"(A, x) \<in> Cl" and B1:"A \<subseteq> B"
    by simp
  then have "Cl``{A} \<subseteq> Cl``{B}"
    using A1 A3 iso_spmapD1 by blast
  then show "B \<in> (dual Cl)``{x}"
    using B0 by blast
qed

lemma iso_psmapI1:"(\<And>x. x \<in> X \<Longrightarrow> up_closed subset_order (Pow X) (N``{x})) \<Longrightarrow> iso_psmap N"
  and iso_psmapD2:"\<lbrakk>iso_psmap N; x \<in> X\<rbrakk> \<Longrightarrow> up_closed subset_order (Pow X) (N``{x})"
  by (simp_all add:iso_psmap_def)

lemma iso_psmapD3:"\<lbrakk>iso_psmap N; x \<in> X; A \<in> N``{x}; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> N``{x}"
  using up_closedD[OF iso_psmapD2] by simp

lemma iso_psmapD1:
  assumes A0:"ispsmap N" and A1:"iso_psmap N"
  shows "iso_spmap (dual N)"
proof(rule iso_spmapI1)
  fix A B assume A2:"B \<in> Pow X" and A3:"A \<subseteq> B"
  show "(dual N)``{A} \<subseteq> (dual N)``{B}"
  proof
    fix x assume A4:"x \<in> (dual N)``{A}"
    then obtain B0:"(x, A) \<in> N" and B1:"x \<in> X"
      using A0 ispsmapD2 by blast
    then have "B \<in> N``{x}"
      using A1 A2 A3 iso_psmapD3 by simp
    then show "x \<in> (dual N)``{B}"
      by simp
  qed
qed

lemma iso_spmapD3:
  assumes A0:"isspmap Cl" and A1:"iso_spmap Cl"
  shows "iso_psmap (dual Cl)"
  by (rule iso_psmapI1) (simp add:iso_spmapD2[OF A0 A1])

lemma ufdetconvI1:
  "(\<And>\<F> x. \<lbrakk>x \<in> X; \<F> \<in> pfilters; \<And>\<U>. \<U> \<in> finer_ultrafilters \<F> \<Longrightarrow> (\<U>, x) \<in> q\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> q) \<Longrightarrow> ufdetconv q"
  and ufdetconvD1:"\<lbrakk>ufdetconv q; x \<in> X; \<F> \<in> pfilters; \<And>\<U>. \<U> \<in> finer_ultrafilters \<F> \<Longrightarrow> (\<U>, x) \<in> q\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> q"
  by (simp_all add:ufdetconv_def)

lemma ufdetadhI1:"(\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> Adh``{\<F>} = \<Union>{Adh``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>}) \<Longrightarrow> ufdetadh Adh"
  and ufdetadhD1:"\<lbrakk>ufdetadh Adh; \<F> \<in> pfilters\<rbrakk> \<Longrightarrow> Adh``{\<F>} = \<Union>{Adh``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>}"
  by (simp_all add:ufdetadh_def)

lemma prdetadhI1:"(\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> Adh``{\<F>} = \<Inter>{Adh``{lcro subset_order (Pow X) F}|F. F \<in> \<F>}) \<Longrightarrow> prdetadh Adh"
  and prdetadhD1:"\<lbrakk>prdetadh Adh; \<F> \<in> pfilters\<rbrakk> \<Longrightarrow> Adh``{\<F>} = \<Inter>{Adh``{lcro subset_order (Pow X) F}|F. F \<in> \<F>}"
  by (simp_all add:prdetadh_def)

lemma prtop_clD:
  assumes A0:"prtop_cl Cl"
  shows prtop_clD1:"Cl``{{}} = {}" and
        prtop_clD2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}" and
        prtop_clD3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B} = Cl``{A} \<union> Cl``{B}" and
        prtop_clD4:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}"
proof-
  show P0:"Cl``{{}} = {}"
    using A0 by (simp add:prtop_cl_def)
  show P1:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
    using A0 by (simp add:prtop_cl_def)
  show P2:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B} = Cl``{A} \<union> Cl``{B}"
    using A0 by (simp add:prtop_cl_def)
  show P3:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}"
  proof-
    fix A B assume B0:"B \<in> Pow X" and AB:"A \<subseteq> B"
    then obtain B1:"A \<in> Pow X" and B2:"B - A \<in> Pow X" and B3:"B = (B - A) \<union> A"
      by blast
    then have "Cl``{B} = Cl``{B - A} \<union> Cl``{A}"
      using P2[of "B - A" A] by presburger
    then show "Cl``{A} \<subseteq> Cl``{B}"
      by blast
  qed
qed

lemma prtop_cl_iso:"prtop_cl Cl \<Longrightarrow> iso_spmap Cl"
  by (rule iso_spmapI1) (rule prtop_clD4)

lemma NCl_memI2:
  assumes A0:"A \<in> Pow X" and A1:"x \<in> X" and A2:"\<And>B. x \<in> Cl``{B} \<Longrightarrow> A \<inter> B \<noteq> {}"
  shows "(x, A) \<in> NCl Cl"
proof-
  have "{A} # (dual Cl)``{x}"
    using A2 by (auto simp:mesh_def)
  then show ?thesis
    using A0 A1 by (simp add:NCl_def)
qed

lemma NCl_memD2:"\<lbrakk>(x, A) \<in> NCl Cl; x \<in> Cl``{B}\<rbrakk> \<Longrightarrow> A \<inter> B \<noteq> {}"
  by (auto simp:NCl_def mesh_def)

lemma prdetadh_antitone:
  assumes A0:"prdet_adh Adh"
  shows "antiadh Adh"
proof(rule antiadhI1)
  fix \<G> \<F> x assume A1:"\<G> \<in> pfilters" and A2:"(\<F>, x) \<in> Adh" and A3:"\<G> \<subseteq> \<F>"
  have A4:"\<F> \<in> pfilters"
    using A0 A2 by (auto simp:prdet_adh_def isconvs_def)
  let ?UF="{Adh``{lcro subset_order (Pow X) A}|A. A \<in> \<F>}"
  let ?UG="{Adh``{lcro subset_order (Pow X) A}|A. A \<in> \<G>}"
  have B0:"Adh``{\<G>} = \<Inter>?UG"
    using A0 A1 by (simp add:prdet_adh_def prdetadh_def)
  have B1:"Adh``{\<F>} = \<Inter>?UF"
    using A0 A4 by (simp add:prdet_adh_def prdetadh_def)
  have B2:"?UG \<subseteq> ?UF"
    using A3 by blast
  have B3:"Adh``{\<F>} = \<Inter>?UF"
    by (simp add: B1)
  also have B4:"... \<subseteq> \<Inter>?UG"
    by (simp add: B2 Inf_superset_mono)
  also have B3:"... = Adh``{\<G>}"
    using B0 by auto
  then show "(\<G>, x) \<in> Adh"
    using A2 calculation by auto
qed

section \<open>Between Convergence Relations\<close>

lemma set_pfilter_base:"pow.pfilter F \<Longrightarrow> F \<subseteq> Pow X"
  and set_pfilter_whole:"pow.pfilter F \<Longrightarrow> X \<in> F"
  and set_pfilter_up:"\<lbrakk>pow.pfilter F; A \<in> F; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F"
  and set_pfilter_Int:"\<lbrakk>pow.pfilter F; A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F"
  by (auto simp:set_pfilter_iff set_filter_iff)

lemma set_pfilter_mem_base:"\<lbrakk>pow.pfilter F; A \<in> F\<rbrakk> \<Longrightarrow> A \<subseteq> X"
  using set_pfilter_base by blast

lemma set_pfilter_lcro_sub:"\<lbrakk>pow.pfilter F; A \<in> F\<rbrakk> \<Longrightarrow> lcro subset_order (Pow X) A \<subseteq> F"
  using set_pfilter_up by (auto simp:lcro_iff)

lemma mesh_single_iff:"{A} # \<B> \<longleftrightarrow> (\<forall>B\<in>\<B>. A \<inter> B \<noteq> {})"
  by (simp add:mesh_def)

lemma pfilter_sub_mesh:"\<lbrakk>pow.pfilter G; F \<subseteq> G\<rbrakk> \<Longrightarrow> F # G"
  using mesh_sub[OF pfilter_mesh_self] by blast

lemma pfilter_mem_mesh:"\<lbrakk>pow.pfilter F; A \<in> F\<rbrakk> \<Longrightarrow> {A} # F"
  using pfilter_sub_mesh by blast

lemma pfilter_mesh_single_iff:
  assumes A0:"pow.pfilter F" and A1:"A \<subseteq> X"
  shows "{A} # F \<longleftrightarrow> X - A \<notin> F"
proof-
  have "{A} # F \<longleftrightarrow> A \<in> grill X F"
    using A1 mesh_iff_grill[of "{A}" F] by simp
  then show ?thesis
    using grill_pfilter_iff[OF A0 A1] by simp
qed

lemma mesh_lcro:
  assumes A0:"A \<subseteq> X" and A1:"\<A> # {A}"
  shows "\<A> # lcro subset_order (Pow X) A"
proof-
  have "\<And>a B. \<lbrakk>a \<in> \<A>; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<inter> B \<noteq> {}"
  proof-
    fix a B assume "a \<in> \<A>" and "B \<in> Pow X" and "A \<subseteq> B"
    then have "a \<inter> A \<noteq> {}"
      using A1 by (simp add:mesh_def)
    then show "a \<inter> B \<noteq> {}"
      using \<open>A \<subseteq> B\<close> by blast
  qed
  then show ?thesis
    by (simp add:mesh_def lcro_iff)
qed

lemma lcro_mesh_iff:"A \<subseteq> X \<Longrightarrow> \<A> # lcro subset_order (Pow X) A \<longleftrightarrow> \<A> # {A}"
  using mesh_lcro mesh_sub[of \<A> "lcro subset_order (Pow X) A" \<A> "{A}"] by (auto simp:lcro_iff)

lemma mesh_pfilter_finer:
  assumes A0:"pow.pfilter F" and A1:"A \<subseteq> X" and A2:"{A} # F"
  shows "\<exists>G. pow.pfilter G \<and> F \<subseteq> G \<and> A \<in> G"
proof-
  have B0:"\<And>B. B \<in> F \<Longrightarrow> A \<inter> B \<noteq> {}"
    using A2 by (simp add:mesh_def)
  have B1:"filter_on subset_order (Pow X) F"
    using A0 by (simp add:set_pfilter_iff)
  have B2:"F \<subseteq> pow.fsup F (lcro subset_order (Pow X) A)"
    using pow.fsup_ge1[OF B1 pow.lcro_filter] A1 by auto
  then show ?thesis
    using finer_pfilter[OF A0 A1 B0] by blast
qed

lemma mesh_pfilters_finer:
  assumes A0:"pow.pfilter F" and A1:"pow.pfilter G" and A2:"F # G"
  shows "\<exists>H. pow.pfilter H \<and> F \<subseteq> H \<and> G \<subseteq> H"
proof-
  have B0:"filter_on subset_order (Pow X) F" and B1:"filter_on subset_order (Pow X) G"
    using A0 A1 by (simp_all add:set_pfilter_iff)
  have B2:"{} \<notin> pow.fsup F G"
  proof
    assume "{} \<in> pow.fsup F G"
    then obtain a b where B3:"a \<in> F" and B4:"b \<in> G" and B5:"inf subset_order (Pow X) a b \<subseteq> {}"
      by (rule pow.fsupE) simp
    have "a \<subseteq> X" and "b \<subseteq> X"
      using B3 B4 set_pfilter_mem_base[OF A0] set_pfilter_mem_base[OF A1] by blast+
    then have "a \<inter> b \<subseteq> {}"
      using B5 by (simp add:inf_pow)
    then show False
      using A2 B3 B4 by (auto simp:mesh_def)
  qed
  have "pow.pfilter (pow.fsup F G)"
    using pow.fsup_filter[OF B0 B1] B2 by (simp add:set_pfilter_iff)
  then show ?thesis
    using pow.fsup_ge1[OF B0 B1] pow.fsup_ge2[OF B0 B1] by blast
qed

lemma lcro_pfilter_iff:"A \<subseteq> X \<Longrightarrow> pow.pfilter (lcro subset_order (Pow X) A) \<longleftrightarrow> A \<noteq> {}"
  using set_lcro_pfilter set_pfilter_ne[of "lcro subset_order (Pow X) A" A] by (auto simp:lcro_iff)


lemma Cl_to_Nh:
  assumes xmem:"x \<in> X"
  shows Cl_to_Nh1:"(NCl Cl)``{x} = grill X ((dual Cl)``{x})" and
        Cl_to_Nh2:"\<And>A. (x, A) \<in> NCl Cl \<longleftrightarrow> A \<in> grill X ((dual Cl)``{x})"
proof-
  show P0:"(NCl Cl)``{x} = grill X ((dual Cl)``{x})"
    using xmem by (auto simp:NCl_def grill_iff mesh_def Int_commute)
  show P1:"\<And>A. (x, A) \<in> NCl Cl \<longleftrightarrow> A \<in> grill X ((dual Cl)``{x})"
    using P0 by auto
qed

lemma Nh_to_Cl:
  assumes xmem:"x \<in> X"
  shows Nh_to_Cl1:"(dual (ClN N))``{x} = grill X (N``{x})" and
        Nh_to_Cl2:"\<And>A. (A, x) \<in> ClN N \<longleftrightarrow> A \<in> grill X (N``{x})"
proof-
  show P0:"(dual (ClN N))``{x} = grill X (N``{x})"
    using xmem by (auto simp:ClN_def grill_iff mesh_def Int_commute)
  show P1:"\<And>A. (A, x) \<in> ClN N \<longleftrightarrow> A \<in> grill X (N``{x})"
    using P0 by auto
qed

lemma Nh_to_Adh:
  assumes A0:"ispsmap N"
  shows Nh_to_Adh1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> x \<in> (AdhN N)``{\<E>} \<longleftrightarrow> N``{x} # \<E>" and
        Nh_to_Adh2:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> AdhN N \<longleftrightarrow> N``{x} # \<E>" and
        Nh_to_Adh3:"prdet_adh (AdhN N)"
proof-
  show P0:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> x \<in> (AdhN N)``{\<E>} \<longleftrightarrow> N``{x} # \<E>"
  proof-
    fix \<E> x assume A1:"x \<in> X" and A2:"\<E> \<in> pfilters"
    have "\<And>A. (x, A) \<in> N \<Longrightarrow> A \<in> Pow X"
      using A0 by (simp add:ispsmap_def subset_iff)
    then show "x \<in> (AdhN N)``{\<E>} \<longleftrightarrow> N``{x} # \<E>"
      using A1 A2 by (auto simp:AdhN_def mesh_def)
  qed
  show P1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> AdhN N \<longleftrightarrow> N``{x} # \<E>"
    using P0 by simp
  have P2:"isconvs (AdhN N)"
    by (auto simp:isconvs_def AdhN_def)
  have P3:"prdetadh (AdhN N)"
  proof(rule prdetadhI1)
    fix \<F> assume A1:"\<F> \<in> pfilters"
    then have P4:"pow.pfilter \<F>"
      by simp
    show "(AdhN N)``{\<F>} = \<Inter>{(AdhN N)``{lcro subset_order (Pow X) F}|F. F \<in> \<F>}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof
        fix x assume A2:"x \<in> ?L"
        then obtain B0:"x \<in> X" and B1:"N``{x} # \<F>"
          using A1 P0 by (auto simp:AdhN_def)
        have B2:"\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> (AdhN N)``{lcro subset_order (Pow X) A}"
        proof-
          fix A assume A3:"A \<in> \<F>"
          then obtain B3:"A \<subseteq> X" and B4:"A \<noteq> {}"
            using set_pfilter_mem_base[OF P4] set_pfilter_ne[OF P4] by blast+
          then have B5:"lcro subset_order (Pow X) A \<in> pfilters"
            using set_lcro_pfilter by simp
          have "N``{x} # {A}"
            using B1 A3 mesh_sub by blast
          then have "N``{x} # lcro subset_order (Pow X) A"
            using mesh_lcro[OF B3] by blast
          then show "x \<in> (AdhN N)``{lcro subset_order (Pow X) A}"
            using P0[OF B0 B5] by blast
        qed
        then show "x \<in> ?R"
          by blast
      qed
    next
      show "?R \<subseteq> ?L"
      proof
        fix x assume A2:"x \<in> ?R"
        then have B0:"\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> (AdhN N)``{lcro subset_order (Pow X) A}"
          by blast
        have B1:"x \<in> X"
          using B0[OF set_pfilter_whole[OF P4]] by (auto simp:AdhN_def)
        have B2:"\<And>A. A \<in> \<F> \<Longrightarrow> N``{x} # {A}"
        proof-
          fix A assume A3:"A \<in> \<F>"
          then obtain B3:"A \<subseteq> X" and B4:"A \<noteq> {}"
            using set_pfilter_mem_base[OF P4] set_pfilter_ne[OF P4] by blast+
          then have B5:"lcro subset_order (Pow X) A \<in> pfilters"
            using set_lcro_pfilter by simp
          have "N``{x} # lcro subset_order (Pow X) A"
            using B0[OF A3] P0[OF B1 B5] by blast
          then show "N``{x} # {A}"
            using lcro_mesh_iff[OF B3] by blast
        qed
        then have "N``{x} # \<F>"
          by (simp add:mesh_def)
        then show "x \<in> ?L"
          using P0[OF B1 A1] by blast
      qed
    qed
  qed
  show "prdet_adh (AdhN N)"
    using P2 P3 by (simp add:prdet_adh_def)
qed

lemma Adh_to_Nh:
  assumes A0:"isconvs Adh"
  shows Adh_to_Nh1:"\<And>x. \<lbrakk>(dual Adh)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> (NAdh Adh)``{x} = \<Inter>{grill X \<E>|\<E>. (\<E>, x) \<in> Adh}" and
        Adh_to_Nh2:"iso_psmap (NAdh Adh)"
proof-
  show P0:"\<And>x. \<lbrakk>(dual Adh)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> (NAdh Adh)``{x} = \<Inter>{grill X \<E>|\<E>. (\<E>, x) \<in> Adh}"
  proof-
    fix x assume A1:"(dual Adh)``{x} \<noteq> {}" and A2:"x \<in> X"
    have B0:"\<And>\<E>. (\<E>, x) \<in> Adh \<Longrightarrow> \<E> \<in> pfilters"
      using A0 by (auto simp:isconvs_def)
    show "(NAdh Adh)``{x} = \<Inter>{grill X \<E>|\<E>. (\<E>, x) \<in> Adh}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof
        fix A assume A3:"A \<in> ?L"
        then obtain B1:"A \<in> Pow X" and B2:"\<And>\<E>. \<lbrakk>\<E> \<in> pfilters; (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A} # \<E>"
          by (simp add:NAdh_def)
        have "\<And>\<E>. (\<E>, x) \<in> Adh \<Longrightarrow> A \<in> grill X \<E>"
        proof-
          fix \<E> assume "(\<E>, x) \<in> Adh"
          then have "{A} # \<E>"
            using B0 B2 by blast
          then show "A \<in> grill X \<E>"
            using B1 by (auto simp:grill_iff mesh_def Int_commute)
        qed
        then show "A \<in> ?R"
          by blast
      qed
    next
      show "?R \<subseteq> ?L"
      proof
        fix A assume A3:"A \<in> ?R"
        obtain \<E> where B1:"(\<E>, x) \<in> Adh"
          using A1 by blast
        then have B2:"A \<in> grill X \<E>"
          using A3 by blast
        then have B3:"A \<in> Pow X"
          by (simp add:grill_iff)
        have "\<And>\<E>. (\<E>, x) \<in> Adh \<Longrightarrow> {A} # \<E>"
          using A3 by (auto simp:grill_iff mesh_def Int_commute)
        then show "A \<in> ?L"
          using A2 B3 by (simp add:NAdh_def)
      qed
    qed
  qed
  show P1:"iso_psmap (NAdh Adh)"
  proof(rule iso_psmapI1)
    fix x assume xmem:"x \<in> X"
    show "up_closed subset_order (Pow X) ((NAdh Adh)``{x})"
    proof(rule up_closedI)
      fix a b assume a0:"a \<in> (NAdh Adh)``{x}" and b0:"b \<in> Pow X" and ab0:"(a, b) \<in> subset_order"
      then have B0:"\<And>\<F>. \<lbrakk>\<F> \<in> pfilters; (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {a} # \<F>"
        by (simp add:NAdh_def)
      then have B1:"\<And>\<F>. \<lbrakk>\<F> \<in> pfilters; (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {b} # \<F>"
        using ab0 by (auto simp:mesh_def)
      then show "b \<in> (NAdh Adh)``{x}"
        using b0 xmem by (simp add:NAdh_def)
    qed
  qed
qed

lemma Nh_to_Lim:
  assumes A0:"ispsmap N"
  shows Nh_to_Lim1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> x \<in> (LimN N)``{\<E>} \<longleftrightarrow> N``{x} \<subseteq> \<E>" and
        Nh_to_Lim2:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> LimN N \<longleftrightarrow> N``{x} \<subseteq> \<E>"
proof-
  show P0:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> x \<in> (LimN N)``{\<E>} \<longleftrightarrow> N``{x} \<subseteq> \<E>"
    using A0 by (auto simp:LimN_def ispsmap_def subset_iff)
  show P1:"\<And>\<E> x. \<lbrakk>x \<in> X; \<E> \<in> pfilters\<rbrakk> \<Longrightarrow> (\<E>, x) \<in> LimN N \<longleftrightarrow> N``{x} \<subseteq> \<E>"
    using P0 by simp
qed

lemma Lim_to_Nh:
  assumes A0:"isconvs Lim"
  shows Lim_to_Nh1:"\<And>x. \<lbrakk>(dual Lim)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> (NLim Lim)``{x} = \<Inter>{\<E>. (\<E>, x) \<in> Lim}" and
        Lim_to_Nh2:"centered Lim \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (NLim Lim)``{x} = \<Inter>{\<E>. (\<E>, x) \<in> Lim})" and
        Lim_to_Nh3:"\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (x, V) \<in> NLim Lim \<longleftrightarrow> (X - V, x) \<notin> ClLim Lim" and
        Lim_to_Nh4:"\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> V \<in> (NLim Lim)``{x} \<longleftrightarrow> x \<notin> (ClLim Lim)``{X - V}" and
        Lim_to_Nh5:"\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> V \<notin> (NLim Lim)``{x} \<longleftrightarrow> x \<in> (ClLim Lim)``{X - V}"
proof-
  have B0:"\<And>\<E> x. (\<E>, x) \<in> Lim \<Longrightarrow> \<E> \<in> pfilters \<and> x \<in> X"
    using A0 by (auto simp:isconvs_def)
  show P0:"\<And>x. \<lbrakk>(dual Lim)``{x} \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> (NLim Lim)``{x} = \<Inter>{\<E>. (\<E>, x) \<in> Lim}"
  proof-
    fix x assume A1:"(dual Lim)``{x} \<noteq> {}" and A2:"x \<in> X"
    show "(NLim Lim)``{x} = \<Inter>{\<E>. (\<E>, x) \<in> Lim}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
        using B0 by (auto simp:NLim_def)
    next
      show "?R \<subseteq> ?L"
      proof
        fix A assume A3:"A \<in> ?R"
        obtain \<E> where B1:"(\<E>, x) \<in> Lim"
          using A1 by blast
        then have "A \<in> \<E>"
          using A3 by blast
        then have "A \<in> Pow X"
          using set_pfilter_mem_base B0[OF B1] by blast
        then show "A \<in> ?L"
          using A2 A3 by (auto simp:NLim_def)
      qed
    qed
  qed
  show P1:"centered Lim \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (NLim Lim)``{x} = \<Inter>{\<E>. (\<E>, x) \<in> Lim})"
    using P0 centeredD2 by blast
  show P2:"\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (x, V) \<in> NLim Lim \<longleftrightarrow> (X - V, x) \<notin> ClLim Lim"
  proof-
    fix x V assume vmem:"V \<in> Pow X" and xmem:"x \<in> X"
    have B1:"\<And>\<F>. (\<F>, x) \<in> Lim \<Longrightarrow> {X - V} # \<F> \<longleftrightarrow> V \<notin> \<F>"
    proof-
      fix \<F> assume "(\<F>, x) \<in> Lim"
      then have "pow.pfilter \<F>"
        using B0 by simp
      then have "{X - V} # \<F> \<longleftrightarrow> X - (X - V) \<notin> \<F>"
        using pfilter_mesh_single_iff[of \<F> "X - V"] by simp
      then show "{X - V} # \<F> \<longleftrightarrow> V \<notin> \<F>"
        using vmem by (simp add:Diff_Diff_Int Int_absorb1)
    qed
    have "(x, V) \<in> NLim Lim \<longleftrightarrow> (\<forall>\<F>. (\<F>, x) \<in> Lim \<longrightarrow> V \<in> \<F>)"
      using vmem xmem B0 by (auto simp:NLim_def)
    also have "... \<longleftrightarrow> \<not>(\<exists>\<F>\<in>pfilters. {X - V} # \<F> \<and> (\<F>, x) \<in> Lim)"
      using B0 B1 by blast
    also have "... \<longleftrightarrow> (X - V, x) \<notin> ClLim Lim"
      using vmem xmem by (simp add:ClLim_def)
    finally show "(x, V) \<in> NLim Lim \<longleftrightarrow> (X - V, x) \<notin> ClLim Lim"
      by blast
  qed
  show P3:"\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> V \<in> (NLim Lim)``{x} \<longleftrightarrow> x \<notin> (ClLim Lim)``{X - V}"
    by (simp add:P2)
  show P4:"\<And>x V. \<lbrakk>V \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> V \<notin> (NLim Lim)``{x} \<longleftrightarrow> x \<in> (ClLim Lim)``{X - V}"
    by (simp add:P2)
qed

lemma Cl_to_Adh:
  assumes A0:"isspmap Cl"
  shows "\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (AdhCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}"
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters"
  then have P0:"pow.pfilter \<F>"
    by simp
  show "(AdhCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
      using set_pfilter_mem_base[OF P0] by (auto simp:AdhCl_def)
  next
    show "?R \<subseteq> ?L"
    proof
      fix x assume R0:"x \<in> ?R"
      then have B0:"\<And>A. A \<in> \<F> \<Longrightarrow> (A, x) \<in> Cl"
        by blast
      then have "(X, x) \<in> Cl"
        using set_pfilter_whole[OF P0] by blast
      then have B1:"x \<in> X"
        using A0 by (auto simp:isspmap_def)
      then show "x \<in> ?L"
        using A1 B0 by (simp add:AdhCl_def)
    qed
  qed
qed

lemma Adh_to_Cl:
  assumes A0:"isconvs Adh"
  shows "\<And>A. A \<in> Pow X \<Longrightarrow> (ClAdh Adh)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> \<F>}"
proof-
  fix A assume A1:"A \<in> Pow X"
  have B0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
    using A0 by (auto simp:isconvs_def)
  show "(ClAdh Adh)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> \<F>}"
    using A1 B0 by (auto simp:ClAdh_def)
qed

lemma Adh_to_Cl2:
  assumes A0:"isconvs Adh" and A1:"antiadh Adh"
  shows Adh_to_Cl20:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClAdh Adh)``{A} = Adh``{lcro subset_order (Pow X) A}" and
        Adh_to_Cl21:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (ClAdh Adh)``{A} \<subseteq> (ClAdh Adh)``{B}" and
        Adh_to_Cl22:"(ClAdh Adh)``{{}} = {}" and
        Adh_to_Cl23:"isspmap (ClAdh Adh)" and
        Adh_to_Cl24:"iso_spmap (ClAdh Adh)"
proof-
  have B0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
    using A0 by (auto simp:isconvs_def)
  show P0:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClAdh Adh)``{A} = Adh``{lcro subset_order (Pow X) A}"
  proof-
    fix A assume A2:"A \<in> Pow X"
    show "(ClAdh Adh)``{A} = Adh``{lcro subset_order (Pow X) A}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof
        fix x assume "x \<in> ?L"
        then obtain \<G> where B1:"\<G> \<in> pfilters" and B2:"A \<in> \<G>" and B3:"(\<G>, x) \<in> Adh"
          by (auto simp:ClAdh_def)
        have B4:"lcro subset_order (Pow X) A \<subseteq> \<G>"
          using set_pfilter_lcro_sub B1 B2 by simp
        have B5:"lcro subset_order (Pow X) A \<in> pfilters"
          using A2 B1 B2 set_pfilter_ne set_lcro_pfilter by auto
        then show "x \<in> ?R"
          using antiadhD1[OF A1 _ B3 B4] by simp
      qed
    next
      show "?R \<subseteq> ?L"
      proof
        fix x assume "x \<in> ?R"
        then have B1:"(lcro subset_order (Pow X) A, x) \<in> Adh"
          by simp
        then obtain B2:"x \<in> X" and B3:"lcro subset_order (Pow X) A \<in> pfilters"
          using B0 by blast
        have "A \<in> lcro subset_order (Pow X) A"
          using A2 by (simp add:lcro_iff)
        then show "x \<in> ?L"
          using A2 B1 B2 B3 by (auto simp:ClAdh_def)
      qed
    qed
  qed
  show P1:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (ClAdh Adh)``{A} \<subseteq> (ClAdh Adh)``{B}"
  proof-
    fix A B assume A2:"A \<in> Pow X" and A3:"B \<in> Pow X" and A4:"A \<subseteq> B"
    show "(ClAdh Adh)``{A} \<subseteq> (ClAdh Adh)``{B}"
    proof
      fix x assume "x \<in> (ClAdh Adh)``{A}"
      then obtain \<G> where B1:"\<G> \<in> pfilters" and B2:"A \<in> \<G>" and B3:"(\<G>, x) \<in> Adh" and B4:"x \<in> X"
        by (auto simp:ClAdh_def)
      then have "B \<in> \<G>"
        using A3 A4 set_pfilter_up by simp
      then show "x \<in> (ClAdh Adh)``{B}"
        using A3 B1 B3 B4 by (auto simp:ClAdh_def)
    qed
  qed
  show P2:"(ClAdh Adh)``{{}} = {}"
    using set_pfilter_ne by (auto simp:ClAdh_def)
  show P3:"isspmap (ClAdh Adh)"
    by (auto simp:isspmap_def ClAdh_def)
  show P4:"iso_spmap (ClAdh Adh)"
    by (rule iso_spmapI1) (simp add:P1)
qed

lemma Cl_to_Adh2:
  assumes A0:"isspmap Cl" and A1:"iso_spmap Cl" and A2:"Cl``{{}} = {}"
  shows Cl_to_Adh20:"isconvs (AdhCl Cl)" and
        Cl_to_Adh21:"antiadh (AdhCl Cl)"
proof-
  show P0:"isconvs (AdhCl Cl)"
    by (auto simp:isconvs_def AdhCl_def)
  show P1:"antiadh (AdhCl Cl)"
  proof(rule antiadhI1)
    fix \<G> \<F> x assume A3:"\<G> \<in> pfilters" and A4:"(\<F>, x) \<in> AdhCl Cl" and A5:"\<G> \<subseteq> \<F>"
    then show "(\<G>, x) \<in> AdhCl Cl"
      by (auto simp:AdhCl_def)
  qed
qed

lemma Cl_to_Lim:
  assumes A0:"isspmap Cl"
  shows Cl_to_Lim1:"\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (LimCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A} # \<F>}" and
        Cl_to_Lim2:"\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (LimCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> grill X \<F>}"
proof-
  show P0:"\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (LimCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A} # \<F>}"
  proof-
    fix \<F> assume A1:"\<F> \<in> pfilters"
    then have P1:"pow.pfilter \<F>"
      by simp
    show "(LimCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A} # \<F>}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
        by (auto simp:LimCl_def)
    next
      show "?R \<subseteq> ?L"
      proof
        fix x assume R0:"x \<in> ?R"
        then have B0:"\<And>A. \<lbrakk>A \<in> Pow X; {A} # \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
          by blast
        have "{X} # \<F>"
          using pfilter_mem_mesh[OF P1 set_pfilter_whole[OF P1]] .
        then have "(X, x) \<in> Cl"
          using B0 by simp
        then have B1:"x \<in> X"
          using A0 by (auto simp:isspmap_def)
        then show "x \<in> ?L"
          using A1 B0 by (simp add:LimCl_def)
      qed
    qed
  qed
  show P1:"\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (LimCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> grill X \<F>}"
  proof-
    fix \<F> assume A1:"\<F> \<in> pfilters"
    have "\<And>A. A \<in> grill X \<F> \<longleftrightarrow> A \<in> Pow X \<and> {A} # \<F>"
      by (auto simp:grill_iff mesh_def Int_commute)
    then show "(LimCl Cl)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> grill X \<F>}"
      using P0[OF A1] by simp
  qed
qed

lemma onpconvD2:
  assumes A0:"onpconv q" and A1:"centered q" and A2:"isconvs q"
  shows "\<And>x. x \<in> X \<Longrightarrow> ((NLim q)``{x}, x) \<in> q"
proof-
  fix x assume xmem:"x \<in> X"
  have "(NLim q)``{x} = \<Inter>{\<E>. (\<E>, x) \<in> q}"
    by (simp add:Lim_to_Nh2[OF A2 A1 xmem])
  then show "((NLim q)``{x}, x) \<in> q"
    using onpconvD1[OF A0 xmem] by simp
qed

lemma ClLim_mem_iff:
  assumes prtpx:"is_prtop q" and xmem:"x \<in> X" and amem:"A \<in> Pow X"
  shows "x \<in> (ClLim q)``{A} \<longleftrightarrow> {A} # (NLim q)``{x}" (is "?L \<longleftrightarrow> ?R")
proof-
  have A0:"isconvs q" and A1:"centered q" and A2:"onpconv q"
    using prtpx by (simp_all add:is_prtop_def)
  have LR:"?L \<Longrightarrow> ?R"
  proof-
    assume ?L
    then obtain F where B0:"F \<in> pfilters" and B1:"(F, x) \<in> q" and B2:"{A} # F"
      by (auto simp:ClLim_def)
    have B3:"(NLim q)``{x} \<subseteq> F"
      using B0 B1 by (auto simp:NLim_def)
    then show ?R
      using B2 mesh_sub by blast
  qed
  have RL:"?R \<Longrightarrow> ?L"
  proof-
    assume ?R
    have "((NLim q)``{x}, x) \<in> q"
      by (rule onpconvD2[OF A2 A1 A0 xmem])
    then have "(NLim q)``{x} \<in> pfilters"
      using A0 by (auto simp:isconvs_def)
    then show ?L
      using \<open>?R\<close> \<open>((NLim q)``{x}, x) \<in> q\<close> amem xmem by (auto simp:ClLim_def)
  qed
  from LR RL show ?thesis
    by blast
qed

lemma Lim_to_Cl:
  assumes A0:"isconvs Lim"
  shows Lim_to_Cl10:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> {A} # \<F>}" and
        Lim_to_Cl11:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> grill X \<F>}"
proof-
  have B0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
    using A0 by (auto simp:isconvs_def)
  show P0:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> {A} # \<F>}"
    using B0 by (auto simp:ClLim_def)
  show P1:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> grill X \<F>}"
  proof-
    fix A assume A1:"A \<in> Pow X"
    have "\<And>\<F>. A \<in> grill X \<F> \<longleftrightarrow> {A} # \<F>"
      using A1 by (auto simp:grill_iff mesh_def Int_commute)
    then show "(ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> grill X \<F>}"
      using P0[OF A1] by simp
  qed
qed

lemma Lim_to_Cl2:
  assumes A0:"isconvs Lim" and A1:"isoconv Lim"
  shows Lim_to_Cl20:"\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (A, x) \<in> ClLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> A \<in> \<G>)" and
        Lim_to_Cl21:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> \<F>}"
proof-
  have B0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
    using A0 by (auto simp:isconvs_def)
  show P0:"\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (A, x) \<in> ClLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> A \<in> \<G>)"
  proof-
    fix x A assume A2:"x \<in> X" and A3:"A \<in> Pow X"
    have "(A, x) \<in> ClLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> {A} # \<G>)"
      using A2 A3 by (auto simp:ClLim_def)
    also have "... \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> A \<in> \<G>)" (is "?L \<longleftrightarrow> ?R")
    proof
      assume ?L
      then obtain \<G> where B1:"\<G> \<in> pfilters" and B2:"(\<G>, x) \<in> Lim" and B3:"{A} # \<G>"
        by blast
      then obtain \<H> where B4:"pow.pfilter \<H>" and B5:"\<G> \<subseteq> \<H>" and B6:"A \<in> \<H>"
        using mesh_pfilter_finer[of \<G> A] A3 by auto
      then have "(\<H>, x) \<in> Lim"
        using isoconvD1[OF A1 _ B2 B5] by simp
      then show ?R
        using B4 B6 by blast
    next
      assume ?R
      then show ?L
        using pfilter_mem_mesh by blast
    qed
    finally show "(A, x) \<in> ClLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> A \<in> \<G>)"
      by blast
  qed
  show P1:"\<And>A. A \<in> Pow X \<Longrightarrow> (ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> \<F>}"
  proof-
    fix A assume A2:"A \<in> Pow X"
    show "(ClLim Lim)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters \<and> A \<in> \<F>}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof
        fix x assume "x \<in> ?L"
        then have "x \<in> X"
          by (simp add:ClLim_def)
        then show "x \<in> ?R"
          using P0[OF _ A2] \<open>x \<in> ?L\<close> by auto
      qed
    next
      show "?R \<subseteq> ?L"
      proof
        fix x assume "x \<in> ?R"
        then obtain \<F> where "\<F> \<in> pfilters" and "A \<in> \<F>" and "(\<F>, x) \<in> Lim"
          by blast
        then show "x \<in> ?L"
          using B0 P0[OF _ A2] by blast
      qed
    qed
  qed
qed

lemma Lim_to_Adh:
  assumes A0:"isconvs Lim"
  shows "\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (AdhLim Lim)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in> pfilters \<and> \<G> # \<F>}"
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters"
  have B0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
    using A0 by (auto simp:isconvs_def)
  then show "(AdhLim Lim)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in> pfilters \<and> \<G> # \<F>}"
    using A1 by (auto simp:AdhLim_def)
qed

lemma Lim_to_Adh2:
  assumes A0:"isconvs Lim" and A1:"isoconv Lim"
  shows Lim_to_Adh20:"\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters; x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> AdhLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> \<F> \<subseteq> \<G>)" and
        Lim_to_Adh21:"\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (AdhLim Lim)``{\<F>} = \<Union>{Lim``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>}"
proof-
  have B0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters"
    using A0 by (auto simp:isconvs_def)
  show P0:"\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters; x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> AdhLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> \<F> \<subseteq> \<G>)"
  proof-
    fix \<F> x assume A2:"\<F> \<in> pfilters" and A3:"x \<in> X"
    have "(\<F>, x) \<in> AdhLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> \<G> # \<F>)"
      using A2 A3 by (auto simp:AdhLim_def)
    also have "... \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> \<F> \<subseteq> \<G>)" (is "?L \<longleftrightarrow> ?R")
    proof
      assume ?L
      then obtain \<G> where B1:"\<G> \<in> pfilters" and B2:"(\<G>, x) \<in> Lim" and B3:"\<G> # \<F>"
        by blast
      then obtain \<H> where B4:"pow.pfilter \<H>" and B5:"\<G> \<subseteq> \<H>" and B6:"\<F> \<subseteq> \<H>"
        using mesh_pfilters_finer[of \<G> \<F>] A2 by auto
      then have "(\<H>, x) \<in> Lim"
        using isoconvD1[OF A1 _ B2 B5] by simp
      then show ?R
        using B4 B6 by blast
    next
      assume ?R
      then obtain \<G> where "\<G> \<in> pfilters" and "(\<G>, x) \<in> Lim" and "\<F> \<subseteq> \<G>"
        by blast
      then show ?L
        using pfilter_sub_mesh mesh_sym by blast
    qed
    finally show "(\<F>, x) \<in> AdhLim Lim \<longleftrightarrow> (\<exists>\<G>\<in>pfilters. (\<G>, x) \<in> Lim \<and> \<F> \<subseteq> \<G>)"
      by blast
  qed
  show P1:"\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (AdhLim Lim)``{\<F>} = \<Union>{Lim``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>}"
  proof-
    fix \<F> assume A2:"\<F> \<in> pfilters"
    show "(AdhLim Lim)``{\<F>} = \<Union>{Lim``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>}" (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof
        fix x assume "x \<in> ?L"
        then have "x \<in> X"
          by (simp add:AdhLim_def)
        then obtain \<G> where B1:"\<G> \<in> pfilters" and B2:"(\<G>, x) \<in> Lim" and B3:"\<F> \<subseteq> \<G>"
          using P0[OF A2] \<open>x \<in> ?L\<close> by auto
        obtain \<U> where B4:"ultrafilter \<U>" and B5:"\<G> \<subseteq> \<U>"
          using ultrafilter_exists B1 by auto
        then have "(\<U>, x) \<in> Lim"
          using isoconvD1[OF A1 _ B2 B5] ultrafilter_pfilter by simp
        then show "x \<in> ?R"
          using B3 B4 B5 by blast
      qed
    next
      show "?R \<subseteq> ?L"
      proof
        fix x assume "x \<in> ?R"
        then obtain \<U> where B1:"ultrafilter \<U>" and B2:"\<F> \<subseteq> \<U>" and B3:"(\<U>, x) \<in> Lim"
          by blast
        then have "\<U> \<in> pfilters" and "x \<in> X"
          using ultrafilter_pfilter B0 by auto
        then show "x \<in> ?L"
          using P0[OF A2] B2 B3 by auto
      qed
    qed
  qed
qed

lemma Adh_to_Lim:
  assumes A0:"isconvs Adh"
  shows "\<And>\<F>. \<F> \<in> pfilters \<Longrightarrow> (LimAdh Adh)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in> pfilters \<and> \<G> # \<F>}"
proof-
  fix \<F> assume A1:"\<F> \<in> pfilters"
  show "(LimAdh Adh)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in> pfilters \<and> \<G> # \<F>}" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
      by (auto simp:LimAdh_def)
  next
    show "?R \<subseteq> ?L"
    proof
      fix x assume R0:"x \<in> ?R"
      then have B0:"\<And>\<G>. \<lbrakk>\<G> \<in> pfilters; \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh"
        by blast
      have "(\<F>, x) \<in> Adh"
        using B0[OF A1] pfilter_mesh_self A1 by simp
      then have "x \<in> X"
        using A0 by (auto simp:isconvs_def)
      then show "x \<in> ?L"
        using A1 B0 by (simp add:LimAdh_def)
    qed
  qed
qed

lemma Adh_to_Lim2:
  assumes A0:"isconvs Adh" and A1:"antiadh Adh"
  shows Adh_to_Lim20:"\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters; x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> LimAdh Adh \<longleftrightarrow> (\<forall>\<G>\<in>pfilters. \<F> \<subseteq> \<G> \<longrightarrow> (\<G>, x) \<in> Adh)"
proof-
  fix \<F> x assume A2:"\<F> \<in> pfilters" and A3:"x \<in> X"
  have "(\<F>, x) \<in> LimAdh Adh \<longleftrightarrow> (\<forall>\<G>\<in>pfilters. \<G> # \<F> \<longrightarrow> (\<G>, x) \<in> Adh)"
    using A2 A3 by (auto simp:LimAdh_def)
  also have "... \<longleftrightarrow> (\<forall>\<G>\<in>pfilters. \<F> \<subseteq> \<G> \<longrightarrow> (\<G>, x) \<in> Adh)" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then show ?R
      using pfilter_sub_mesh mesh_sym by blast
  next
    assume A4:?R
    have "\<And>\<G>. \<lbrakk>\<G> \<in> pfilters; \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh"
    proof-
      fix \<G> assume A5:"\<G> \<in> pfilters" and A6:"\<G> # \<F>"
      then obtain \<H> where B0:"pow.pfilter \<H>" and B1:"\<G> \<subseteq> \<H>" and B2:"\<F> \<subseteq> \<H>"
        using mesh_pfilters_finer[of \<G> \<F>] A2 by auto
      then have "(\<H>, x) \<in> Adh"
        using A4 by simp
      then show "(\<G>, x) \<in> Adh"
        using antiadhD1[OF A1 A5 _ B1] by simp
    qed
    then show ?L
      by blast
  qed
  finally show "(\<F>, x) \<in> LimAdh Adh \<longleftrightarrow> (\<forall>\<G>\<in>pfilters. \<F> \<subseteq> \<G> \<longrightarrow> (\<G>, x) \<in> Adh)"
    by blast
qed

section \<open>Galois Connections on Convergences\<close>

lemma NCl_galois_iff:
  assumes A0:"Cl \<subseteq> Pow X \<times> X" and A1:"N \<subseteq> X \<times> Pow X"
  shows "Cl \<subseteq> ClN N \<longleftrightarrow> N \<subseteq> NCl Cl"
proof-
  have "Cl \<subseteq> ClN N \<longleftrightarrow> (\<forall>B x A. (B, x) \<in> Cl \<and> (x, A) \<in> N \<longrightarrow> B \<inter> A \<noteq> {})"
    using A0 by (auto simp:ClN_def mesh_def subset_iff)
  moreover have "N \<subseteq> NCl Cl \<longleftrightarrow> (\<forall>B x A. (B, x) \<in> Cl \<and> (x, A) \<in> N \<longrightarrow> A \<inter> B \<noteq> {})"
    using A1 by (auto simp:NCl_def mesh_def subset_iff)
  ultimately show ?thesis
    by (simp add:Int_commute)
qed

lemma NAdh_galois_iff:
  assumes A0:"Adh \<subseteq> pfilters \<times> X" and A1:"N \<subseteq> X \<times> Pow X"
  shows "Adh \<subseteq> AdhN N \<longleftrightarrow> N \<subseteq> NAdh Adh"
proof-
  have "Adh \<subseteq> AdhN N \<longleftrightarrow> (\<forall>\<E> x A. (\<E>, x) \<in> Adh \<and> (x, A) \<in> N \<longrightarrow> {A} # \<E>)"
    using A0 A1 by (auto simp:AdhN_def subset_iff)
  moreover have "N \<subseteq> NAdh Adh \<longleftrightarrow> (\<forall>\<E> x A. (\<E>, x) \<in> Adh \<and> (x, A) \<in> N \<longrightarrow> {A} # \<E>)"
    using A0 A1 by (auto simp:NAdh_def subset_iff)
  ultimately show ?thesis
    by simp
qed

lemma NLim_galois_iff:
  assumes A0:"Lim \<subseteq> pfilters \<times> X" and A1:"N \<subseteq> X \<times> Pow X"
  shows "Lim \<subseteq> LimN N \<longleftrightarrow> N \<subseteq> NLim Lim"
proof-
  have "Lim \<subseteq> LimN N \<longleftrightarrow> (\<forall>\<E> x A. (\<E>, x) \<in> Lim \<and> (x, A) \<in> N \<longrightarrow> A \<in> \<E>)"
    using A0 A1 by (auto simp:LimN_def subset_iff)
  moreover have "N \<subseteq> NLim Lim \<longleftrightarrow> (\<forall>\<E> x A. (\<E>, x) \<in> Lim \<and> (x, A) \<in> N \<longrightarrow> A \<in> \<E>)"
    using A0 A1 by (auto simp:NLim_def subset_iff)
  ultimately show ?thesis
    by simp
qed

lemma ClAdh_galois_iff:
  assumes A0:"Adh \<subseteq> pfilters \<times> X" and A1:"Cl \<subseteq> Pow X \<times> X"
  shows "Adh \<subseteq> AdhCl Cl \<longleftrightarrow> ClAdh Adh \<subseteq> Cl"
proof
  assume L:"Adh \<subseteq> AdhCl Cl"
  show "ClAdh Adh \<subseteq> Cl"
  proof
    fix p assume "p \<in> ClAdh Adh"
    then obtain A x \<F> where B0:"p = (A, x)" and B1:"A \<in> Pow X" and B2:"\<F> \<in> pfilters" and B3:"A \<in> \<F>" and B4:"(\<F>, x) \<in> Adh"
      by (auto simp:ClAdh_def)
    then have "(\<F>, x) \<in> AdhCl Cl"
      using L by blast
    then show "p \<in> Cl"
      using B0 B1 B3 by (simp add:AdhCl_def)
  qed
next
  assume R:"ClAdh Adh \<subseteq> Cl"
  show "Adh \<subseteq> AdhCl Cl"
  proof
    fix p assume "p \<in> Adh"
    then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and B3:"(\<F>, x) \<in> Adh"
      using A0 by auto
    have "\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
      using R B1 B2 B3 by (auto simp:ClAdh_def)
    then show "p \<in> AdhCl Cl"
      using B0 B1 B2 by (simp add:AdhCl_def)
  qed
qed

lemma ClLim_galois_iff:
  assumes A0:"Lim \<subseteq> pfilters \<times> X" and A1:"Cl \<subseteq> Pow X \<times> X"
  shows "Lim \<subseteq> LimCl Cl \<longleftrightarrow> ClLim Lim \<subseteq> Cl"
proof
  assume L:"Lim \<subseteq> LimCl Cl"
  show "ClLim Lim \<subseteq> Cl"
  proof
    fix p assume "p \<in> ClLim Lim"
    then obtain A x \<F> where B0:"p = (A, x)" and B1:"A \<in> Pow X" and B2:"\<F> \<in> pfilters" and B3:"{A} # \<F>" and B4:"(\<F>, x) \<in> Lim"
      by (auto simp:ClLim_def)
    then have "(\<F>, x) \<in> LimCl Cl"
      using L by blast
    then show "p \<in> Cl"
      using B0 B1 B3 by (simp add:LimCl_def)
  qed
next
  assume R:"ClLim Lim \<subseteq> Cl"
  show "Lim \<subseteq> LimCl Cl"
  proof
    fix p assume "p \<in> Lim"
    then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and B3:"(\<F>, x) \<in> Lim"
      using A0 by auto
    have "\<And>A. \<lbrakk>A \<in> Pow X; {A} # \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl"
      using R B1 B2 B3 by (auto simp:ClLim_def)
    then show "p \<in> LimCl Cl"
      using B0 B1 B2 by (simp add:LimCl_def)
  qed
qed

lemma LimAdh_galois_iff:
  assumes A0:"Lim \<subseteq> pfilters \<times> X" and A1:"Adh \<subseteq> pfilters \<times> X"
  shows "Lim \<subseteq> LimAdh Adh \<longleftrightarrow> AdhLim Lim \<subseteq> Adh"
proof
  assume L:"Lim \<subseteq> LimAdh Adh"
  show "AdhLim Lim \<subseteq> Adh"
  proof
    fix p assume "p \<in> AdhLim Lim"
    then obtain \<F> x \<G> where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"\<G> \<in> pfilters" and B3:"\<G> # \<F>" and B4:"(\<G>, x) \<in> Lim"
      by (auto simp:AdhLim_def)
    then have "(\<G>, x) \<in> LimAdh Adh"
      using L by blast
    then show "p \<in> Adh"
      using B0 B1 B3 mesh_sym by (auto simp:LimAdh_def)
  qed
next
  assume R:"AdhLim Lim \<subseteq> Adh"
  show "Lim \<subseteq> LimAdh Adh"
  proof
    fix p assume "p \<in> Lim"
    then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and B3:"(\<F>, x) \<in> Lim"
      using A0 by auto
    have "\<And>\<G>. \<lbrakk>\<G> \<in> pfilters; \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Adh"
      using R B1 B2 B3 mesh_sym by (auto simp:AdhLim_def)
    then show "p \<in> LimAdh Adh"
      using B0 B1 B2 by (simp add:LimAdh_def)
  qed
qed

end

lemma pow_poset_dual:"poset (dual subset_order) (Pow X)"
  by unfold_locales auto

lemma galois_conn_sym:"galois_conn R X S Y f g \<Longrightarrow> galois_conn S Y R X g f"
  by (simp add:galois_conn_def galois_conn_axioms_def)

sublocale powerset \<subseteq> NCl:galois_conn subset_order "Pow (Pow X \<times> X)" subset_order "Pow (X \<times> Pow X)" NCl ClN
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
proof-
  show "galois_conn subset_order (Pow (Pow X \<times> X)) subset_order (Pow (X \<times> Pow X)) NCl ClN"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset)
    show "\<And>Cl. Cl \<in> Pow (Pow X \<times> X) \<Longrightarrow> NCl Cl \<in> Pow (X \<times> Pow X)"
      by (auto simp:NCl_def)
    show "\<And>N. N \<in> Pow (X \<times> Pow X) \<Longrightarrow> ClN N \<in> Pow (Pow X \<times> X)"
      by (auto simp:ClN_def)
    show "\<And>Cl N. \<lbrakk>Cl \<in> Pow (Pow X \<times> X); N \<in> Pow (X \<times> Pow X)\<rbrakk> \<Longrightarrow> (Cl, ClN N) \<in> subset_order \<longleftrightarrow> (N, NCl Cl) \<in> subset_order"
      by (simp add:NCl_galois_iff)
  qed
qed simp

sublocale powerset \<subseteq> ClN:galois_conn subset_order "Pow (X \<times> Pow X)" subset_order "Pow (Pow X \<times> X)" ClN NCl
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  by (rule galois_conn_sym[OF NCl.galois_conn_axioms]) simp

sublocale powerset \<subseteq> NAdh:galois_conn subset_order "Pow (pfilters \<times> X)" subset_order "Pow (X \<times> Pow X)" NAdh AdhN
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
proof-
  show "galois_conn subset_order (Pow (pfilters \<times> X)) subset_order (Pow (X \<times> Pow X)) NAdh AdhN"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset)
    show "\<And>Adh. Adh \<in> Pow (pfilters \<times> X) \<Longrightarrow> NAdh Adh \<in> Pow (X \<times> Pow X)"
      by (auto simp:NAdh_def)
    show "\<And>N. N \<in> Pow (X \<times> Pow X) \<Longrightarrow> AdhN N \<in> Pow (pfilters \<times> X)"
      by (auto simp:AdhN_def)
    show "\<And>Adh N. \<lbrakk>Adh \<in> Pow (pfilters \<times> X); N \<in> Pow (X \<times> Pow X)\<rbrakk> \<Longrightarrow> (Adh, AdhN N) \<in> subset_order \<longleftrightarrow> (N, NAdh Adh) \<in> subset_order"
      by (simp add:NAdh_galois_iff)
  qed
qed simp

sublocale powerset \<subseteq> AdhN:galois_conn subset_order "Pow (X \<times> Pow X)" subset_order "Pow (pfilters \<times> X)" AdhN NAdh
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  by (rule galois_conn_sym[OF NAdh.galois_conn_axioms]) simp

sublocale powerset \<subseteq> NLim:galois_conn subset_order "Pow (pfilters \<times> X)" subset_order "Pow (X \<times> Pow X)" NLim LimN
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
proof-
  show "galois_conn subset_order (Pow (pfilters \<times> X)) subset_order (Pow (X \<times> Pow X)) NLim LimN"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset)
    show "\<And>Lim. Lim \<in> Pow (pfilters \<times> X) \<Longrightarrow> NLim Lim \<in> Pow (X \<times> Pow X)"
      by (auto simp:NLim_def)
    show "\<And>N. N \<in> Pow (X \<times> Pow X) \<Longrightarrow> LimN N \<in> Pow (pfilters \<times> X)"
      by (auto simp:LimN_def)
    show "\<And>Lim N. \<lbrakk>Lim \<in> Pow (pfilters \<times> X); N \<in> Pow (X \<times> Pow X)\<rbrakk> \<Longrightarrow> (Lim, LimN N) \<in> subset_order \<longleftrightarrow> (N, NLim Lim) \<in> subset_order"
      by (simp add:NLim_galois_iff)
  qed
qed simp

sublocale powerset \<subseteq> LimN:galois_conn subset_order "Pow (X \<times> Pow X)" subset_order "Pow (pfilters \<times> X)" LimN NLim
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B"
  by (rule galois_conn_sym[OF NLim.galois_conn_axioms]) simp

sublocale powerset \<subseteq> ClAdh:galois_conn subset_order "Pow (pfilters \<times> X)" "dual subset_order" "Pow (Pow X \<times> X)" ClAdh AdhCl
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "\<And>A B. (A, B) \<in> dual subset_order \<longleftrightarrow> B \<subseteq> A"
proof-
  show "galois_conn subset_order (Pow (pfilters \<times> X)) (dual subset_order) (Pow (Pow X \<times> X)) ClAdh AdhCl"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset pow_poset_dual)
    show "\<And>Adh. Adh \<in> Pow (pfilters \<times> X) \<Longrightarrow> ClAdh Adh \<in> Pow (Pow X \<times> X)"
      by (auto simp:ClAdh_def)
    show "\<And>Cl. Cl \<in> Pow (Pow X \<times> X) \<Longrightarrow> AdhCl Cl \<in> Pow (pfilters \<times> X)"
      by (auto simp:AdhCl_def)
    show "\<And>Adh Cl. \<lbrakk>Adh \<in> Pow (pfilters \<times> X); Cl \<in> Pow (Pow X \<times> X)\<rbrakk> \<Longrightarrow> (Adh, AdhCl Cl) \<in> subset_order \<longleftrightarrow> (Cl, ClAdh Adh) \<in> dual subset_order"
      by (simp add:ClAdh_galois_iff)
  qed
qed simp_all

sublocale powerset \<subseteq> AdhCl:galois_conn "dual subset_order" "Pow (Pow X \<times> X)" subset_order "Pow (pfilters \<times> X)" AdhCl ClAdh
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "\<And>A B. (A, B) \<in> dual subset_order \<longleftrightarrow> B \<subseteq> A"
  by (rule galois_conn_sym[OF ClAdh.galois_conn_axioms]) simp_all

sublocale powerset \<subseteq> ClLim:galois_conn subset_order "Pow (pfilters \<times> X)" "dual subset_order" "Pow (Pow X \<times> X)" ClLim LimCl
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "\<And>A B. (A, B) \<in> dual subset_order \<longleftrightarrow> B \<subseteq> A"
proof-
  show "galois_conn subset_order (Pow (pfilters \<times> X)) (dual subset_order) (Pow (Pow X \<times> X)) ClLim LimCl"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset pow_poset_dual)
    show "\<And>Lim. Lim \<in> Pow (pfilters \<times> X) \<Longrightarrow> ClLim Lim \<in> Pow (Pow X \<times> X)"
      by (auto simp:ClLim_def)
    show "\<And>Cl. Cl \<in> Pow (Pow X \<times> X) \<Longrightarrow> LimCl Cl \<in> Pow (pfilters \<times> X)"
      by (auto simp:LimCl_def)
    show "\<And>Lim Cl. \<lbrakk>Lim \<in> Pow (pfilters \<times> X); Cl \<in> Pow (Pow X \<times> X)\<rbrakk> \<Longrightarrow> (Lim, LimCl Cl) \<in> subset_order \<longleftrightarrow> (Cl, ClLim Lim) \<in> dual subset_order"
      by (simp add:ClLim_galois_iff)
  qed
qed simp_all

sublocale powerset \<subseteq> LimCl:galois_conn "dual subset_order" "Pow (Pow X \<times> X)" subset_order "Pow (pfilters \<times> X)" LimCl ClLim
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "\<And>A B. (A, B) \<in> dual subset_order \<longleftrightarrow> B \<subseteq> A"
  by (rule galois_conn_sym[OF ClLim.galois_conn_axioms]) simp_all

sublocale powerset \<subseteq> AdhLim:galois_conn subset_order "Pow (pfilters \<times> X)" "dual subset_order" "Pow (pfilters \<times> X)" AdhLim LimAdh
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "\<And>A B. (A, B) \<in> dual subset_order \<longleftrightarrow> B \<subseteq> A"
proof-
  show "galois_conn subset_order (Pow (pfilters \<times> X)) (dual subset_order) (Pow (pfilters \<times> X)) AdhLim LimAdh"
  proof(intro galois_conn.intro galois_conn_axioms.intro pow_poset pow_poset_dual)
    show "\<And>Lim. Lim \<in> Pow (pfilters \<times> X) \<Longrightarrow> AdhLim Lim \<in> Pow (pfilters \<times> X)"
      by (auto simp:AdhLim_def)
    show "\<And>Adh. Adh \<in> Pow (pfilters \<times> X) \<Longrightarrow> LimAdh Adh \<in> Pow (pfilters \<times> X)"
      by (auto simp:LimAdh_def)
    show "\<And>Lim Adh. \<lbrakk>Lim \<in> Pow (pfilters \<times> X); Adh \<in> Pow (pfilters \<times> X)\<rbrakk> \<Longrightarrow> (Lim, LimAdh Adh) \<in> subset_order \<longleftrightarrow> (Adh, AdhLim Lim) \<in> dual subset_order"
      by (simp add:LimAdh_galois_iff)
  qed
qed simp_all

sublocale powerset \<subseteq> LimAdh:galois_conn "dual subset_order" "Pow (pfilters \<times> X)" subset_order "Pow (pfilters \<times> X)" LimAdh AdhLim
  rewrites "\<And>A B. (A, B) \<in> subset_order \<longleftrightarrow> A \<subseteq> B" and "\<And>A B. (A, B) \<in> dual subset_order \<longleftrightarrow> B \<subseteq> A"
  by (rule galois_conn_sym[OF AdhLim.galois_conn_axioms]) simp_all

context powerset
begin

lemma NCl_rng:"NCl ` Pow (Pow X \<times> X) \<subseteq> Pow (X \<times> Pow X)"
  and ClN_rng:"ClN ` Pow (X \<times> Pow X) \<subseteq> Pow (Pow X \<times> X)"
  and NAdh_rng:"NAdh ` Pow (pfilters \<times> X) \<subseteq> Pow (X \<times> Pow X)"
  and AdhN_rng:"AdhN ` Pow (X \<times> Pow X) \<subseteq> Pow (pfilters \<times> X)"
  and NLim_rng:"NLim ` Pow (pfilters \<times> X) \<subseteq> Pow (X \<times> Pow X)"
  and LimN_rng:"LimN ` Pow (X \<times> Pow X) \<subseteq> Pow (pfilters \<times> X)"
  and ClAdh_rng:"ClAdh ` Pow (pfilters \<times> X) \<subseteq> Pow (Pow X \<times> X)"
  and AdhCl_rng:"AdhCl ` Pow (Pow X \<times> X) \<subseteq> Pow (pfilters \<times> X)"
  and ClLim_rng:"ClLim ` Pow (pfilters \<times> X) \<subseteq> Pow (Pow X \<times> X)"
  and LimCl_rng:"LimCl ` Pow (Pow X \<times> X) \<subseteq> Pow (pfilters \<times> X)"
  and AdhLim_rng:"AdhLim ` Pow (pfilters \<times> X) \<subseteq> Pow (pfilters \<times> X)"
  and LimAdh_rng:"LimAdh ` Pow (pfilters \<times> X) \<subseteq> Pow (pfilters \<times> X)"
  by (auto simp:NCl_def ClN_def NAdh_def AdhN_def NLim_def LimN_def ClAdh_def AdhCl_def ClLim_def LimCl_def AdhLim_def LimAdh_def)

lemma NCl_antitone:"antitone subset_order (Pow (Pow X \<times> X)) subset_order NCl"
  and ClN_antitone:"antitone subset_order (Pow (X \<times> Pow X)) subset_order ClN"
  and NAdh_antitone:"antitone subset_order (Pow (pfilters \<times> X)) subset_order NAdh"
  and AdhN_antitone:"antitone subset_order (Pow (X \<times> Pow X)) subset_order AdhN"
  and NLim_antitone:"antitone subset_order (Pow (pfilters \<times> X)) subset_order NLim"
  and LimN_antitone:"antitone subset_order (Pow (X \<times> Pow X)) subset_order LimN"
  and ClAdh_antitone:"antitone subset_order (Pow (pfilters \<times> X)) (dual subset_order) ClAdh"
  and AdhCl_antitone:"antitone subset_order (Pow (Pow X \<times> X)) (dual subset_order) AdhCl"
  and ClLim_antitone:"antitone subset_order (Pow (pfilters \<times> X)) (dual subset_order) ClLim"
  and LimCl_antitone:"antitone subset_order (Pow (Pow X \<times> X)) (dual subset_order) LimCl"
  and AdhLim_antitone:"antitone subset_order (Pow (pfilters \<times> X)) (dual subset_order) AdhLim"
  and LimAdh_antitone:"antitone subset_order (Pow (pfilters \<times> X)) (dual subset_order) LimAdh"
  by (rule isotoneI, simp add:NCl.anti_f ClN.anti_f NAdh.anti_f AdhN.anti_f NLim.anti_f LimN.anti_f
                              ClAdh.anti_f AdhCl.anti_f ClLim.anti_f LimCl.anti_f AdhLim.anti_f LimAdh.anti_f)+

lemma ClNCl_ext:"Cl \<subseteq> Pow X \<times> X \<Longrightarrow> Cl \<subseteq> ClN (NCl Cl)"
  and NClN_ext:"N \<subseteq> X \<times> Pow X \<Longrightarrow> N \<subseteq> NCl (ClN N)"
  and AdhNAdh_ext:"Adh \<subseteq> pfilters \<times> X \<Longrightarrow> Adh \<subseteq> AdhN (NAdh Adh)"
  and NAdhN_ext:"N \<subseteq> X \<times> Pow X \<Longrightarrow> N \<subseteq> NAdh (AdhN N)"
  and LimN_ext:"Lim \<subseteq> pfilters \<times> X \<Longrightarrow> Lim \<subseteq> LimN (NLim Lim)"
  and NLim_ext:"N \<subseteq> X \<times> Pow X \<Longrightarrow> N \<subseteq> NLim (LimN N)"
  and AdhCl_ext:"Adh \<subseteq> pfilters \<times> X \<Longrightarrow> Adh \<subseteq> AdhCl (ClAdh Adh)"
  and ClAdh_ext:"Cl \<subseteq> Pow X \<times> X \<Longrightarrow> ClAdh (AdhCl Cl) \<subseteq> Cl"
  and LimCl_ext:"Lim \<subseteq> pfilters \<times> X \<Longrightarrow> Lim \<subseteq> LimCl (ClLim Lim)"
  and ClLim_ext:"Cl \<subseteq> Pow X \<times> X \<Longrightarrow> ClLim (LimCl Cl) \<subseteq> Cl"
  and AdhLim_ext:"Lim \<subseteq> pfilters \<times> X \<Longrightarrow> Lim \<subseteq> LimAdh (AdhLim Lim)"
  and LimAdh_ext:"Adh \<subseteq> pfilters \<times> X \<Longrightarrow> AdhLim (LimAdh Adh) \<subseteq> Adh"
  using NCl.ext_f ClN.ext_f NAdh.ext_f AdhN.ext_f NLim.ext_f LimN.ext_f
        ClAdh.ext_f ClAdh.ext_g ClLim.ext_f ClLim.ext_g AdhLim.ext_f AdhLim.ext_g by simp_all

lemma NCl_galois:"galois_conn subset_order (Pow (Pow X \<times> X)) subset_order (Pow (X \<times> Pow X)) NCl ClN"
  and NAdh_galois:"galois_conn subset_order (Pow (pfilters \<times> X)) subset_order (Pow (X \<times> Pow X)) NAdh AdhN"
  and LimN_galois:"galois_conn subset_order (Pow (pfilters \<times> X)) subset_order (Pow (X \<times> Pow X)) NLim LimN"
  and ClAdh_galois:"galois_conn subset_order (Pow (pfilters \<times> X)) (dual subset_order) (Pow (Pow X \<times> X)) ClAdh AdhCl"
  and ClLim_galois:"galois_conn subset_order (Pow (pfilters \<times> X)) (dual subset_order) (Pow (Pow X \<times> X)) ClLim LimCl"
  and LimAdh_galois:"galois_conn subset_order (Pow (pfilters \<times> X)) (dual subset_order) (Pow (pfilters \<times> X)) AdhLim LimAdh"
  by (rule NCl.galois_conn_axioms NAdh.galois_conn_axioms NLim.galois_conn_axioms
           ClAdh.galois_conn_axioms ClLim.galois_conn_axioms AdhLim.galois_conn_axioms)+

section \<open>Convergence Sets\<close>

lemma mesh_single_mono:"\<lbrakk>{A} # \<N>; A \<subseteq> B\<rbrakk> \<Longrightarrow> {B} # \<N>"
  by (auto simp:mesh_def)

lemma mesh_single_grill_iff:"A \<subseteq> X \<Longrightarrow> {A} # \<B> \<longleftrightarrow> A \<in> grill X \<B>"
  using mesh_iff_grill[of "{A}" \<B>] by simp

lemma spmap_eqI:
  assumes A0:"isspmap Cl" and A1:"isspmap Cl'" and A2:"\<And>x. x \<in> X \<Longrightarrow> (dual Cl)``{x} = (dual Cl')``{x}"
  shows "Cl = Cl'"
proof
  show "Cl \<subseteq> Cl'"
  proof
    fix p assume "p \<in> Cl"
    then obtain A x where "p = (A, x)" and "x \<in> X" and "A \<in> (dual Cl)``{x}"
      using A0 by (auto simp:isspmap_def)
    then show "p \<in> Cl'"
      using A2 by auto
  qed
next
  show "Cl' \<subseteq> Cl"
  proof
    fix p assume "p \<in> Cl'"
    then obtain A x where "p = (A, x)" and "x \<in> X" and "A \<in> (dual Cl')``{x}"
      using A1 by (auto simp:isspmap_def)
    then show "p \<in> Cl"
      using A2 by auto
  qed
qed

lemma psmap_eqI:
  assumes A0:"ispsmap N" and A1:"ispsmap N'" and A2:"\<And>x. x \<in> X \<Longrightarrow> N``{x} = N'``{x}"
  shows "N = N'"
proof
  show "N \<subseteq> N'"
  proof
    fix p assume "p \<in> N"
    then obtain x A where "p = (x, A)" and "x \<in> X" and "A \<in> N``{x}"
      using A0 by (auto simp:ispsmap_def)
    then show "p \<in> N'"
      using A2 by auto
  qed
next
  show "N' \<subseteq> N"
  proof
    fix p assume "p \<in> N'"
    then obtain x A where "p = (x, A)" and "x \<in> X" and "A \<in> N'``{x}"
      using A1 by (auto simp:ispsmap_def)
    then show "p \<in> N"
      using A2 by auto
  qed
qed

lemma convs_eqI:
  assumes A0:"isconvs q" and A1:"isconvs q'" and A2:"\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters; x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> q \<longleftrightarrow> (\<F>, x) \<in> q'"
  shows "q = q'"
proof
  show "q \<subseteq> q'"
  proof
    fix p assume "p \<in> q"
    then obtain \<F> x where "p = (\<F>, x)" and "\<F> \<in> pfilters" and "x \<in> X"
      using A0 by (auto simp:isconvs_def)
    then show "p \<in> q'"
      using A2 \<open>p \<in> q\<close> by auto
  qed
next
  show "q' \<subseteq> q"
  proof
    fix p assume "p \<in> q'"
    then obtain \<F> x where "p = (\<F>, x)" and "\<F> \<in> pfilters" and "x \<in> X"
      using A1 by (auto simp:isconvs_def)
    then show "p \<in> q"
      using A2 \<open>p \<in> q'\<close> by auto
  qed
qed

lemma NCl_psmap:"ispsmap (NCl Cl)"
  and ClN_spmap:"isspmap (ClN N)"
  and NAdh_psmap:"ispsmap (NAdh Adh)"
  and AdhN_convs:"isconvs (AdhN N)"
  and NLim_psmap:"ispsmap (NLim Lim)"
  and LimN_convs:"isconvs (LimN N)"
  and ClAdh_spmap:"isspmap (ClAdh Adh)"
  and AdhCl_convs:"isconvs (AdhCl Cl)"
  and ClLim_spmap:"isspmap (ClLim Lim)"
  and LimCl_convs:"isconvs (LimCl Cl)"
  and AdhLim_convs:"isconvs (AdhLim Lim)"
  and LimAdh_convs:"isconvs (LimAdh Adh)"
  by (auto simp:ispsmap_def isspmap_def isconvs_def NCl_def ClN_def NAdh_def AdhN_def NLim_def LimN_def
                ClAdh_def AdhCl_def ClLim_def LimCl_def AdhLim_def LimAdh_def)

lemma ClN_iso:"iso_spmap (ClN N)"
  by (rule iso_spmapI1) (auto simp:ClN_def intro:mesh_single_mono)

lemma NCl_iso:"iso_psmap (NCl Cl)"
  by (rule iso_psmapI1) (auto simp:NCl_def intro!:up_closedI intro:mesh_single_mono)

lemma ClLim_iso:"iso_spmap (ClLim Lim)"
  by (rule iso_spmapI1) (auto simp:ClLim_def intro:mesh_single_mono)

lemma ClLim_empty:"(ClLim Lim)``{{}} = {}"
  using set_pfilter_whole by (auto simp:ClLim_def mesh_def)

lemma ClAdh_iso:"iso_spmap (ClAdh Adh)"
  by (rule iso_spmapI1) (auto simp:ClAdh_def intro:set_pfilter_up)

lemma ClAdh_empty:"(ClAdh Adh)``{{}} = {}"
  using set_pfilter_ne by (auto simp:ClAdh_def)

lemma NAdh_iso:"iso_psmap (NAdh Adh)"
proof(rule iso_psmapI1)
  fix x assume xmem:"x \<in> X"
  show "up_closed subset_order (Pow X) ((NAdh Adh)``{x})"
  proof(rule up_closedI)
    fix a b assume a0:"a \<in> (NAdh Adh)``{x}" and b0:"b \<in> Pow X" and ab0:"(a, b) \<in> subset_order"
    then have B0:"\<And>\<F>. \<lbrakk>\<F> \<in> pfilters; (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {a} # \<F>"
      by (simp add:NAdh_def)
    have "\<And>\<F>. \<lbrakk>\<F> \<in> pfilters; (\<F>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {b} # \<F>"
    proof-
      fix \<F> assume "\<F> \<in> pfilters" and "(\<F>, x) \<in> Adh"
      then have "{a} # \<F>"
        by (rule B0)
      then show "{b} # \<F>"
        using mesh_single_mono[OF \<open>{a} # \<F>\<close>, of b] ab0 by simp
    qed
    then show "b \<in> (NAdh Adh)``{x}"
      using b0 xmem by (simp add:NAdh_def)
  qed
qed

lemma NAdh_whole:"x \<in> X \<Longrightarrow> X \<in> (NAdh Adh)``{x}"
  using set_pfilter_whole pfilter_mem_mesh by (auto simp:NAdh_def)

lemma LimN_isoconv:"isoconv (LimN N)"
  by (rule isoconvI1) (auto simp:LimN_def)

lemma LimCl_isoconv:"isoconv (LimCl Cl)"
  by (rule isoconvI1) (auto simp:LimCl_def intro:mesh_sub)

lemma LimAdh_isoconv:"isoconv (LimAdh Adh)"
  by (rule isoconvI1) (auto simp:LimAdh_def intro:mesh_sub)

lemma AdhCl_antiadh:"antiadh (AdhCl Cl)"
  by (rule antiadhI1) (auto simp:AdhCl_def)

lemma AdhN_antiadh:"antiadh (AdhN N)"
  by (rule antiadhI1) (auto simp:AdhN_def intro:mesh_sub)

lemma AdhLim_antiadh:"antiadh (AdhLim Lim)"
  by (rule antiadhI1) (auto simp:AdhLim_def intro:mesh_sub)


lemma ClNh_if_iso:
  assumes A0:"isspmap Cl" and A1:"iso_spmap Cl"
  shows ClNh_if_iso4:"ClN (NCl Cl) = Cl" and
        ClNh_if_iso5:"ispsmap (NCl Cl)" and
        ClNh_if_iso6:"iso_psmap (NCl Cl)"
proof-
  have P3:"\<And>x. x \<in> X \<Longrightarrow> (dual (ClN (NCl Cl)))``{x} = (dual Cl)``{x}"
  proof-
    fix x assume A2:"x \<in> X"
    have B0:"(dual Cl)``{x} \<subseteq> Pow X"
      using A0 by (auto simp:isspmap_def)
    have B1:"up_closed subset_order (Pow X) ((dual Cl)``{x})"
      by (rule iso_spmapD2[OF A0 A1])
    have "(dual (ClN (NCl Cl)))``{x} = grill X ((NCl Cl)``{x})"
      by (rule Nh_to_Cl1[OF A2])
    also have "... = grill X (grill X ((dual Cl)``{x}))"
      by (simp add:Cl_to_Nh1[OF A2])
    also have "... = (dual Cl)``{x}"
      using double_grill[OF B0] B1 by simp
    finally show "(dual (ClN (NCl Cl)))``{x} = (dual Cl)``{x}" .
  qed
  show "ClN (NCl Cl) = Cl"
    by (rule spmap_eqI[OF _ A0 P3]) (auto simp:isspmap_def ClN_def)
  show "ispsmap (NCl Cl)"
    by (auto simp:ispsmap_def NCl_def)
  show "iso_psmap (NCl Cl)"
    by (rule NCl_iso)
qed

lemma NhCl_if_iso:
  assumes is_nh:"ispsmap N" and upcl:"iso_psmap N"
  shows NhCl_if_iso1:"\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> NCl (ClN N) \<longleftrightarrow> (x, A) \<in> N" and
        NhCl_if_iso2:"NCl (ClN N) = N" and
        NhCl_if_iso3:"isspmap (ClN N)" and
        NhCl_if_iso4:"iso_spmap (ClN N)"
proof-
  have P0:"\<And>x. x \<in> X \<Longrightarrow> (NCl (ClN N))``{x} = N``{x}"
  proof-
    fix x assume xmem:"x \<in> X"
    have B0:"N``{x} \<subseteq> Pow X"
      using is_nh by (auto simp:ispsmap_def)
    have B1:"up_closed subset_order (Pow X) (N``{x})"
      by (rule iso_psmapD2[OF upcl xmem])
    have "(NCl (ClN N))``{x} = grill X ((dual (ClN N))``{x})"
      by (rule Cl_to_Nh1[OF xmem])
    also have "... = grill X (grill X (N``{x}))"
      by (simp add:Nh_to_Cl1[OF xmem])
    also have "... = N``{x}"
      using double_grill[OF B0] B1 by simp
    finally show "(NCl (ClN N))``{x} = N``{x}" .
  qed
  show "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> NCl (ClN N) \<longleftrightarrow> (x, A) \<in> N"
    using P0 by blast
  show "NCl (ClN N) = N"
    by (rule psmap_eqI[OF _ is_nh P0]) (auto simp:ispsmap_def NCl_def)
  show "isspmap (ClN N)"
    by (auto simp:isspmap_def ClN_def)
  show "iso_spmap (ClN N)"
    by (rule ClN_iso)
qed

lemma LimN_Inter:
  assumes A0:"prtop_nh N" and A1:"ispsmap N" and A2:"x \<in> X"
  shows "\<Inter>{\<F>. (\<F>, x) \<in> LimN N} = N``{x}"
proof-
  have B0:"N``{x} \<in> pfilters"
    using A0 A2 by (simp add:prtop_nh_def)
  have B1:"(N``{x}, x) \<in> LimN N"
    using Nh_to_Lim2[OF A1 A2 B0] by simp
  have B2:"\<And>\<F>. (\<F>, x) \<in> LimN N \<Longrightarrow> N``{x} \<subseteq> \<F>"
  proof-
    fix \<F> assume "(\<F>, x) \<in> LimN N"
    then have "\<F> \<in> pfilters"
      by (simp add:LimN_def)
    then show "N``{x} \<subseteq> \<F>"
      using Nh_to_Lim2[OF A1 A2] \<open>(\<F>, x) \<in> LimN N\<close> by simp
  qed
  show ?thesis
    using B1 B2 by blast
qed

lemma LimNh_if_prtop:
  assumes prt:"prtop_nh N" and is_nh:"ispsmap N"
  shows LimNh_if_prtop1:"is_prtop (LimN N)" and
        LimNh_if_prtop2:"NLim (LimN N) = N"
proof-
  have B0:"isconvs (LimN N)"
    by (auto simp:isconvs_def LimN_def)
  have B1:"isoconv (LimN N)"
    by (rule LimN_isoconv)
  have B2:"centered (LimN N)"
  proof(rule centeredI1)
    fix x assume xmem:"x \<in> X"
    have "lcro subset_order (Pow X) {x} \<in> pfilters"
      using set_lcro_pfilter xmem by simp
    moreover have "\<And>A. \<lbrakk>A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> A \<in> lcro subset_order (Pow X) {x}"
      using prt xmem by (auto simp:prtop_nh_def lcro_iff)
    ultimately show "(lcro subset_order (Pow X) {x}, x) \<in> LimN N"
      using xmem by (simp add:LimN_def)
  qed
  have B3:"onpconv (LimN N)"
  proof(rule onpconvI1)
    fix x assume xmem:"x \<in> X"
    have "N``{x} \<in> pfilters"
      using prt xmem by (simp add:prtop_nh_def)
    then show "(\<Inter>{\<F>. (\<F>, x) \<in> LimN N}, x) \<in> LimN N"
      using LimN_Inter[OF prt is_nh xmem] Nh_to_Lim2[OF is_nh xmem] by simp
  qed
  show "is_prtop (LimN N)"
    using B0 B1 B2 B3 by (simp add:is_prtop_def)
  show "NLim (LimN N) = N"
  proof(rule psmap_eqI)
    show "ispsmap (NLim (LimN N))"
      by (auto simp:ispsmap_def NLim_def)
    show "ispsmap N"
      by (rule is_nh)
    fix x assume xmem:"x \<in> X"
    show "(NLim (LimN N))``{x} = N``{x}"
      using Lim_to_Nh2[OF B0 B2 xmem] LimN_Inter[OF prt is_nh xmem] by simp
  qed
qed

lemma NhLim_if_prtop:
  assumes prt:"is_prtop Lim"
  shows NhLim_if_prtop1:"prtop_nh (NLim Lim)" and
        NhLim_if_prtop2:"LimN (NLim Lim) = Lim"
proof-
  have A0:"isconvs Lim" and A1:"centered Lim" and A2:"isoconv Lim" and A3:"onpconv Lim"
    using prt by (simp_all add:is_prtop_def)
  have P0:"\<And>x. x \<in> X \<Longrightarrow> ((NLim Lim)``{x}, x) \<in> Lim"
    by (rule onpconvD2[OF A3 A1 A0])
  have P1:"\<And>x. x \<in> X \<Longrightarrow> (NLim Lim)``{x} \<in> pfilters"
    using P0 A0 by (auto simp:isconvs_def)
  have P2:"ispsmap (NLim Lim)"
    by (auto simp:ispsmap_def NLim_def)
  show "prtop_nh (NLim Lim)"
    unfolding prtop_nh_def
  proof(intro conjI ballI allI impI)
    show "\<And>x. x \<in> X \<Longrightarrow> (NLim Lim)``{x} \<in> pfilters"
      by (rule P1)
    fix A x assume "x \<in> X \<and> A \<in> Pow X \<and> (x, A) \<in> NLim Lim"
    then obtain B0:"x \<in> X" and B1:"(x, A) \<in> NLim Lim"
      by blast
    have "lcro subset_order (Pow X) {x} \<in> pfilters"
      using set_lcro_pfilter B0 by simp
    moreover have "(lcro subset_order (Pow X) {x}, x) \<in> Lim"
      by (rule centeredD1[OF A1 B0])
    ultimately have "A \<in> lcro subset_order (Pow X) {x}"
      using NLim_memD[OF B1] by blast
    then show "x \<in> A"
      by (simp add:lcro_iff)
  qed
  show "LimN (NLim Lim) = Lim"
  proof(rule convs_eqI)
    show "isconvs (LimN (NLim Lim))"
      by (auto simp:isconvs_def LimN_def)
    show "isconvs Lim"
      by (rule A0)
    fix \<F> x assume B0:"\<F> \<in> pfilters" and B1:"x \<in> X"
    have "(\<F>, x) \<in> LimN (NLim Lim) \<longleftrightarrow> (NLim Lim)``{x} \<subseteq> \<F>"
      by (rule Nh_to_Lim2[OF P2 B1 B0])
    also have "... \<longleftrightarrow> (\<F>, x) \<in> Lim"
    proof
      assume "(NLim Lim)``{x} \<subseteq> \<F>"
      then show "(\<F>, x) \<in> Lim"
        using isoconvD1[OF A2 B0 P0[OF B1]] by simp
    next
      assume "(\<F>, x) \<in> Lim"
      then show "(NLim Lim)``{x} \<subseteq> \<F>"
        using B0 by (auto simp:NLim_def)
    qed
    finally show "(\<F>, x) \<in> LimN (NLim Lim) \<longleftrightarrow> (\<F>, x) \<in> Lim" .
  qed
qed

lemma NhAdh_if_iso:
  assumes inh:"ispsmap N" and iso:"iso_psmap N" and ntr:"\<And>x. x \<in> X \<Longrightarrow> N``{x} \<noteq> {}"
  shows NhAdh_if_iso1:"NAdh (AdhN N) = N"
proof(rule psmap_eqI)
  show "ispsmap (NAdh (AdhN N))"
    by (auto simp:ispsmap_def NAdh_def)
  show "ispsmap N"
    by (rule inh)
  fix x assume xmem:"x \<in> X"
  have P0:"\<And>A. A \<in> (NAdh (AdhN N))``{x} \<longleftrightarrow> A \<in> Pow X \<and> (\<forall>\<F>\<in>pfilters. N``{x} # \<F> \<longrightarrow> {A} # \<F>)"
    using xmem Nh_to_Adh2[OF inh xmem] by (auto simp:NAdh_def)
  show "(NAdh (AdhN N))``{x} = N``{x}"
  proof
    show "N``{x} \<subseteq> (NAdh (AdhN N))``{x}"
    proof
      fix A assume "A \<in> N``{x}"
      then have "A \<in> Pow X" and "\<And>\<F>. N``{x} # \<F> \<Longrightarrow> {A} # \<F>"
        using inh mesh_sub by (auto simp:ispsmap_def)
      then show "A \<in> (NAdh (AdhN N))``{x}"
        using P0 by blast
    qed
  next
    show "(NAdh (AdhN N))``{x} \<subseteq> N``{x}"
    proof
      fix A assume A0:"A \<in> (NAdh (AdhN N))``{x}"
      then have B0:"A \<in> Pow X" and B1:"\<And>\<F>. \<lbrakk>\<F> \<in> pfilters; N``{x} # \<F>\<rbrakk> \<Longrightarrow> {A} # \<F>"
        using P0 by blast+
      show "A \<in> N``{x}"
      proof(rule ccontr)
        assume B2:"A \<notin> N``{x}"
        have B3:"\<And>B. B \<in> N``{x} \<Longrightarrow> \<not> B \<subseteq> A"
          using iso_psmapD3[OF iso xmem _ B0] B2 by blast
        have B4:"N``{x} # {X - A}"
        proof-
          have "\<And>B. B \<in> N``{x} \<Longrightarrow> B \<inter> (X - A) \<noteq> {}"
          proof-
            fix B assume "B \<in> N``{x}"
            then have "B \<subseteq> X"
              using inh by (auto simp:ispsmap_def)
            then show "B \<inter> (X - A) \<noteq> {}"
              using B3[OF \<open>B \<in> N``{x}\<close>] by blast
          qed
          then show ?thesis
            by (simp add:mesh_def)
        qed
        have B5:"X - A \<noteq> {}"
        proof
          assume "X - A = {}"
          obtain B where "B \<in> N``{x}"
            using ntr[OF xmem] by blast
          then have "B \<inter> (X - A) \<noteq> {}"
            using B4 by (simp add:mesh_def)
          then show False
            using \<open>X - A = {}\<close> by simp
        qed
        then have B6:"lcro subset_order (Pow X) (X - A) \<in> pfilters"
          using set_lcro_pfilter by simp
        have B7:"N``{x} # lcro subset_order (Pow X) (X - A)"
          using mesh_lcro[OF _ B4] by simp
        then have "{A} # lcro subset_order (Pow X) (X - A)"
          using B1[OF B6] by simp
        then have "X - A \<in> lcro subset_order (Pow X) (X - A)"
          by (simp add:lcro_iff)
        then show False
          using B0 B5 \<open>{A} # lcro subset_order (Pow X) (X - A)\<close> lcro_pfilter_iff
            pfilter_mesh_single_iff by auto
      qed
    qed
  qed
qed

lemma ClAdh_if_iso:
  assumes A0:"isspmap Cl" and A1:"iso_spmap Cl" and A2:"Cl``{{}} = {}"
  shows ClAdh_if_iso1:"ClAdh (AdhCl Cl) = Cl"
proof
  show "ClAdh (AdhCl Cl) \<subseteq> Cl"
    using ClAdh_ext A0 by (simp add:isspmap_def)
  show "Cl \<subseteq> ClAdh (AdhCl Cl)"
  proof
    fix p assume "p \<in> Cl"
    then obtain A x where B0:"p = (A, x)" and B1:"A \<in> Pow X" and B2:"x \<in> X" and B3:"(A, x) \<in> Cl"
      using A0 by (auto simp:isspmap_def)
    have B4:"A \<noteq> {}"
      using A2 B3 by blast
    have B5:"lcro subset_order (Pow X) A \<in> pfilters"
      using set_lcro_pfilter B1 B4 by simp
    have "(lcro subset_order (Pow X) A, x) \<in> AdhCl Cl"
    proof(rule AdhCl_memI)
      show "lcro subset_order (Pow X) A \<in> pfilters"
        by (rule B5)
      show "x \<in> X"
        by (rule B2)
      fix B assume "B \<in> Pow X" and "B \<in> lcro subset_order (Pow X) A"
      then have "A \<subseteq> B"
        by (simp add:lcro_iff)
      then show "(B, x) \<in> Cl"
        using iso_spmapD1[OF A1 \<open>B \<in> Pow X\<close>] B3 by blast
    qed
    moreover have "A \<in> lcro subset_order (Pow X) A"
      using B1 by (simp add:lcro_iff)
    ultimately show "p \<in> ClAdh (AdhCl Cl)"
      using B0 B1 B2 B5 by (auto simp:ClAdh_def)
  qed
qed

lemma LimCl_if_prtop:
  assumes prt:"is_prtop Lim"
  shows LimCl_if_prtop1:"\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters; x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim)" and
        LimCl_if_prtop2:"ClLim Lim = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}" and
        LimCl_if_prtop3:"(ClLim Lim)``{{}} = {}" and
        LimCl_if_prtop4:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> (ClLim Lim)``{A}" and
        LimCl_if_prtop5:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (ClLim Lim)``{A \<union> B} = (ClLim Lim)``{A} \<union> (ClLim Lim)``{B}" and
        LimCl_if_prtop6:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (ClLim Lim)``{A} \<subseteq> (ClLim Lim)``{B}" and
        LimCl_if_prtop7:"prtop_cl (ClLim Lim)" and
        LimCl_if_prtop8:"isspmap (ClLim Lim)" and
        LimCl_if_prtop9:"LimCl (ClLim Lim) = Lim"
proof-
  have A0:"isconvs Lim" and A1:"centered Lim" and A2:"isoconv Lim" and A3:"onpconv Lim"
    using prt by (simp_all add:is_prtop_def)
  have vic:"\<And>x. x \<in> X \<Longrightarrow> ((NLim Lim)``{x}, x) \<in> Lim"
    by (rule onpconvD2[OF A3 A1 A0])
  have vicp:"\<And>x. x \<in> X \<Longrightarrow> pow.pfilter ((NLim Lim)``{x})"
    using vic A0 by (auto simp:isconvs_def)
  have vicle:"\<And>\<F> x. (\<F>, x) \<in> Lim \<Longrightarrow> (NLim Lim)``{x} \<subseteq> \<F>"
    using A0 by (auto simp:NLim_def isconvs_def)
  show Q0:"\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters; x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim)"
  proof-
    fix \<F> x assume pfil:"\<F> \<in> pfilters" and xmem:"x \<in> X"
    let ?N="(NLim Lim)``{x}"
    have B0:"(\<F>, x) \<in> LimCl (ClLim Lim) \<longleftrightarrow> (\<forall>A\<in>Pow X. {A} # \<F> \<longrightarrow> {A} # ?N)"
      using pfil xmem ClLim_mem_iff[OF prt xmem] by (auto simp:LimCl_def)
    show "(\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim)" (is "?L \<longleftrightarrow> ?R")
    proof
      assume ?L
      then have "?N \<subseteq> \<F>"
        by (rule vicle)
      then show ?R
        using B0 mesh_sub by blast
    next
      assume ?R
      then have B1:"\<And>A. \<lbrakk>A \<in> Pow X; {A} # \<F>\<rbrakk> \<Longrightarrow> {A} # ?N"
        using B0 by blast
      have "?N \<subseteq> \<F>"
      proof
        fix V assume B2:"V \<in> ?N"
        then have B3:"V \<subseteq> X"
          by (simp add:NLim_def)
        show "V \<in> \<F>"
        proof(rule ccontr)
          assume "V \<notin> \<F>"
          then have "{X - V} # \<F>"
            using pfilter_mesh_single_iff[of \<F> "X - V"] pfil B3 by (simp add:Diff_Diff_Int Int_absorb1)
          then have "{X - V} # ?N"
            using B1 by simp
          then show False
            using B2 by (auto simp:mesh_def)
        qed
      qed
      then show ?L
        using isoconvD1[OF A2 pfil vic[OF xmem]] by simp
    qed
  qed
  show Q1:"ClLim Lim = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}"
  proof(intro set_eqI)
    fix p
    show "p \<in> ClLim Lim \<longleftrightarrow> p \<in> {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F>\<in>pfilters. A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}"
    proof(cases p)
      case (Pair A x)
      show ?thesis
      proof(cases "A \<in> Pow X \<and> x \<in> X")
        case True
        then show ?thesis
          using Pair Lim_to_Cl20[OF A0 A2, of x A] by auto
      next
        case False
        then show ?thesis
          using Pair by (auto simp:ClLim_def)
      qed
    qed
  qed
  show Q2:"(ClLim Lim)``{{}} = {}"
    by (rule ClLim_empty)
  show Q3:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> (ClLim Lim)``{A}"
  proof-
    fix A assume amem:"A \<in> Pow X"
    show "A \<subseteq> (ClLim Lim)``{A}"
    proof
      fix x assume xa:"x \<in> A"
      then have xmem:"x \<in> X"
        using amem by blast
      have "lcro subset_order (Pow X) {x} \<in> pfilters"
        using set_lcro_pfilter xmem by simp
      moreover have "{A} # lcro subset_order (Pow X) {x}"
        using xa by (auto simp:mesh_def lcro_iff)
      ultimately show "x \<in> (ClLim Lim)``{A}"
        using centeredD1[OF A1 xmem] amem xmem by (auto simp:ClLim_def)
    qed
  qed
  show Q5:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (ClLim Lim)``{A} \<subseteq> (ClLim Lim)``{B}"
    by (rule iso_spmapD1[OF ClLim_iso])
  show Q4:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (ClLim Lim)``{A \<union> B} = (ClLim Lim)``{A} \<union> (ClLim Lim)``{B}"
  proof-
    fix A B assume amem:"A \<in> Pow X" and bmem:"B \<in> Pow X"
    show "(ClLim Lim)``{A \<union> B} = (ClLim Lim)``{A} \<union> (ClLim Lim)``{B}"
    proof
      show "(ClLim Lim)``{A \<union> B} \<subseteq> (ClLim Lim)``{A} \<union> (ClLim Lim)``{B}"
      proof
        fix x assume B0:"x \<in> (ClLim Lim)``{A \<union> B}"
        then have xmem:"x \<in> X"
          by (simp add:ClLim_def)
        have "{A \<union> B} # (NLim Lim)``{x}"
          using ClLim_mem_iff[OF prt xmem, of "A \<union> B"] amem bmem B0 by simp
        then have "A \<union> B \<in> grill X ((NLim Lim)``{x})"
          using mesh_single_grill_iff amem bmem by auto
        then have "A \<in> grill X ((NLim Lim)``{x}) \<or> B \<in> grill X ((NLim Lim)``{x})"
          using grill_pfilter_Un[OF vicp[OF xmem]] amem bmem by simp
        then have "{A} # (NLim Lim)``{x} \<or> {B} # (NLim Lim)``{x}"
          using mesh_single_grill_iff amem bmem by auto
        then show "x \<in> (ClLim Lim)``{A} \<union> (ClLim Lim)``{B}"
          using ClLim_mem_iff[OF prt xmem amem] ClLim_mem_iff[OF prt xmem bmem] by blast
      qed
    next
      show "(ClLim Lim)``{A} \<union> (ClLim Lim)``{B} \<subseteq> (ClLim Lim)``{A \<union> B}"
        using Q5[of "A \<union> B" A] Q5[of "A \<union> B" B] amem bmem by blast
    qed
  qed
  show Q6:"prtop_cl (ClLim Lim)"
    using Q2 Q3 Q4 by (simp add:prtop_cl_def)
  show Q7:"isspmap (ClLim Lim)"
    by (auto simp:isspmap_def ClLim_def)
  show Q8:"LimCl (ClLim Lim) = Lim"
  proof(rule convs_eqI)
    show "isconvs (LimCl (ClLim Lim))"
      by (auto simp:isconvs_def LimCl_def)
    show "isconvs Lim"
      by (rule A0)
  qed (simp add:Q0)
qed

lemma ext_LimCl:
  assumes CCl2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
  shows ext_LimCl1:"\<And>x. x \<in> X \<Longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> LimCl Cl" and
        ext_LimCl2:"\<And>x. x \<in> X \<Longrightarrow> {} \<notin> {V \<in> Pow X. x \<notin> Cl``{X - V}}"
proof-
  show P0:"\<And>x. x \<in> X \<Longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> LimCl Cl"
  proof-
    fix x assume xmem:"x \<in> X"
    show "(lcro subset_order (Pow X) {x}, x) \<in> LimCl Cl"
    proof(rule LimCl_memI)
      show "lcro subset_order (Pow X) {x} \<in> pfilters"
        using set_lcro_pfilter xmem by simp
      show "x \<in> X"
        by (rule xmem)
      fix A assume "A \<in> Pow X" and "{A} # lcro subset_order (Pow X) {x}"
      then have "x \<in> A"
        using xmem by (auto simp:mesh_def lcro_iff)
      then show "(A, x) \<in> Cl"
        using CCl2[OF \<open>A \<in> Pow X\<close>] by blast
    qed
  qed
  show P1:"\<And>x. x \<in> X \<Longrightarrow> {} \<notin> {V \<in> Pow X. x \<notin> Cl``{X - V}}"
    using CCl2[of X] by auto
qed

lemma LimCl_add_iso:
  assumes CCl3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B} = Cl``{A} \<union> Cl``{B}"
  shows "\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}"
proof-
  fix A B assume B0:"B \<in> Pow X" and AB:"A \<subseteq> B"
  then obtain B1:"A \<in> Pow X" and B2:"B - A \<in> Pow X" and B3:"B = (B - A) \<union> A"
    by blast
  then have "Cl``{B} = Cl``{B - A} \<union> Cl``{A}"
    using CCl3[of "B - A" A] by presburger
  then show "Cl``{A} \<subseteq> Cl``{B}"
    by blast
qed

lemma LimCl_add:
  assumes CCl1:"Cl``{{}} = {}" and
          CCl3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B} = Cl``{A} \<union> Cl``{B}"
  shows "\<And>x. x \<in> X \<Longrightarrow> filter_on subset_order (Pow X) {V \<in> Pow X. x \<notin> Cl``{X - V}}"
proof-
  fix x assume xmem:"x \<in> X"
  let ?V="{V \<in> Pow X. x \<notin> Cl``{X - V}}"
  show "filter_on subset_order (Pow X) ?V"
  proof(rule set_filterI)
    show "?V \<subseteq> Pow X"
      by blast
    have "X \<in> ?V"
      using CCl1 by auto
    then show "?V \<noteq> {}"
      by blast
    show "\<And>A B. \<lbrakk>A \<in> ?V; B \<in> ?V\<rbrakk> \<Longrightarrow> A \<inter> B \<in> ?V"
    proof-
      fix A B assume A0:"A \<in> ?V" and A1:"B \<in> ?V"
      then have "Cl``{X - (A \<inter> B)} = Cl``{X - A} \<union> Cl``{X - B}"
        using CCl3[of "X - A" "X - B"] by (simp add:Diff_Int)
      then show "A \<inter> B \<in> ?V"
        using A0 A1 by auto
    qed
    show "\<And>A B. \<lbrakk>A \<in> ?V; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> ?V"
    proof-
      fix A B assume A0:"A \<in> ?V" and A1:"B \<subseteq> X" and A2:"A \<subseteq> B"
      then have "Cl``{X - B} \<subseteq> Cl``{X - A}"
        using LimCl_add_iso[OF CCl3, of "X - A" "X - B"] by blast
      then show "B \<in> ?V"
        using A0 A1 by auto
    qed
  qed
qed

lemma LimCl_iso:
  assumes CCl4:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}"
  shows Cl_mem_iff1:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (X - V, x) \<notin> Cl \<longrightarrow> V \<inter> A \<noteq> {})" and
        Cl_mem_iff2:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (X - A, x) \<notin> Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (V, x) \<in> Cl \<longrightarrow> V \<inter> A \<noteq> {})" and
        Cl_mem_iff4:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X; x \<in> Cl``{X - A}\<rbrakk> \<Longrightarrow> (\<forall>V\<in>Pow X. x \<notin> Cl``{X - V} \<longrightarrow> V \<inter> (X - A) \<noteq> {})"
proof-
  show P0:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (X - V, x) \<notin> Cl \<longrightarrow> V \<inter> A \<noteq> {})"
  proof-
    fix A x assume A0:"A \<in> Pow X" and A1:"x \<in> X"
    show "(A, x) \<in> Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (X - V, x) \<notin> Cl \<longrightarrow> V \<inter> A \<noteq> {})" (is "?L \<longleftrightarrow> ?R")
    proof
      assume L:?L
      show ?R
      proof(intro ballI impI)
        fix V assume "V \<in> Pow X" and "(X - V, x) \<notin> Cl"
        show "V \<inter> A \<noteq> {}"
        proof
          assume "V \<inter> A = {}"
          then have "A \<subseteq> X - V"
            using A0 by blast
          then have "(X - V, x) \<in> Cl"
            using CCl4[of "X - V" A] L by blast
          then show False
            using \<open>(X - V, x) \<notin> Cl\<close> by simp
        qed
      qed
    next
      assume R:?R
      then have "(X - (X - A), x) \<notin> Cl \<longrightarrow> (X - A) \<inter> A \<noteq> {}"
        by simp
      moreover have "X - (X - A) = A"
        using A0 by auto
      moreover have "(X - A) \<inter> A = {}"
        by blast
      ultimately show ?L
        by simp
    qed
  qed
  show P1:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (X - A, x) \<notin> Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (V, x) \<in> Cl \<longrightarrow> V \<inter> A \<noteq> {})"
  proof-
    fix A x assume A0:"A \<in> Pow X" and A1:"x \<in> X"
    show "(X - A, x) \<notin> Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (V, x) \<in> Cl \<longrightarrow> V \<inter> A \<noteq> {})" (is "?L \<longleftrightarrow> ?R")
    proof
      assume L:?L
      show ?R
      proof(intro ballI impI)
        fix V assume "V \<in> Pow X" and "(V, x) \<in> Cl"
        show "V \<inter> A \<noteq> {}"
        proof
          assume "V \<inter> A = {}"
          then have "V \<subseteq> X - A"
            using \<open>V \<in> Pow X\<close> by blast
          then have "(X - A, x) \<in> Cl"
            using CCl4[of "X - A" V] \<open>(V, x) \<in> Cl\<close> by blast
          then show False
            using L by simp
        qed
      qed
    next
      assume R:?R
      then show ?L
        by auto
    qed
  qed
  show P2:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X; x \<in> Cl``{X - A}\<rbrakk> \<Longrightarrow> (\<forall>V\<in>Pow X. x \<notin> Cl``{X - V} \<longrightarrow> V \<inter> (X - A) \<noteq> {})"
  proof-
    fix A x assume "A \<in> Pow X" and "x \<in> X" and "x \<in> Cl``{X - A}"
    then show "\<forall>V\<in>Pow X. x \<notin> Cl``{X - V} \<longrightarrow> V \<inter> (X - A) \<noteq> {}"
      using P0[of "X - A" x] by simp
  qed
qed

lemma prtp_cl_mem_iff:
  assumes prt:"prtop_cl Cl"
  shows Cl_mem_iff3:"\<And>x. x \<in> X \<Longrightarrow> pow.pfilter {V \<in> Pow X. x \<notin> Cl``{X - V}}" and
        Cl_mem_iff7:"\<And>x. x \<in> X \<Longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> LimCl Cl"
proof-
  show "\<And>x. x \<in> X \<Longrightarrow> pow.pfilter {V \<in> Pow X. x \<notin> Cl``{X - V}}"
    using LimCl_add[OF prtop_clD1[OF prt] prtop_clD3[OF prt]] ext_LimCl2[OF prtop_clD2[OF prt]]
    by (simp add:set_pfilter_iff)
  show "\<And>x. x \<in> X \<Longrightarrow> (lcro subset_order (Pow X) {x}, x) \<in> LimCl Cl"
    by (rule ext_LimCl1[OF prtop_clD2[OF prt]])
qed

lemma ClLim_ps_prt:
  assumes prt:"prtop_cl Cl" and isp:"isspmap Cl"
  shows ClLim_ps_prt1:"\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> NCl Cl \<longleftrightarrow> A \<in> {V \<in> Pow X. (X - V, x) \<notin> Cl}" and
        ClLim_ps_prt2:"\<And>x A. x \<in> X \<Longrightarrow> A \<in> (NCl Cl)``{x} \<longleftrightarrow> A \<in> {V \<in> Pow X. (X - V, x) \<notin> Cl}" and
        ClLim_ps_prt3:"\<And>x. x \<in> X \<Longrightarrow> (NCl Cl)``{x} = \<Inter>{\<F>. (\<F>, x) \<in> LimCl Cl}" and
        ClLim_ps_prt4:"\<And>x. x \<in> X \<Longrightarrow> ((NCl Cl)``{x}, x) \<in> LimCl Cl"
proof-
  have CCl4:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}"
    by (rule prtop_clD4[OF prt])
  show P1:"\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> NCl Cl \<longleftrightarrow> A \<in> {V \<in> Pow X. (X - V, x) \<notin> Cl}"
  proof-
    fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
    have "(x, A) \<in> NCl Cl \<longleftrightarrow> (\<forall>V\<in>Pow X. (V, x) \<in> Cl \<longrightarrow> V \<inter> A \<noteq> {})"
      using xmem amem isp by (auto simp:NCl_def mesh_def isspmap_def Int_commute)
    then show "(x, A) \<in> NCl Cl \<longleftrightarrow> A \<in> {V \<in> Pow X. (X - V, x) \<notin> Cl}"
      using Cl_mem_iff2[OF CCl4 amem xmem] amem by simp
  qed
  show P2:"\<And>x A. x \<in> X \<Longrightarrow> A \<in> (NCl Cl)``{x} \<longleftrightarrow> A \<in> {V \<in> Pow X. (X - V, x) \<notin> Cl}"
    using P1 by (auto simp:NCl_def)
  have P3:"\<And>x. x \<in> X \<Longrightarrow> (NCl Cl)``{x} = {V \<in> Pow X. (X - V, x) \<notin> Cl}"
    using P2 by blast
  show P4:"\<And>x. x \<in> X \<Longrightarrow> ((NCl Cl)``{x}, x) \<in> LimCl Cl"
  proof-
    fix x assume xmem:"x \<in> X"
    show "((NCl Cl)``{x}, x) \<in> LimCl Cl"
    proof(rule LimCl_memI)
      show "(NCl Cl)``{x} \<in> pfilters"
        using Cl_mem_iff3[OF prt xmem] P3[OF xmem] by simp
      show "x \<in> X"
        by (rule xmem)
      fix A assume amem:"A \<in> Pow X" and amesh:"{A} # (NCl Cl)``{x}"
      have "\<And>V. \<lbrakk>V \<in> Pow X; (X - V, x) \<notin> Cl\<rbrakk> \<Longrightarrow> V \<inter> A \<noteq> {}"
        using amesh P3[OF xmem] by (auto simp:mesh_def Int_commute)
      then show "(A, x) \<in> Cl"
        using Cl_mem_iff1[OF CCl4 amem xmem] by simp
    qed
  qed
  show "\<And>x. x \<in> X \<Longrightarrow> (NCl Cl)``{x} = \<Inter>{\<F>. (\<F>, x) \<in> LimCl Cl}"
  proof-
    fix x assume xmem:"x \<in> X"
    have "\<And>\<F>. (\<F>, x) \<in> LimCl Cl \<Longrightarrow> (NCl Cl)``{x} \<subseteq> \<F>"
    proof
      fix \<F> V assume A0:"(\<F>, x) \<in> LimCl Cl" and A1:"V \<in> (NCl Cl)``{x}"
      then have B0:"V \<in> Pow X" and B1:"(X - V, x) \<notin> Cl" and B2:"pow.pfilter \<F>"
        using P3[OF xmem] by (auto simp:LimCl_def)
      show "V \<in> \<F>"
      proof(rule ccontr)
        assume "V \<notin> \<F>"
        then have "{X - V} # \<F>"
          using pfilter_mesh_single_iff[OF B2, of "X - V"] B0 by (simp add:Diff_Diff_Int Int_absorb1)
        then have "(X - V, x) \<in> Cl"
          using A0 by (simp add:LimCl_def)
        then show False
          using B1 by simp
      qed
    qed
    then show "(NCl Cl)``{x} = \<Inter>{\<F>. (\<F>, x) \<in> LimCl Cl}"
      using P4[OF xmem] by blast
  qed
qed

lemma ClLim_if_prtop:
  assumes A0:"isspmap Cl" and A1:"prtop_cl Cl"
  shows ClLim_if_prt1:"ClLim (LimCl Cl) = Cl" and
        ClLim_if_prt2:"is_prtop (LimCl Cl)"
proof-
  show "ClLim (LimCl Cl) = Cl"
  proof
    show "ClLim (LimCl Cl) \<subseteq> Cl"
      using ClLim_ext A0 by (simp add:isspmap_def)
    show "Cl \<subseteq> ClLim (LimCl Cl)"
    proof
      fix p assume "p \<in> Cl"
      then obtain A x where B0:"p = (A, x)" and B1:"A \<in> Pow X" and B2:"x \<in> X" and B3:"(A, x) \<in> Cl"
        using A0 by (auto simp:isspmap_def)
      have B4:"((NCl Cl)``{x}, x) \<in> LimCl Cl"
        by (rule ClLim_ps_prt4[OF A1 A0 B2])
      then have B5:"(NCl Cl)``{x} \<in> pfilters"
        by (simp add:LimCl_def)
      have "{A} # (NCl Cl)``{x}"
      proof-
        have "\<And>V. \<lbrakk>V \<in> Pow X; (X - V, x) \<notin> Cl\<rbrakk> \<Longrightarrow> A \<inter> V \<noteq> {}"
        proof-
          fix V assume "V \<in> Pow X" and "(X - V, x) \<notin> Cl"
          then show "A \<inter> V \<noteq> {}"
            using Cl_mem_iff1[OF prtop_clD4[OF A1] B1 B2] B3 by (auto simp:Int_commute)
        qed
        then show ?thesis
          using ClLim_ps_prt2[OF A1 A0 B2] by (auto simp:mesh_def)
      qed
      then show "p \<in> ClLim (LimCl Cl)"
        using B0 B1 B2 B4 B5 by (auto simp:ClLim_def)
    qed
  qed
  show "is_prtop (LimCl Cl)"
    unfolding is_prtop_def
  proof(intro conjI)
    show "isconvs (LimCl Cl)"
      by (auto simp:isconvs_def LimCl_def)
    show "centered (LimCl Cl)"
      by (rule centeredI1) (rule Cl_mem_iff7[OF A1])
    show "isoconv (LimCl Cl)"
      by (rule LimCl_isoconv)
    show "onpconv (LimCl Cl)"
      by (rule onpconvI1) (simp add:ClLim_ps_prt3[OF A1 A0, symmetric] ClLim_ps_prt4[OF A1 A0])
  qed
qed

lemma LimCl_imp_prtop:
  assumes A0:"isspmap Cl" and A1:"ClLim (LimCl Cl) = Cl" and A2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
  shows "prtop_cl Cl"
  unfolding prtop_cl_def
proof(intro conjI ballI)
  show "Cl``{{}} = {}"
    using ClLim_empty A1 by metis
  show "\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
    by (rule A2)
  fix A B assume amem:"A \<in> Pow X" and bmem:"B \<in> Pow X"
  have iso:"\<And>A B. \<lbrakk>B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}"
    using iso_spmapD1[OF ClLim_iso] A1 by metis
  show "Cl``{A \<union> B} = Cl``{A} \<union> Cl``{B}"
  proof
    show "Cl``{A \<union> B} \<subseteq> Cl``{A} \<union> Cl``{B}"
    proof
      fix x assume "x \<in> Cl``{A \<union> B}"
      then have "x \<in> (ClLim (LimCl Cl))``{A \<union> B}"
        using A1 by simp
      then obtain \<F> where B0:"\<F> \<in> pfilters" and B1:"{A \<union> B} # \<F>" and B2:"(\<F>, x) \<in> LimCl Cl" and B3:"x \<in> X"
        by (auto simp:ClLim_def)
      have "A \<union> B \<in> grill X \<F>"
        using mesh_single_grill_iff B1 amem bmem by auto
      then have "A \<in> grill X \<F> \<or> B \<in> grill X \<F>"
        using grill_pfilter_Un[of \<F> A B] B0 amem bmem by simp
      then have "{A} # \<F> \<or> {B} # \<F>"
        using mesh_single_grill_iff amem bmem by auto
      then have "x \<in> (ClLim (LimCl Cl))``{A} \<union> (ClLim (LimCl Cl))``{B}"
        using B0 B2 B3 amem bmem by (auto simp:ClLim_def)
      then show "x \<in> Cl``{A} \<union> Cl``{B}"
        using A1 by simp
    qed
  next
    show "Cl``{A} \<union> Cl``{B} \<subseteq> Cl``{A \<union> B}"
      using iso[of "A \<union> B" A] iso[of "A \<union> B" B] amem bmem by blast
  qed
qed

lemma ClLim_imp_prtop:
  assumes A0:"isconvs Lim" and A1:"LimCl (ClLim Lim) = Lim" and cntr:"centered Lim"
  shows "is_prtop Lim"
  unfolding is_prtop_def
proof(intro conjI)
  show "isconvs Lim"
    by (rule A0)
  show "centered Lim"
    by (rule cntr)
  show "isoconv Lim"
    using LimCl_isoconv A1 by metis
  show "onpconv Lim"
  proof(rule onpconvI1)
    fix x assume xmem:"x \<in> X"
    let ?N="\<Inter>{\<F>. (\<F>, x) \<in> Lim}"
    have B0:"\<And>\<F>. (\<F>, x) \<in> Lim \<Longrightarrow> pow.pfilter \<F>"
      using A0 by (auto simp:isconvs_def)
    have B1:"{\<F>. (\<F>, x) \<in> Lim} \<noteq> {}"
      using centeredD1[OF cntr xmem] by blast
    have B2:"pow.pfilter ?N"
      using set_pfilter_Inter[OF B1] B0 by simp
    have "(?N, x) \<in> LimCl (ClLim Lim)"
    proof(rule LimCl_memI)
      show "?N \<in> pfilters"
        using B2 by simp
      show "x \<in> X"
        by (rule xmem)
      fix A assume amem:"A \<in> Pow X" and amesh:"{A} # ?N"
      have "\<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim"
      proof(rule ccontr)
        assume "\<not>(\<exists>\<F>\<in>pfilters. {A} # \<F> \<and> (\<F>, x) \<in> Lim)"
        then have "\<And>\<F>. (\<F>, x) \<in> Lim \<Longrightarrow> X - A \<in> \<F>"
          using B0 pfilter_mesh_single_iff[of _ A] amem by auto
        then have "X - A \<in> ?N"
          using B1 by blast
        then show False
          using amesh by (auto simp:mesh_def)
      qed
      then show "(A, x) \<in> ClLim Lim"
        using amem xmem by (auto simp:ClLim_def)
    qed
    then show "(?N, x) \<in> Lim"
      using A1 by simp
  qed
qed

lemma NhLim_imp_prtop:
  assumes A0:"isconvs Lim" and A1:"LimN (NLim Lim) = Lim" and A2:"centered Lim"
  shows "is_prtop Lim"
  unfolding is_prtop_def
proof(intro conjI)
  show "isconvs Lim"
    by (rule A0)
  show "centered Lim"
    by (rule A2)
  show "isoconv Lim"
    using LimN_isoconv A1 by metis
  show "onpconv Lim"
  proof(rule onpconvI1)
    fix x assume xmem:"x \<in> X"
    let ?N="\<Inter>{\<F>. (\<F>, x) \<in> Lim}"
    have B0:"\<And>\<F>. (\<F>, x) \<in> Lim \<Longrightarrow> pow.pfilter \<F>"
      using A0 by (auto simp:isconvs_def)
    have B1:"{\<F>. (\<F>, x) \<in> Lim} \<noteq> {}"
      using centeredD1[OF A2 xmem] by blast
    have B2:"pow.pfilter ?N"
      using set_pfilter_Inter[OF B1] B0 by simp
    have B3:"(NLim Lim)``{x} = ?N"
      by (rule Lim_to_Nh2[OF A0 A2 xmem])
    have B4:"ispsmap (NLim Lim)"
      by (auto simp:ispsmap_def NLim_def)
    have "(?N, x) \<in> LimN (NLim Lim)"
      using Nh_to_Lim2[OF B4 xmem] B2 B3 by simp
    then show "(?N, x) \<in> Lim"
      using A1 by simp
  qed
qed

lemma LimNh_imp_prtop:
  assumes A0:"\<And>A x. \<lbrakk>x \<in> X; A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> x \<in> A" and
          A1:"NLim (LimN N) = N" and
          is_nh:"ispsmap N"
  shows "prtop_nh N"
  unfolding prtop_nh_def
proof(intro conjI ballI allI impI)
  show "\<And>A x. x \<in> X \<and> A \<in> Pow X \<and> (x, A) \<in> N \<Longrightarrow> x \<in> A"
    using A0 by blast
  fix x assume xmem:"x \<in> X"
  have B0:"N``{x} \<subseteq> lcro subset_order (Pow X) {x}"
  proof
    show "\<And>y. y \<in> N `` {x} \<Longrightarrow> y \<in> lcro subset_order (Pow X) {x}"
    proof-
      fix y assume A2:"y \<in> N``{x}"
      then show "y \<in> lcro subset_order (Pow X) {x}"
        using A0 lcro_iff is_nh ispsmapD2 by auto
    qed
  qed
  have B1:"lcro subset_order (Pow X) {x} \<in> pfilters"
    using set_lcro_pfilter xmem by simp
  have B2:"(lcro subset_order (Pow X) {x}, x) \<in> LimN N"
    using Nh_to_Lim2[OF is_nh xmem B1] B0 by simp
  have B3:"isconvs (LimN N)"
    by (auto simp:isconvs_def LimN_def)
  have "N``{x} = (NLim (LimN N))``{x}"
    using A1 by simp
  also have "... = \<Inter>{\<F>. (\<F>, x) \<in> LimN N}"
    using Lim_to_Nh1[OF B3 _ xmem] B2 by blast
  finally have B4:"N``{x} = \<Inter>{\<F>. (\<F>, x) \<in> LimN N}" .
  have "pow.pfilter (\<Inter>{\<F>. (\<F>, x) \<in> LimN N})"
    using B2 by (intro set_pfilter_Inter) (auto simp:LimN_def)
  then show "N``{x} \<in> pfilters"
    using B4 by simp
qed

lemma LimAdh_ufdet:
  assumes A0:"ufdetadh Adh"
  shows "ufdetconv (LimAdh Adh)"
proof(rule ufdetconvI1)
  fix \<F> x assume xmem:"x \<in> X" and fmem:"\<F> \<in> pfilters" and
    ufl:"\<And>\<U>. \<U> \<in> finer_ultrafilters \<F> \<Longrightarrow> (\<U>, x) \<in> LimAdh Adh"
  show "(\<F>, x) \<in> LimAdh Adh"
  proof(rule LimAdh_memI[OF fmem xmem])
    fix \<G> assume gmem:"\<G> \<in> pfilters" and gmesh:"\<G> # \<F>"
    obtain \<H> where B0:"pow.pfilter \<H>" and B1:"\<G> \<subseteq> \<H>" and B2:"\<F> \<subseteq> \<H>"
      using mesh_pfilters_finer[of \<G> \<F>] gmem fmem gmesh by auto
    obtain \<U> where B3:"ultrafilter \<U>" and B4:"\<H> \<subseteq> \<U>"
      using ultrafilter_exists[OF B0] by blast
    have B5:"\<U> \<in> pfilters"
      using ultrafilter_pfilter[OF B3] by simp
    have "(\<U>, x) \<in> LimAdh Adh"
      using ufl B3 B2 B4 by blast
    then have "(\<U>, x) \<in> Adh"
      using pfilter_mesh_self[of \<U>] B5 by (auto simp:LimAdh_def)
    then show "(\<G>, x) \<in> Adh"
      using ufdetadhD1[OF A0 gmem] B3 B1 B4 by blast
  qed
qed

lemma AdhLim_LimAdh:
  assumes A0:"isconvs Adh" and A1:"ufdetadh Adh"
  shows "AdhLim (LimAdh Adh) = Adh"
proof
  show "AdhLim (LimAdh Adh) \<subseteq> Adh"
    using LimAdh_ext A0 by (simp add:isconvs_def)
  show "Adh \<subseteq> AdhLim (LimAdh Adh)"
  proof
    fix p assume "p \<in> Adh"
    then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and B3:"(\<F>, x) \<in> Adh"
      using A0 by (auto simp:isconvs_def)
    obtain \<U> where B4:"ultrafilter \<U>" and B5:"\<F> \<subseteq> \<U>" and B6:"(\<U>, x) \<in> Adh"
      using ufdetadhD1[OF A1 B1] B3 by blast
    have B7:"\<U> \<in> pfilters"
      using ultrafilter_pfilter[OF B4] by simp
    have "(\<U>, x) \<in> LimAdh Adh"
    proof(rule LimAdh_memI[OF B7 B2])
      fix \<G> assume gmem:"\<G> \<in> pfilters" and gmesh:"\<G> # \<U>"
      then have "\<G> \<subseteq> \<U>"
        using ultrafilter_mesh[OF B4] by simp
      then show "(\<G>, x) \<in> Adh"
        using ufdetadhD1[OF A1 gmem] B4 B6 by blast
    qed
    moreover have "\<U> # \<F>"
      using pfilter_sub_mesh[OF _ B5] B7 mesh_sym by auto
    ultimately show "p \<in> AdhLim (LimAdh Adh)"
      using B0 B1 B2 B7 by (auto simp:AdhLim_def)
  qed
qed

lemma LimAdh_if_pstop:
  assumes pst:"pseudotop_adh Adh"
  shows LimAdh_if_pstop0:"isconvs (LimAdh Adh)" and
        LimAdh_if_pstop1:"centered (LimAdh Adh)" and
        LimAdh_if_pstop2:"isoconv (LimAdh Adh)" and
        LimAdh_if_pstop3:"ufdetconv (LimAdh Adh)" and
        LimAdh_if_pstop4:"is_pseudotop (LimAdh Adh)" and
        LimAdh_if_pstop5:"AdhLim (LimAdh Adh) = Adh"
proof-
  have A0:"isconvs Adh" and A1:"centered Adh" and A2:"ufdetadh Adh"
    using pst by (simp_all add:pseudotop_adh_def)
  show P0:"isconvs (LimAdh Adh)"
    by (auto simp:isconvs_def LimAdh_def)
  show P1:"centered (LimAdh Adh)"
  proof(rule centeredI1)
    fix x assume xmem:"x \<in> X"
    show "(lcro subset_order (Pow X) {x}, x) \<in> LimAdh Adh"
    proof(rule LimAdh_memI)
      show "lcro subset_order (Pow X) {x} \<in> pfilters"
        using set_lcro_pfilter xmem by simp
      show "x \<in> X"
        by (rule xmem)
      fix \<G> assume gmem:"\<G> \<in> pfilters" and gmesh:"\<G> # lcro subset_order (Pow X) {x}"
      have "\<G> \<subseteq> lcro subset_order (Pow X) {x}"
      proof
        fix G assume "G \<in> \<G>"
        have "{x} \<in> lcro subset_order (Pow X) {x}"
          using xmem by (simp add:lcro_iff)
        then have "G \<inter> {x} \<noteq> {}"
          using gmesh \<open>G \<in> \<G>\<close> unfolding mesh_def by blast
        moreover have "G \<subseteq> X"
          using gmem set_pfilter_mem_base \<open>G \<in> \<G>\<close> by simp
        ultimately show "G \<in> lcro subset_order (Pow X) {x}"
          by (auto simp:lcro_iff)
      qed
      then show "(\<G>, x) \<in> Adh"
        using ufdetadhD1[OF A2 gmem] principal_ultrafilter[OF xmem] centeredD1[OF A1 xmem] by blast
    qed
  qed
  show P2:"isoconv (LimAdh Adh)"
    by (rule LimAdh_isoconv)
  show P3:"ufdetconv (LimAdh Adh)"
    by (rule LimAdh_ufdet[OF A2])
  show P4:"is_pseudotop (LimAdh Adh)"
    using P0 P1 P2 P3 by (simp add:is_pseudotop_def)
  show P5:"AdhLim (LimAdh Adh) = Adh"
    by (rule AdhLim_LimAdh[OF A0 A2])
qed

lemma AdhLim_ufdet:
  assumes A0:"isconvs Lim" and A2:"isoconv Lim"
  shows "ufdetadh (AdhLim Lim)"
proof(rule ufdetadhI1)
  fix \<F> assume fmem:"\<F> \<in> pfilters"
  show "(AdhLim Lim)``{\<F>} = \<Union>{(AdhLim Lim)``{\<U>}|\<U>. \<U> \<in> finer_ultrafilters \<F>}" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix x assume "x \<in> ?L"
      then obtain \<U> where B0:"ultrafilter \<U>" and B1:"\<F> \<subseteq> \<U>" and B2:"(\<U>, x) \<in> Lim"
        using Lim_to_Adh21[OF A0 A2 fmem] by blast
      have B3:"\<U> \<in> pfilters"
        using ultrafilter_pfilter[OF B0] by simp
      then have "(\<U>, x) \<in> AdhLim Lim"
        using pfilter_mesh_self[of \<U>] B2 A0 by (auto simp:AdhLim_def isconvs_def)
      then show "x \<in> ?R"
        using B0 B1 by blast
    qed
  next
    show "?R \<subseteq> ?L"
    proof
      fix x assume "x \<in> ?R"
      then obtain \<U> where B0:"ultrafilter \<U>" and B1:"\<F> \<subseteq> \<U>" and B2:"(\<U>, x) \<in> AdhLim Lim"
        by blast
      then obtain \<G> where B3:"\<G> \<in> pfilters" and B4:"\<G> # \<U>" and B5:"(\<G>, x) \<in> Lim" and B6:"x \<in> X"
        by (auto simp:AdhLim_def)
      have "\<G> # \<F>"
        using mesh_sub[OF B4 _ B1] by simp
      then show "x \<in> ?L"
        using fmem B3 B5 B6 by (auto simp:AdhLim_def)
    qed
  qed
qed

lemma LimAdh_AdhLim:
  assumes A0:"isconvs Lim" and A2:"isoconv Lim" and A3:"ufdetconv Lim"
  shows "LimAdh (AdhLim Lim) = Lim"
proof
  show "Lim \<subseteq> LimAdh (AdhLim Lim)"
    using AdhLim_ext A0 by (simp add:isconvs_def)
  show "LimAdh (AdhLim Lim) \<subseteq> Lim"
  proof
    fix p assume "p \<in> LimAdh (AdhLim Lim)"
    then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and
      B3:"\<And>\<G>. \<lbrakk>\<G> \<in> pfilters; \<G> # \<F>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> AdhLim Lim"
      by (auto simp:LimAdh_def)
    have "(\<F>, x) \<in> Lim"
    proof(rule ufdetconvD1[OF A3 B2 B1])
      fix \<U> assume "\<U> \<in> finer_ultrafilters \<F>"
      then have B4:"ultrafilter \<U>" and B5:"\<F> \<subseteq> \<U>"
        by simp_all
      have B6:"\<U> \<in> pfilters"
        using ultrafilter_pfilter[OF B4] by simp
      have "\<U> # \<F>"
        using pfilter_sub_mesh[OF _ B5] B6 mesh_sym by auto
      then obtain \<G> where B7:"\<G> \<in> pfilters" and B8:"\<G> # \<U>" and B9:"(\<G>, x) \<in> Lim"
        using B3[OF B6] by (auto simp:AdhLim_def)
      have "\<G> \<subseteq> \<U>"
        using ultrafilter_mesh[OF B4] B7 B8 by simp
      then show "(\<U>, x) \<in> Lim"
        using isoconvD1[OF A2 B6 B9] by simp
    qed
    then show "p \<in> Lim"
      using B0 by simp
  qed
qed

lemma AdhLim_if_pstop:
  assumes pst:"is_pseudotop Lim"
  shows AdhLim_if_pstop0:"isconvs (AdhLim Lim)" and
        AdhLim_if_pstop1:"centered (AdhLim Lim)" and
        AdhLim_if_pstop2:"ufdetadh (AdhLim Lim)" and
        AdhLim_if_pstop4:"pseudotop_adh (AdhLim Lim)" and
        AdhLim_if_pstop5:"LimAdh (AdhLim Lim) = Lim"
proof-
  have A0:"isconvs Lim" and A1:"centered Lim" and A2:"isoconv Lim" and A3:"ufdetconv Lim"
    using pst by (simp_all add:is_pseudotop_def)
  show P0:"isconvs (AdhLim Lim)"
    by (auto simp:isconvs_def AdhLim_def)
  show P1:"centered (AdhLim Lim)"
  proof(rule centeredI1)
    fix x assume xmem:"x \<in> X"
    have "lcro subset_order (Pow X) {x} \<in> pfilters"
      using set_lcro_pfilter xmem by simp
    then show "(lcro subset_order (Pow X) {x}, x) \<in> AdhLim Lim"
      using pfilter_mesh_self[of "lcro subset_order (Pow X) {x}"] centeredD1[OF A1 xmem] xmem
      by (auto simp:AdhLim_def)
  qed
  show P2:"ufdetadh (AdhLim Lim)"
    by (rule AdhLim_ufdet[OF A0 A2])
  show P4:"pseudotop_adh (AdhLim Lim)"
    using P0 P1 P2 by (simp add:pseudotop_adh_def)
  show P5:"LimAdh (AdhLim Lim) = Lim"
    by (rule LimAdh_AdhLim[OF A0 A2 A3])
qed

lemma AdhCl_if_prdet:
  assumes A0:"prdet_adh Adh"
  shows AdhCl_if_prdet0:"isspmap (ClAdh Adh)" and
        AdhCl_if_prdet1:"AdhCl (ClAdh Adh) = Adh"
proof-
  have A1:"isconvs Adh" and A2:"prdetadh Adh"
    using A0 by (simp_all add:prdet_adh_def)
  have A3:"antiadh Adh"
    by (rule prdetadh_antitone[OF A0])
  show "isspmap (ClAdh Adh)"
    by (auto simp:isspmap_def ClAdh_def)
  show "AdhCl (ClAdh Adh) = Adh"
  proof
    show "Adh \<subseteq> AdhCl (ClAdh Adh)"
      using AdhCl_ext A1 by (simp add:isconvs_def)
    show "AdhCl (ClAdh Adh) \<subseteq> Adh"
    proof
      fix p assume "p \<in> AdhCl (ClAdh Adh)"
      then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and
        B3:"\<And>A. \<lbrakk>A \<in> Pow X; A \<in> \<F>\<rbrakk> \<Longrightarrow> (A, x) \<in> ClAdh Adh"
        by (auto simp:AdhCl_def)
      have "\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Adh``{lcro subset_order (Pow X) A}"
      proof-
        fix A assume "A \<in> \<F>"
        then have "A \<in> Pow X"
          using set_pfilter_mem_base B1 by simp
        then show "x \<in> Adh``{lcro subset_order (Pow X) A}"
          using B3[OF _ \<open>A \<in> \<F>\<close>] Adh_to_Cl20[OF A1 A3] by blast
      qed
      then have "x \<in> \<Inter>{Adh``{lcro subset_order (Pow X) A}|A. A \<in> \<F>}"
        by blast
      then have "x \<in> Adh``{\<F>}"
        using prdetadhD1[OF A2 B1] by simp
      then show "p \<in> Adh"
        using B0 by simp
    qed
  qed
qed

lemma AdhNh_if_prdet:
  assumes A0:"prdet_adh Adh" and IC1:"isconvs Adh"
  shows AdhNh_if_prdet0:"ispsmap (NAdh Adh)" and
        AdhNh_if_prdet1:"AdhN (NAdh Adh) = Adh"
proof-
  have A2:"prdetadh Adh"
    using A0 by (simp add:prdet_adh_def)
  have A3:"antiadh Adh"
    by (rule prdetadh_antitone[OF A0])
  show P0:"ispsmap (NAdh Adh)"
    by (auto simp:ispsmap_def NAdh_def)
  show "AdhN (NAdh Adh) = Adh"
  proof
    show "Adh \<subseteq> AdhN (NAdh Adh)"
      using AdhNAdh_ext IC1 by (simp add:isconvs_def)
    show "AdhN (NAdh Adh) \<subseteq> Adh"
    proof
      fix p assume "p \<in> AdhN (NAdh Adh)"
      then obtain \<F> x where B0:"p = (\<F>, x)" and B1:"\<F> \<in> pfilters" and B2:"x \<in> X" and B3:"(\<F>, x) \<in> AdhN (NAdh Adh)"
        by (auto simp:AdhN_def)
      have B4:"(NAdh Adh)``{x} # \<F>"
        using Nh_to_Adh2[OF P0 B2 B1] B3 by simp
      have "\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Adh``{lcro subset_order (Pow X) A}"
      proof-
        fix A assume amem:"A \<in> \<F>"
        then have B5:"A \<subseteq> X"
          using set_pfilter_mem_base B1 by simp
        show "x \<in> Adh``{lcro subset_order (Pow X) A}"
        proof(rule ccontr)
          assume B6:"x \<notin> Adh``{lcro subset_order (Pow X) A}"
          have "(x, X - A) \<in> NAdh Adh"
          proof(rule NAdh_memI)
            show "X - A \<in> Pow X"
              by simp
            show "x \<in> X"
              by (rule B2)
            fix \<E> assume emem:"\<E> \<in> pfilters" and eadh:"(\<E>, x) \<in> Adh"
            have "A \<notin> \<E>"
            proof
              assume "A \<in> \<E>"
              then have "lcro subset_order (Pow X) A \<subseteq> \<E>"
                using set_pfilter_lcro_sub emem by simp
              moreover have "lcro subset_order (Pow X) A \<in> pfilters"
                using set_lcro_pfilter[OF B5] set_pfilter_ne[of \<E> A] emem \<open>A \<in> \<E>\<close> by simp
              ultimately have "(lcro subset_order (Pow X) A, x) \<in> Adh"
                using antiadhD1[OF A3 _ eadh] by simp
              then show False
                using B6 by simp
            qed
            then show "{X - A} # \<E>"
              using pfilter_mesh_single_iff[of \<E> "X - A"] emem B5 by (simp add:Diff_Diff_Int Int_absorb1)
          qed
          then have "(X - A) \<inter> A \<noteq> {}"
            using B4 amem by (auto simp:mesh_def)
          then show False
            by blast
        qed
      qed
      then have "x \<in> \<Inter>{Adh``{lcro subset_order (Pow X) A}|A. A \<in> \<F>}"
        by blast
      then have "x \<in> Adh``{\<F>}"
        using prdetadhD1[OF A2 B1] by simp
      then show "p \<in> Adh"
        using B0 by simp
    qed
  qed
qed

lemma AdhCl_prdet:
  assumes A0:"isspmap Cl"
  shows "prdetadh (AdhCl Cl)"
proof(rule prdetadhI1)
  fix \<F> assume fmem:"\<F> \<in> pfilters"
  then have P0:"pow.pfilter \<F>"
    by simp
  have B0:"\<And>A. A \<in> \<F> \<Longrightarrow> lcro subset_order (Pow X) A \<in> pfilters"
    using set_lcro_pfilter set_pfilter_mem_base[OF P0] set_pfilter_ne[OF P0] by simp
  have B1:"\<And>A. A \<in> \<F> \<Longrightarrow> (AdhCl Cl)``{lcro subset_order (Pow X) A} = \<Inter>{Cl``{B}|B. B \<in> lcro subset_order (Pow X) A}"
    using Cl_to_Adh[OF A0] B0 by simp
  show "(AdhCl Cl)``{\<F>} = \<Inter>{(AdhCl Cl)``{lcro subset_order (Pow X) A}|A. A \<in> \<F>}" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix x assume "x \<in> ?L"
      then have B2:"\<And>B. B \<in> \<F> \<Longrightarrow> x \<in> Cl``{B}"
        using Cl_to_Adh[OF A0 fmem] by blast
      have "\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> (AdhCl Cl)``{lcro subset_order (Pow X) A}"
      proof-
        fix A assume amem:"A \<in> \<F>"
        have "\<And>B. B \<in> lcro subset_order (Pow X) A \<Longrightarrow> x \<in> Cl``{B}"
          using set_pfilter_up[OF P0 amem] B2 by (auto simp:lcro_iff)
        then show "x \<in> (AdhCl Cl)``{lcro subset_order (Pow X) A}"
          using B1[OF amem] by blast
      qed
      then show "x \<in> ?R"
        by blast
    qed
  next
    show "?R \<subseteq> ?L"
    proof
      fix x assume "x \<in> ?R"
      then have B2:"\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> (AdhCl Cl)``{lcro subset_order (Pow X) A}"
        by blast
      have "\<And>A. A \<in> \<F> \<Longrightarrow> x \<in> Cl``{A}"
      proof-
        fix A assume amem:"A \<in> \<F>"
        then have "A \<in> lcro subset_order (Pow X) A"
          using set_pfilter_mem_base[OF P0] by (simp add:lcro_iff)
        then show "x \<in> Cl``{A}"
          using B2[OF amem] B1[OF amem] by blast
      qed
      then show "x \<in> ?L"
        using Cl_to_Adh[OF A0 fmem] by blast
    qed
  qed
qed


section \<open>Lattices of Convergences\<close>

lemma isconvs_top:"isconvs (pfilters \<times> X)"
  by (simp add:isconvs_def)

lemma isconvs_bot:"isconvs {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}"
  using set_lcro_pfilter by (auto simp:isconvs_def)

lemma centered_top:"centered (pfilters \<times> X)"
  using set_lcro_pfilter by (auto simp:centered_def)

lemma centered_bot:"centered {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}"
  by (auto simp:centered_def)

lemma onpconv_top:"onpconv (pfilters \<times> X)"
proof(rule onpconvI1)
  fix x assume xmem:"x \<in> X"
  let ?S="{\<F>. (\<F>, x) \<in> pfilters \<times> X}"
  have "lcro subset_order (Pow X) {x} \<in> ?S"
    using set_lcro_pfilter xmem by simp
  then have "?S \<noteq> {}"
    by blast
  then have "pow.pfilter (\<Inter>?S)"
    by (intro set_pfilter_Inter) auto
  then show "(\<Inter>?S, x) \<in> pfilters \<times> X"
    using xmem by simp
qed

lemma centered_iff:"centered q \<longleftrightarrow> {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X} \<subseteq> q"
  by (auto simp:centered_def)

lemma isoconv_top:"isoconv (pfilters \<times> X)"
  by (rule isoconvI1) auto

lemma prtop_top:"is_prtop (pfilters \<times> X)"
  using isconvs_top centered_top isoconv_top onpconv_top by (simp add:is_prtop_def)

lemma isoconv_bot:"isoconv {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}"
proof(rule isoconvI1)
  fix \<G> \<F> x assume A0:"\<G> \<in> pfilters" and A1:"(\<F>, x) \<in> {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}" and A2:"\<F> \<subseteq> \<G>"
  then obtain B0:"\<F> = lcro subset_order (Pow X) {x}" and B1:"x \<in> X"
    by blast
  then have "ultrafilter \<F>"
    using principal_ultrafilter by simp
  then have "\<G> = \<F>"
    using ultrafilter_max A0 A2 by simp
  then show "(\<G>, x) \<in> {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}"
    using A1 by simp
qed

lemma convs_inter:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> isconvs q" and A1:"Q \<noteq> {}"
  shows "isconvs (\<Inter>Q)"
  using A0 A1 by (auto simp:isconvs_def)

lemma convs_un:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> isconvs q" and A1:"Q \<noteq> {}"
  shows "isconvs (\<Union>Q)"
  using A0 by (auto simp:isconvs_def)

lemma isoconvs_inter:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> isoconv q" and A1:"Q \<noteq> {}"
  shows "isoconv (\<Inter>Q)"
proof(rule isoconvI1)
  fix \<G> \<F> x assume "\<G> \<in> pfilters" and "(\<F>, x) \<in> \<Inter>Q" and "\<F> \<subseteq> \<G>"
  then show "(\<G>, x) \<in> \<Inter>Q"
    using isoconvD1[OF A0] by blast
qed

lemma isoconvs_un:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> isoconv q" and A1:"Q \<noteq> {}"
  shows "isoconv (\<Union>Q)"
proof(rule isoconvI1)
  fix \<G> \<F> x assume "\<G> \<in> pfilters" and "(\<F>, x) \<in> \<Union>Q" and "\<F> \<subseteq> \<G>"
  then show "(\<G>, x) \<in> \<Union>Q"
    using isoconvD1[OF A0] by blast
qed

lemma centered_inter:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> centered q" and A1:"Q \<noteq> {}"
  shows "centered (\<Inter>Q)"
  using A0 A1 by (auto simp:centered_def)

lemma centered_un:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> centered q" and A1:"Q \<noteq> {}"
  shows "centered (\<Union>Q)"
  using A0 A1 by (auto simp:centered_def)

lemma gconv_extrema:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> is_gconv q" and A1:"Q \<noteq> {}"
  shows gconv_clat1:"is_gconv (\<Union>Q)" and
        gconv_clat2:"is_gconv (\<Inter>Q)" and
        gconv_clat3:"is_sup subset_order gconvs Q (\<Union>Q)" and
        gconv_clat4:"is_inf subset_order gconvs Q (\<Inter>Q)"
proof-
  have B0:"\<And>q. q \<in> Q \<Longrightarrow> isconvs q" and B1:"\<And>q. q \<in> Q \<Longrightarrow> centered q" and B2:"\<And>q. q \<in> Q \<Longrightarrow> isoconv q"
    using A0 by (simp_all add:is_gconv_def)
  show P0:"is_gconv (\<Union>Q)"
    using convs_un[OF B0 A1] centered_un[OF B1 A1] isoconvs_un[OF B2 A1] by (simp add:is_gconv_def)
  show P1:"is_gconv (\<Inter>Q)"
    using convs_inter[OF B0 A1] centered_inter[OF B1 A1] isoconvs_inter[OF B2 A1] by (simp add:is_gconv_def)
  show "is_sup subset_order gconvs Q (\<Union>Q)"
    using P0 A0 by (auto simp:is_sup_iff)
  show "is_inf subset_order gconvs Q (\<Inter>Q)"
    using P1 A0 by (auto simp:is_sup_iff)
qed

lemma gconv_clat:
  shows gconv_clat5:"\<And>q. q \<in> gconvs \<Longrightarrow> q \<subseteq> pfilters \<times> X" and
        gconv_clat6:"\<And>q. q \<in> gconvs \<Longrightarrow> {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X} \<subseteq> q" and
        gconv_clat7:"is_least subset_order gconvs {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}" and
        gconv_clat8:"is_greatest subset_order gconvs (pfilters \<times> X)"
proof-
  show P0:"\<And>q. q \<in> gconvs \<Longrightarrow> q \<subseteq> pfilters \<times> X"
    by (simp add:is_gconv_def isconvs_def)
  show P1:"\<And>q. q \<in> gconvs \<Longrightarrow> {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X} \<subseteq> q"
    by (simp add:is_gconv_def centered_iff)
  have "is_gconv {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}"
    using isconvs_bot centered_bot isoconv_bot by (simp add:is_gconv_def)
  then show "is_least subset_order gconvs {(lcro subset_order (Pow X) {x}, x)|x. x \<in> X}"
    using P1 by (simp add:is_least_iff)
  have "is_gconv (pfilters \<times> X)"
    using isconvs_top centered_top isoconv_top by (simp add:is_gconv_def)
  then show "is_greatest subset_order gconvs (pfilters \<times> X)"
    using P0 by (simp add:is_greatest_iff)
qed

lemma prtop_inter:
  assumes A0:"\<And>q. q \<in> Q \<Longrightarrow> is_prtop q" and A1:"Q \<noteq> {}"
  shows prtop_sup1:"is_prtop (\<Inter>Q)"
  unfolding is_prtop_def
proof(intro conjI)
  show "isconvs (\<Inter>Q)"
    using A0 A1 convs_inter by (simp add:is_prtop_def)
  show "centered (\<Inter>Q)"
    using A0 A1 centered_inter by (simp add:is_prtop_def)
  show "isoconv (\<Inter>Q)"
    using A0 A1 isoconvs_inter by (simp add:is_prtop_def)
  show "onpconv (\<Inter>Q)"
  proof(rule onpconvI1)
    fix x assume xmem:"x \<in> X"
    let ?N="\<Inter>{\<F>. (\<F>, x) \<in> \<Inter>Q}"
    have B0:"(lcro subset_order (Pow X) {x}, x) \<in> \<Inter>Q"
      using A0 xmem by (auto simp:is_prtop_def centered_def)
    have B1:"\<And>\<F>. (\<F>, x) \<in> \<Inter>Q \<Longrightarrow> pow.pfilter \<F>"
      using A0 A1 by (auto simp:is_prtop_def isconvs_def)
    have B2:"pow.pfilter ?N"
      using B0 B1 by (intro set_pfilter_Inter) auto
    have "\<And>q. q \<in> Q \<Longrightarrow> (?N, x) \<in> q"
    proof-
      fix q assume qmem:"q \<in> Q"
      then have B3:"onpconv q" and B4:"isoconv q"
        using A0 by (simp_all add:is_prtop_def)
      have "(\<Inter>{\<F>. (\<F>, x) \<in> q}, x) \<in> q"
        by (rule onpconvD1[OF B3 xmem])
      moreover have "\<Inter>{\<F>. (\<F>, x) \<in> q} \<subseteq> ?N"
        using qmem by blast
      ultimately show "(?N, x) \<in> q"
        using isoconvD1[OF B4] B2 by simp
    qed
    then show "(?N, x) \<in> \<Inter>Q"
      by blast
  qed
qed

lemma gconv_moore:"moore_family (pfilters \<times> X) gconvs"
proof(unfold_locales)
  show "gconvs \<subseteq> Pow (pfilters \<times> X)"
    using gconv_clat5 by blast
  show "pfilters \<times> X \<in> gconvs"
    using prtop_top by (simp add:is_prtop_def is_gconv_def)
  show "\<And>E. \<lbrakk>E \<subseteq> gconvs; E \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>E \<in> gconvs"
    using gconv_clat2 by blast
qed

lemma prtop_moore:"moore_family (pfilters \<times> X) prtops"
proof(unfold_locales)
  show "prtops \<subseteq> Pow (pfilters \<times> X)"
    by (auto simp:is_prtop_def isconvs_def)
  show "pfilters \<times> X \<in> prtops"
    using prtop_top by simp
  show "\<And>E. \<lbrakk>E \<subseteq> prtops; E \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>E \<in> prtops"
    using prtop_inter by blast
qed

end

sublocale powerset \<subseteq> gconv:moore_family "pfilters \<times> X" gconvs
  by (rule gconv_moore)

sublocale powerset \<subseteq> prtop:moore_family "pfilters \<times> X" prtops
  by (rule prtop_moore)

context powerset
begin

lemma gconv_clat9:"complete_lattice_on subset_order gconvs"
  by (rule gconv.closed.complete_lattice_on_axioms)

lemma prtop_clat:"complete_lattice_on subset_order prtops"
  by (rule prtop.closed.complete_lattice_on_axioms)

lemma gconv_SupIn:"\<lbrakk>Q \<subseteq> gconvs; Q \<noteq> {}\<rbrakk> \<Longrightarrow> gconv.closed.SupIn Q = \<Union>Q"
  by (rule gconv.closed.SupIn_eqI) (rule gconv_clat3, auto)

lemma gconv_InfIn:"\<lbrakk>Q \<subseteq> gconvs; Q \<noteq> {}\<rbrakk> \<Longrightarrow> gconv.closed.InfIn Q = \<Inter>Q"
  by (rule gconv.InfIn_closed_eq)

lemma prtop_InfIn:"\<lbrakk>Q \<subseteq> prtops; Q \<noteq> {}\<rbrakk> \<Longrightarrow> prtop.closed.InfIn Q = \<Inter>Q"
  by (rule prtop.InfIn_closed_eq)


section \<open>Closed Elements of the Six Galois Connections\<close>

theorem ClN_closed_iff:
  assumes A0:"isspmap Cl"
  shows "ClN (NCl Cl) = Cl \<longleftrightarrow> iso_spmap Cl"
  using ClNh_if_iso4[OF A0] ClN_iso[of "NCl Cl"] by metis

theorem NCl_closed_iff:
  assumes A0:"ispsmap N"
  shows "NCl (ClN N) = N \<longleftrightarrow> iso_psmap N"
  using NhCl_if_iso2[OF A0] NCl_iso[of "ClN N"] by metis

theorem AdhN_closed_iff:
  assumes A0:"isconvs Adh"
  shows "AdhN (NAdh Adh) = Adh \<longleftrightarrow> prdetadh Adh"
proof
  assume "AdhN (NAdh Adh) = Adh"
  then show "prdetadh Adh"
    using Nh_to_Adh3[OF NAdh_psmap, of Adh] by (simp add:prdet_adh_def)
next
  assume "prdetadh Adh"
  then show "AdhN (NAdh Adh) = Adh"
    using AdhNh_if_prdet1[OF _ A0] A0 by (simp add:prdet_adh_def)
qed

theorem NAdh_closed_iff:
  assumes A0:"ispsmap N"
  shows "NAdh (AdhN N) = N \<longleftrightarrow> iso_psmap N \<and> (\<forall>x\<in>X. N``{x} \<noteq> {})"
proof
  assume "NAdh (AdhN N) = N"
  then show "iso_psmap N \<and> (\<forall>x\<in>X. N``{x} \<noteq> {})"
    using NAdh_iso[of "AdhN N"] NAdh_whole[of _ "AdhN N"] by auto
next
  assume "iso_psmap N \<and> (\<forall>x\<in>X. N``{x} \<noteq> {})"
  then show "NAdh (AdhN N) = N"
    using NhAdh_if_iso1[OF A0] by blast
qed

theorem LimN_closed_iff:
  assumes A0:"isconvs Lim" and A1:"centered Lim"
  shows "LimN (NLim Lim) = Lim \<longleftrightarrow> is_prtop Lim"
  using NhLim_imp_prtop[OF A0 _ A1] NhLim_if_prtop2 by blast

theorem NLim_closed_iff:
  assumes A0:"ispsmap N" and A1:"\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X; (x, A) \<in> N\<rbrakk> \<Longrightarrow> x \<in> A"
  shows "NLim (LimN N) = N \<longleftrightarrow> prtop_nh N"
  using LimNh_imp_prtop[OF A1 _ A0] LimNh_if_prtop2[OF _ A0] by blast

theorem LimCl_closed_iff:
  assumes A0:"isconvs Lim" and A1:"centered Lim"
  shows "LimCl (ClLim Lim) = Lim \<longleftrightarrow> is_prtop Lim"
  using ClLim_imp_prtop[OF A0 _ A1] LimCl_if_prtop9 by blast

theorem ClLim_closed_iff:
  assumes A0:"isspmap Cl" and A1:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
  shows "ClLim (LimCl Cl) = Cl \<longleftrightarrow> prtop_cl Cl"
  using LimCl_imp_prtop[OF A0 _ A1] ClLim_if_prt1[OF A0] by blast

theorem AdhCl_closed_iff:
  assumes A0:"isconvs Adh"
  shows "AdhCl (ClAdh Adh) = Adh \<longleftrightarrow> prdetadh Adh"
proof
  assume "AdhCl (ClAdh Adh) = Adh"
  then show "prdetadh Adh"
    using AdhCl_prdet[OF ClAdh_spmap, of Adh] by simp
next
  assume "prdetadh Adh"
  then show "AdhCl (ClAdh Adh) = Adh"
    using AdhCl_if_prdet1 A0 by (simp add:prdet_adh_def)
qed

theorem ClAdh_closed_iff:
  assumes A0:"isspmap Cl"
  shows "ClAdh (AdhCl Cl) = Cl \<longleftrightarrow> iso_spmap Cl \<and> Cl``{{}} = {}"
  using ClAdh_if_iso1[OF A0] ClAdh_iso[of "AdhCl Cl"] ClAdh_empty[of "AdhCl Cl"] by metis

theorem AdhLim_closed_iff:
  assumes A0:"isconvs Adh"
  shows "AdhLim (LimAdh Adh) = Adh \<longleftrightarrow> ufdetadh Adh"
proof
  assume "AdhLim (LimAdh Adh) = Adh"
  then show "ufdetadh Adh"
    using AdhLim_ufdet[OF LimAdh_convs LimAdh_isoconv, of Adh] by simp
next
  assume "ufdetadh Adh"
  then show "AdhLim (LimAdh Adh) = Adh"
    by (rule AdhLim_LimAdh[OF A0])
qed

theorem LimAdh_closed_iff:
  assumes A0:"isconvs Lim" and A1:"isoconv Lim"
  shows "LimAdh (AdhLim Lim) = Lim \<longleftrightarrow> ufdetconv Lim"
proof
  assume "LimAdh (AdhLim Lim) = Lim"
  then show "ufdetconv Lim"
    using LimAdh_ufdet[OF AdhLim_ufdet[OF A0 A1]] by simp
next
  assume "ufdetconv Lim"
  then show "LimAdh (AdhLim Lim) = Lim"
    by (rule LimAdh_AdhLim[OF A0 A1])
qed

lemma NCl_closed_mem:"Cl \<in> NCl.closure.closed \<longleftrightarrow> isspmap Cl \<and> ClN (NCl Cl) = Cl"
  and ClN_closed_mem:"N \<in> ClN.closure.closed \<longleftrightarrow> ispsmap N \<and> NCl (ClN N) = N"
  and NAdh_closed_mem:"Adh \<in> NAdh.closure.closed \<longleftrightarrow> isconvs Adh \<and> AdhN (NAdh Adh) = Adh"
  and AdhN_closed_mem:"N \<in> AdhN.closure.closed \<longleftrightarrow> ispsmap N \<and> NAdh (AdhN N) = N"
  and NLim_closed_mem:"Lim \<in> NLim.closure.closed \<longleftrightarrow> isconvs Lim \<and> LimN (NLim Lim) = Lim"
  and LimN_closed_mem:"N \<in> LimN.closure.closed \<longleftrightarrow> ispsmap N \<and> NLim (LimN N) = N"
  and ClAdh_closed_mem:"Adh \<in> ClAdh.closure.closed \<longleftrightarrow> isconvs Adh \<and> AdhCl (ClAdh Adh) = Adh"
  and AdhCl_closed_mem:"Cl \<in> AdhCl.closure.closed \<longleftrightarrow> isspmap Cl \<and> ClAdh (AdhCl Cl) = Cl"
  and ClLim_closed_mem:"Lim \<in> ClLim.closure.closed \<longleftrightarrow> isconvs Lim \<and> LimCl (ClLim Lim) = Lim"
  and LimCl_closed_mem:"Cl \<in> LimCl.closure.closed \<longleftrightarrow> isspmap Cl \<and> ClLim (LimCl Cl) = Cl"
  and AdhLim_closed_mem:"Lim \<in> AdhLim.closure.closed \<longleftrightarrow> isconvs Lim \<and> LimAdh (AdhLim Lim) = Lim"
  and LimAdh_closed_mem:"Adh \<in> LimAdh.closure.closed \<longleftrightarrow> isconvs Adh \<and> AdhLim (LimAdh Adh) = Adh"
  by (simp_all add:NCl.closure.closed_iff ClN.closure.closed_iff NAdh.closure.closed_iff AdhN.closure.closed_iff
                   NLim.closure.closed_iff LimN.closure.closed_iff ClAdh.closure.closed_iff AdhCl.closure.closed_iff
                   ClLim.closure.closed_iff LimCl.closure.closed_iff AdhLim.closure.closed_iff LimAdh.closure.closed_iff
                   isspmap_def ispsmap_def isconvs_def)

theorem NCl_closure_closed:"NCl.closure.closed = {Cl. isspmap Cl \<and> iso_spmap Cl}"
proof(intro set_eqI)
  fix Cl
  show "Cl \<in> NCl.closure.closed \<longleftrightarrow> Cl \<in> {Cl. isspmap Cl \<and> iso_spmap Cl}"
    using ClN_closed_iff[of Cl] by (auto simp:NCl_closed_mem)
qed

theorem ClN_closure_closed:"ClN.closure.closed = {N. ispsmap N \<and> iso_psmap N}"
proof(intro set_eqI)
  fix N
  show "N \<in> ClN.closure.closed \<longleftrightarrow> N \<in> {N. ispsmap N \<and> iso_psmap N}"
    using NCl_closed_iff[of N] by (auto simp:ClN_closed_mem)
qed

theorem NAdh_closure_closed:"NAdh.closure.closed = {Adh. prdet_adh Adh}"
proof(intro set_eqI)
  fix Adh
  show "Adh \<in> NAdh.closure.closed \<longleftrightarrow> Adh \<in> {Adh. prdet_adh Adh}"
    using AdhN_closed_iff[of Adh] by (auto simp:NAdh_closed_mem prdet_adh_def)
qed

theorem AdhN_closure_closed:"AdhN.closure.closed = {N. ispsmap N \<and> iso_psmap N \<and> (\<forall>x\<in>X. N``{x} \<noteq> {})}"
proof(intro set_eqI)
  fix N
  show "N \<in> AdhN.closure.closed \<longleftrightarrow> N \<in> {N. ispsmap N \<and> iso_psmap N \<and> (\<forall>x\<in>X. N``{x} \<noteq> {})}"
    using NAdh_closed_iff[of N] by (auto simp:AdhN_closed_mem)
qed

theorem NLim_closure_closed:"{Lim \<in> NLim.closure.closed. centered Lim} = prtops"
proof(intro set_eqI)
  fix Lim
  show "Lim \<in> {Lim \<in> NLim.closure.closed. centered Lim} \<longleftrightarrow> Lim \<in> prtops"
    using LimN_closed_iff[of Lim] by (auto simp:NLim_closed_mem is_prtop_def)
qed

theorem LimN_closure_closed:
  "{N \<in> LimN.closure.closed. \<forall>x A. (x, A) \<in> N \<longrightarrow> x \<in> A} = {N. ispsmap N \<and> prtop_nh N}"
proof(intro set_eqI)
  fix N
  show "N \<in> {N \<in> LimN.closure.closed. \<forall>x A. (x, A) \<in> N \<longrightarrow> x \<in> A} \<longleftrightarrow> N \<in> {N. ispsmap N \<and> prtop_nh N}" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then have B0:"ispsmap N" and B1:"NLim (LimN N) = N" and B2:"\<And>x A. (x, A) \<in> N \<Longrightarrow> x \<in> A"
      by (auto simp:LimN_closed_mem)
    then show ?R
      using NLim_closed_iff[OF B0 B2] by simp
  next
    assume ?R
    then have B0:"ispsmap N" and B1:"prtop_nh N"
      by simp_all
    then have B2:"\<And>x A. (x, A) \<in> N \<Longrightarrow> x \<in> A"
      by (auto simp:prtop_nh_def ispsmap_def)
    then show ?L
      using NLim_closed_iff[OF B0 B2] B0 B1 by (auto simp:LimN_closed_mem)
  qed
qed

theorem ClLim_closure_closed:"{Lim \<in> ClLim.closure.closed. centered Lim} = prtops"
proof(intro set_eqI)
  fix Lim
  show "Lim \<in> {Lim \<in> ClLim.closure.closed. centered Lim} \<longleftrightarrow> Lim \<in> prtops"
    using LimCl_closed_iff[of Lim] by (auto simp:ClLim_closed_mem is_prtop_def)
qed

theorem LimCl_closure_closed:
  "{Cl \<in> LimCl.closure.closed. \<forall>A\<in>Pow X. A \<subseteq> Cl``{A}} = {Cl. isspmap Cl \<and> prtop_cl Cl}"
proof(intro set_eqI)
  fix Cl
  show "Cl \<in> {Cl \<in> LimCl.closure.closed. \<forall>A\<in>Pow X. A \<subseteq> Cl``{A}} \<longleftrightarrow> Cl \<in> {Cl. isspmap Cl \<and> prtop_cl Cl}" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then have B0:"isspmap Cl" and B1:"ClLim (LimCl Cl) = Cl" and B2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
      by (auto simp:LimCl_closed_mem)
    then show ?R
      using ClLim_closed_iff[OF B0 B2] by simp
  next
    assume ?R
    then have B0:"isspmap Cl" and B1:"prtop_cl Cl"
      by simp_all
    then have B2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}"
      by (simp add:prtop_cl_def)
    then show ?L
      using ClLim_closed_iff[OF B0 B2] B0 B1 by (auto simp:LimCl_closed_mem)
  qed
qed

theorem ClAdh_closure_closed:"ClAdh.closure.closed = {Adh. prdet_adh Adh}"
proof(intro set_eqI)
  fix Adh
  show "Adh \<in> ClAdh.closure.closed \<longleftrightarrow> Adh \<in> {Adh. prdet_adh Adh}"
    using AdhCl_closed_iff[of Adh] by (auto simp:ClAdh_closed_mem prdet_adh_def)
qed

theorem AdhCl_closure_closed:"AdhCl.closure.closed = {Cl. isspmap Cl \<and> iso_spmap Cl \<and> Cl``{{}} = {}}"
proof(intro set_eqI)
  fix Cl
  show "Cl \<in> AdhCl.closure.closed \<longleftrightarrow> Cl \<in> {Cl. isspmap Cl \<and> iso_spmap Cl \<and> Cl``{{}} = {}}"
    using ClAdh_closed_iff[of Cl] by (auto simp:AdhCl_closed_mem)
qed

theorem AdhLim_closure_closed:"AdhLim.closure.closed = {Lim. isconvs Lim \<and> isoconv Lim \<and> ufdetconv Lim}"
proof(intro set_eqI)
  fix Lim
  have "isconvs Lim \<Longrightarrow> LimAdh (AdhLim Lim) = Lim \<longleftrightarrow> isoconv Lim \<and> ufdetconv Lim"
    using LimAdh_closed_iff[of Lim] LimAdh_isoconv[of "AdhLim Lim"] by metis
  then show "Lim \<in> AdhLim.closure.closed \<longleftrightarrow> Lim \<in> {Lim. isconvs Lim \<and> isoconv Lim \<and> ufdetconv Lim}"
    by (auto simp:AdhLim_closed_mem)
qed

theorem LimAdh_closure_closed:"LimAdh.closure.closed = {Adh. isconvs Adh \<and> ufdetadh Adh}"
proof(intro set_eqI)
  fix Adh
  show "Adh \<in> LimAdh.closure.closed \<longleftrightarrow> Adh \<in> {Adh. isconvs Adh \<and> ufdetadh Adh}"
    using AdhLim_closed_iff[of Adh] by (auto simp:LimAdh_closed_mem)
qed

end


section \<open>Continuity\<close>

locale powerset_map = dom:powerset X + cod:powerset Y
  for X::"'a set" and Y::"'b set" +
  fixes f::"'a \<Rightarrow> 'b"
  assumes f_maps:"f ` X \<subseteq> Y"
begin

definition Imfil::"'a set set \<Rightarrow> 'b set set"
  where "Imfil \<F> = {E \<in> Pow Y. \<exists>F\<in>\<F>. f`F \<subseteq> E}"

definition cont_at::"('a set set \<times> 'a) set \<Rightarrow> ('b set set \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> bool"
  where "cont_at q p x \<longleftrightarrow> (\<forall>\<F>. (\<F>, x) \<in> q \<longrightarrow> (Imfil \<F>, f x) \<in> p)"

lemma Imfil_memD:"E \<in> Imfil \<F> \<Longrightarrow> E \<in> Pow Y \<and> (\<exists>F\<in>\<F>. f`F \<subseteq> E)"
  and Imfil_memI:"\<lbrakk>E \<in> Pow Y; \<exists>F\<in>\<F>. f`F \<subseteq> E\<rbrakk> \<Longrightarrow> E \<in> Imfil \<F>"
  by (simp_all add:Imfil_def)

lemma Imfil_iso:"\<F> \<subseteq> \<G> \<Longrightarrow> Imfil \<F> \<subseteq> Imfil \<G>"
  by (auto simp:Imfil_def)

lemma im_filter:
  assumes pfl:"dom.pow.pfilter \<F>"
  shows "cod.pow.pfilter (Imfil \<F>)"
proof-
  have B0:"filter_on subset_order (Pow X) \<F>" and B1:"{} \<notin> \<F>"
    using pfl by (simp_all add:dom.set_pfilter_iff)
  have "filter_on subset_order (Pow Y) (Imfil \<F>)"
  proof(rule cod.set_filterI)
    show "Imfil \<F> \<subseteq> Pow Y"
      by (auto simp:Imfil_def)
    have "X \<in> \<F>"
      by (rule dom.set_filter_whole[OF B0])
    then have "Y \<in> Imfil \<F>"
      using f_maps by (auto simp:Imfil_def)
    then show "Imfil \<F> \<noteq> {}"
      by blast
    show "\<And>A B. \<lbrakk>A \<in> Imfil \<F>; B \<in> Imfil \<F>\<rbrakk> \<Longrightarrow> A \<inter> B \<in> Imfil \<F>"
    proof-
      fix A B assume "A \<in> Imfil \<F>" and "B \<in> Imfil \<F>"
      then obtain FA FB where B2:"FA \<in> \<F>" and B3:"f`FA \<subseteq> A" and B4:"FB \<in> \<F>" and B5:"f`FB \<subseteq> B" and B6:"A \<subseteq> Y"
        by (auto simp:Imfil_def)
      have "FA \<inter> FB \<in> \<F>"
        by (rule dom.set_filter_Int[OF B0 B2 B4])
      moreover have "f`(FA \<inter> FB) \<subseteq> A \<inter> B"
        using B3 B5 by blast
      ultimately show "A \<inter> B \<in> Imfil \<F>"
        using B6 by (auto simp:Imfil_def)
    qed
    show "\<And>A B. \<lbrakk>A \<in> Imfil \<F>; B \<subseteq> Y; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> Imfil \<F>"
    proof-
      fix A B assume "A \<in> Imfil \<F>" and "B \<subseteq> Y" and "A \<subseteq> B"
      then obtain F where "F \<in> \<F>" and "f`F \<subseteq> A"
        by (auto simp:Imfil_def)
      then have "f`F \<subseteq> B"
        using \<open>A \<subseteq> B\<close> by blast
      then show "B \<in> Imfil \<F>"
        using \<open>B \<subseteq> Y\<close> \<open>F \<in> \<F>\<close> by (auto simp:Imfil_def)
    qed
  qed
  moreover have "{} \<notin> Imfil \<F>"
  proof
    assume "{} \<in> Imfil \<F>"
    then obtain F where "F \<in> \<F>" and "f`F \<subseteq> {}"
      by (auto simp:Imfil_def)
    then have "F = {}"
      by blast
    then show False
      using B1 \<open>F \<in> \<F>\<close> by simp
  qed
  ultimately show ?thesis
    by (simp add:cod.set_pfilter_iff)
qed

lemma cont_at2:"cont_at q p x \<longleftrightarrow> (\<forall>\<F>. (\<F>, x) \<in> q \<longrightarrow> (Imfil \<F>, f x) \<in> p)"
  by (simp add:cont_at_def)

lemma cont_atD1:"\<lbrakk>cont_at q p x; \<F> \<in> dom.pfilters; (\<F>, x) \<in> q\<rbrakk> \<Longrightarrow> (Imfil \<F>, f x) \<in> p"
  and cont_atD2:"\<lbrakk>cont_at q p x; (\<F>, x) \<in> q\<rbrakk> \<Longrightarrow> (Imfil \<F>, f x) \<in> p"
  and cont_atI2:"(\<And>\<F>. (\<F>, x) \<in> q \<Longrightarrow> (Imfil \<F>, f x) \<in> p) \<Longrightarrow> cont_at q p x"
  by (simp_all add:cont_at_def)

lemma cont_atI1:
  "\<lbrakk>dom.isconvs q; \<And>\<F>. \<lbrakk>\<F> \<in> dom.pfilters; (\<F>, x) \<in> q\<rbrakk> \<Longrightarrow> (Imfil \<F>, f x) \<in> p\<rbrakk> \<Longrightarrow> cont_at q p x"
  unfolding cont_at_def using dom.isgconvD1 by blast

lemma continuousD1:"\<lbrakk>cont_at q p x; (\<F>, x) \<in> q\<rbrakk> \<Longrightarrow> ({E \<in> Pow Y. \<exists>F\<in>\<F>. f`F \<subseteq> E}, f x) \<in> p"
  by (simp add:cont_at_def Imfil_def)

lemma cont12:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and xmem0:"x \<in> X" and cont1:"cont_at q p x"
  shows "(cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
proof-
  have B0:"((dom.NLim q)``{x}, x) \<in> q"
    using dom.onpconvD2[OF _ _ _ xmem0] prtpx by (simp add:dom.is_prtop_def)
  then have B1:"(Imfil ((dom.NLim q)``{x}), f x) \<in> p"
    using cont1 by (simp add:cont_at_def)
  have "(dom.NLim q)``{x} \<in> dom.pfilters"
    using B0 prtpx by (auto simp:dom.is_prtop_def dom.isconvs_def)
  then have B2:"Imfil ((dom.NLim q)``{x}) \<in> cod.pfilters"
    using im_filter by simp
  show ?thesis
    using B1 B2 by (auto simp:cod.NLim_def)
qed

lemma cont12_global:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and cont1:"\<And>x. x \<in> X \<Longrightarrow> cont_at q p x"
  shows "\<And>x. x \<in> X \<Longrightarrow> (cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
  by (intro cont12[OF prtpx prtpy] cont1)

lemma cont21:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and
          cont2:"(cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
  shows "cont_at q p x"
proof(rule cont_atI2)
  fix \<F> assume A0:"(\<F>, x) \<in> q"
  then have B0:"x \<in> X" and B1:"\<F> \<in> dom.pfilters"
    using prtpx by (auto simp:dom.is_prtop_def dom.isconvs_def)
  have B2:"f x \<in> Y"
    using f_maps B0 by blast
  have B3:"(dom.NLim q)``{x} \<subseteq> \<F>"
    using A0 B1 by (auto simp:dom.NLim_def)
  have B4:"(cod.NLim p)``{f x} \<subseteq> Imfil \<F>"
    using cont2 Imfil_iso[OF B3] by blast
  have B5:"Imfil \<F> \<in> cod.pfilters"
    using im_filter B1 by simp
  have B6:"((cod.NLim p)``{f x}, f x) \<in> p"
    using cod.onpconvD2[OF _ _ _ B2] prtpy by (simp add:cod.is_prtop_def)
  show "(Imfil \<F>, f x) \<in> p"
    using cod.isoconvD1[OF _ B5 B6 B4] prtpy by (simp add:cod.is_prtop_def)
qed

lemma cont21_global:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and
          cont2:"\<And>x. x \<in> X \<Longrightarrow> (cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
  shows "\<And>x. x \<in> X \<Longrightarrow> cont_at q p x"
  by (intro cont21[OF prtpx prtpy] cont2)

theorem cont_at_iff:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and xmem:"x \<in> X"
  shows "cont_at q p x \<longleftrightarrow> (cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
  using cont12[OF prtpx prtpy xmem] cont21[OF prtpx prtpy] by blast

lemma cont23:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and
          cont2:"\<And>x. x \<in> X \<Longrightarrow> (cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})" and
          amem:"A \<in> Pow X"
  shows "f`((dom.ClLim q)``{A}) \<subseteq> (cod.ClLim p)``{f`A}"
proof
  fix y assume "y \<in> f`((dom.ClLim q)``{A})"
  then obtain x where B0:"x \<in> (dom.ClLim q)``{A}" and B1:"y = f x"
    by blast
  have B2:"x \<in> X"
    using B0 by (simp add:dom.ClLim_def)
  have B3:"f x \<in> Y"
    using f_maps B2 by blast
  have B4:"f`A \<in> Pow Y"
    using f_maps amem by blast
  have B5:"dom.mesh {A} ((dom.NLim q)``{x})"
    using dom.ClLim_mem_iff[OF prtpx B2 amem] B0 by simp
  have "\<And>V. V \<in> (cod.NLim p)``{f x} \<Longrightarrow> f`A \<inter> V \<noteq> {}"
  proof-
    fix V assume "V \<in> (cod.NLim p)``{f x}"
    then obtain F where B6:"F \<in> (dom.NLim q)``{x}" and B7:"f`F \<subseteq> V"
      using cont2[OF B2] by (auto simp:Imfil_def)
    then have "A \<inter> F \<noteq> {}"
      using B5 by (simp add:dom.mesh_single_iff)
    then obtain a where "a \<in> A" and "a \<in> F"
      by blast
    then have "f a \<in> f`A \<inter> V"
      using B7 by blast
    then show "f`A \<inter> V \<noteq> {}"
      by blast
  qed
  then have "cod.mesh {f`A} ((cod.NLim p)``{f x})"
    by (simp add:cod.mesh_single_iff)
  then show "y \<in> (cod.ClLim p)``{f`A}"
    using cod.ClLim_mem_iff[OF prtpy B3 B4] B1 by simp
qed

lemma cont34:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and fmap2:"f -` Y \<subseteq> X" and
          cont3:"\<And>A. A \<in> Pow X \<Longrightarrow> f`((dom.ClLim q)``{A}) \<subseteq> (cod.ClLim p)``{f`A}"
  shows "\<And>x V. \<lbrakk>x \<in> X; V \<in> (cod.NLim p)``{f x}\<rbrakk> \<Longrightarrow> f -` V \<in> (dom.NLim q)``{x}"
proof-
  fix x V assume xmem:"x \<in> X" and vmem:"V \<in> (cod.NLim p)``{f x}"
  have A0:"dom.isconvs q" and A1:"cod.isconvs p"
    using prtpx prtpy by (simp_all add:dom.is_prtop_def cod.is_prtop_def)
  have B0:"V \<in> Pow Y"
    using vmem by (simp add:cod.NLim_def)
  have B1:"f x \<in> Y"
    using f_maps xmem by blast
  have B2:"f -` V \<in> Pow X"
    using B0 fmap2 by blast
  show "f -` V \<in> (dom.NLim q)``{x}"
  proof(rule ccontr)
    assume "f -` V \<notin> (dom.NLim q)``{x}"
    then have "x \<in> (dom.ClLim q)``{X - f -` V}"
      using dom.Lim_to_Nh5[OF A0 B2 xmem] by simp
    then have "f x \<in> (cod.ClLim p)``{f`(X - f -` V)}"
      using cont3[of "X - f -` V"] by blast
    moreover have "f`(X - f -` V) \<subseteq> Y - V"
      using f_maps by blast
    ultimately have "f x \<in> (cod.ClLim p)``{Y - V}"
      using cod.iso_spmapD1[OF cod.ClLim_iso, of "Y - V" "f`(X - f -` V)"] by blast
    then have "V \<notin> (cod.NLim p)``{f x}"
      using cod.Lim_to_Nh5[OF A1 B0 B1] by simp
    then show False
      using vmem by simp
  qed
qed

lemma cont45:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and fmap2:"f -` Y \<subseteq> X" and
          cont4:"\<And>x V. \<lbrakk>x \<in> X; V \<in> (cod.NLim p)``{f x}\<rbrakk> \<Longrightarrow> f -` V \<in> (dom.NLim q)``{x}"
  shows "\<And>x V. \<lbrakk>x \<in> X; V \<in> (cod.NLim p)``{f x}\<rbrakk> \<Longrightarrow> \<exists>U\<in>(dom.NLim q)``{x}. f`U \<subseteq> V"
proof-
  fix x V assume "x \<in> X" and "V \<in> (cod.NLim p)``{f x}"
  then have "f -` V \<in> (dom.NLim q)``{x}"
    by (rule cont4)
  moreover have "f`(f -` V) \<subseteq> V"
    by blast
  ultimately show "\<exists>U\<in>(dom.NLim q)``{x}. f`U \<subseteq> V"
    by blast
qed

lemma cont52:
  assumes prtpx:"dom.is_prtop q" and prtpy:"cod.is_prtop p" and
          cont5:"\<And>x V. \<lbrakk>x \<in> X; V \<in> (cod.NLim p)``{f x}\<rbrakk> \<Longrightarrow> \<exists>U\<in>(dom.NLim q)``{x}. f`U \<subseteq> V"
  shows "\<And>x. x \<in> X \<Longrightarrow> (cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
proof-
  fix x assume xmem:"x \<in> X"
  show "(cod.NLim p)``{f x} \<subseteq> Imfil ((dom.NLim q)``{x})"
  proof
    fix V assume vmem:"V \<in> (cod.NLim p)``{f x}"
    then have "V \<in> Pow Y"
      by (simp add:cod.NLim_def)
    then show "V \<in> Imfil ((dom.NLim q)``{x})"
      using cont5[OF xmem vmem] by (auto simp:Imfil_def)
  qed
qed

end

end
