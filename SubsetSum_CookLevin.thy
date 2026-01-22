theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section \<open>Cook--Levin bridge for the subset-sum lower bound\<close>

text \<open>
This theory connects the abstract decision-tree lower bound developed in
\<open>SubsetSum_DecisionTree\<close> with the concrete operational semantics of
Turing machines, as defined in the AFP \emph{Cook\_Levin} library.

The objective of this file is structural.  Within the Cook--Levin framework,
we introduce an explicit information-flow interface, formalised below as
\emph{LR-read}, that exposes the same per-candidate informational structure
required by the abstract \(\sqrt{2^n}\) lower bound.

The development proceeds in several layers:

\begin{itemize}
\item We define a time measure \verb|steps_CL| together with acceptance
      predicates \verb|accepts_CL| and \verb|accepts_CL_halt| for Cook--Levin
      machines operating on Boolean inputs.  Inputs are written onto tape~0
      using the encoding function \verb|bool_to_symbols|.

\item Using these notions, we formalise SUBSET--SUM as a language in the
      Cook--Levin sense and give a verifier-based proof that SUBSET--SUM lies
      in \(\mathcal{NP}\) relative to any instance encoding \verb|enc0|
      that admits a verifier in the sense of the locale \verb|SS_Verifier_NP|.

\item We introduce a locale \verb|CL_SubsetSum_Solver| for a Turing machine
      \verb|M| and encoding \verb|enc| that together decide SUBSET--SUM
      correctly.  Inside this locale we obtain the specialised notions
      \[
        \verb|steps_TM as s| = \verb|steps_CL M (enc as s)|,
        \qquad
        \verb|read0_TM as s| = \verb|read0_CL M (enc as s)|,
      \]
      which specialise the Cook--Levin-level notions to SUBSET--SUM instances
      and serve as the concrete time and read measures for the later transfer
      of the lower bound.

\item Finally, the locale \verb|LR_Read_TM| states the assumptions needed to
      align the observable behaviour of \verb|M| with the canonical candidate
      sets used in the abstract lower bound.  Once these assumptions are made,
      the abstract \(\sqrt{2^n}\) bound transfers directly to
      \verb|steps_TM| and hence to \verb|steps_CL M|.
\end{itemize}

This theory does not, by itself, separate complexity classes.  It provides
only the Cook--Levin-side definitions and the LR-read interface required to
import the abstract decision-tree lower bound.  The conditional separation
\(\mathcal{P} \neq \mathcal{NP}\) is established later, in
\<open>SubsetSum_PneqNP\<close>.
\<close>

text \<open>
As a preparatory step, we state an elementary analytic fact in the precise
numerical form needed later: polynomials bounded above by a ceiling function
are eventually strictly dominated by the function
\(n \mapsto 2 \cdot \sqrt{2^n}\).
\<close>

lemma exp_beats_poly_ceiling_strict_TM:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "\<exists>N::nat. \<forall>n\<ge>N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d \<le> (\<surd>2)^n *)
  have ev: "eventually (\<lambda>n. c * (real n) ^ d \<le> (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 where N1: "\<forall>n\<ge>N1. c * (real n) ^ d \<le> (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)

  define N where "N = max N1 1"

  (* Simple ceiling bound: \<lceil>y\<rceil> \<le> y + 1 *)
  have ceil_le: "of_int (ceiling y) \<le> y + 1" for y :: real
    by linarith

  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n \<ge> N"
    then have nN1: "n \<ge> N1" and n_ge1: "n \<ge> 1"
      by (auto simp: N_def)

    from N1[rule_format, OF nN1]
    have bound: "c * (real n) ^ d \<le> (sqrt 2) ^ n"
      by simp

    have up:
      "of_int (ceiling (c * (real n) ^ d))
         \<le> (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith

    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by simp

    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with up step
    show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
      by linarith
  qed
qed

lemma length_pow2_list[simp]: "length (pow2_list n) = n"
  by (simp add: pow2_list_def)

text \<open>
For each length \verb|n| we fix a canonical example with distinct subset sums,
namely \verb|pow2_list n|.  This family is convenient because for
\verb|as = pow2_list n| all \(2^n\) subset sums are different, and thus it
witnesses the existence of lists of length \verb|n| with pairwise distinct
subset sums.

The lower-bound argument itself does not depend on any special hardness
property of powers of~\(2\).  It uses only the abstract assumption that for
each \verb|n| there exist lists \verb|as| of length \verb|n| satisfying
\verb|distinct_subset_sums as|.  This assumption is captured formally by the
lemma \verb|exists_distinct_family_TM|.
\<close>

lemma exists_distinct_family_TM:
  "\<forall>n. \<exists>as. length as = n \<and> distinct_subset_sums as"
proof
  fix n :: nat
  have len: "length (pow2_list n) = n"
    by (rule length_pow2_list)
  moreover have dist: "distinct_subset_sums (pow2_list n)"
    by (rule distinct_subset_sums_pow2_list)
  ultimately show "\<exists>as. length as = n \<and> distinct_subset_sums as"
    by blast
qed

subsection \<open>Basic encoding to Cook--Levin symbols\<close>

text \<open>
We use the standard Cook--Levin tape alphabet with the following conventions:

\begin{itemize}
\item symbol \verb|0| represents the blank symbol;
\item symbol \verb|1| represents the start symbol;
\item symbol \verb|2| represents the Boolean value \verb|0|;
\item symbol \verb|3| represents the Boolean value \verb|1|.
\end{itemize}

An input Boolean string is written on tape~0 as a sequence of symbols
\verb|2| and \verb|3|, using the encoding defined by
\verb|bool_to_symbols|.
\<close>

definition bool_to_symbols :: "bool list \<Rightarrow> symbol list" where
  "bool_to_symbols bs = map (\<lambda>b. if b then 3 else 2) bs"

text \<open>We fix two tapes: input (0) and output (1).\<close>

definition k_tapes :: nat where
  "k_tapes = 2"


subsection \<open>Cook--Levin step count and acceptance\<close>

text \<open>
We define a simple halting-time function \verb|steps_CL| together with the
acceptance predicates \verb|accepts_CL| and \verb|accepts_CL_halt| for
Cook--Levin machines.

\begin{itemize}
\item \verb|steps_CL M x| is defined as the least time step \verb|t| such that
      the control-state index of the machine configuration is at least
      \verb|length M|.  This matches the halting convention used in the
      theory \<open>Cook_Levin.NP\<close>.

\item \verb|conf_CL M x t| denotes the configuration of machine \verb|M|
      after \verb|t| execution steps on input \verb|x|.

\item \verb|accepts_CL M x| holds if, at time \verb|steps_CL M x|, the symbol
      under the head on tape~1 is \verb|3|.  In other words, the output tape
      contains the symbol representing Boolean~\verb|1| under its head at
      halting time.
\end{itemize}

These are purely Cook--Levin--level notions.  They refer to an arbitrary
machine \verb|M| run on an arbitrary Boolean string
\verb|x :: bool list|, and make no reference to SUBSET--SUM or to any specific
instance encoding.

The definitions are intended for machines that halt on the relevant inputs.
In this development, halting is supplied implicitly by the solver and
time-bound assumptions introduced later, for example via an explicit halting
assumption or via a polynomial time-bound hypothesis.
\<close>

definition steps_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat" where
  "steps_CL M x =
     (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t)
                 \<ge> length M)"

definition conf_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> config" where
  "conf_CL M x t = execute M (start_config k_tapes (bool_to_symbols x)) t"

definition halts_CL :: "machine \<Rightarrow> bool list \<Rightarrow> bool" where
  "halts_CL M x \<longleftrightarrow> (\<exists>t. fst (conf_CL M x t) \<ge> length M)"

lemma halts_CL_iff [simp]:
  "halts_CL M x \<longleftrightarrow> (\<exists>t. fst (conf_CL M x t) \<ge> length M)"
  by (simp add: halts_CL_def)

lemma steps_CL_halting:
  assumes halt: "halts_CL M x"
  shows "fst (conf_CL M x (steps_CL M x)) \<ge> length M"
  using halt
  unfolding halts_CL_def steps_CL_def conf_CL_def
  by (rule LeastI_ex)

lemma steps_CL_minimal:
  assumes ht: "fst (conf_CL M x t) \<ge> length M"
  shows "steps_CL M x \<le> t"
  using ht
  unfolding steps_CL_def conf_CL_def
  by (rule Least_le)

definition head0_CL :: "config \<Rightarrow> int" where
  "head0_CL cfg = (cfg <#> 0)"

definition accept_symbol :: nat where
  "accept_symbol = 3"

text \<open>
We interpret the symbol under the head on tape~1 at halting time as the
machine's one-bit Boolean output.  The symbol \verb|3| denotes Boolean
\verb|True| (accept), while the symbol \verb|2| denotes Boolean \verb|False|.
\<close>

lemma accept_symbol_is_bit1 [simp]:
  "accept_symbol = (if True then 3 else 2)"
  by (simp add: accept_symbol_def)

definition output_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat list" where
  "output_CL M x =
     (let t   = steps_CL M x;
          cfg = conf_CL M x t
      in [ (cfg <:> 1) (cfg <#> 1) ])"

definition accepts_CL :: "machine \<Rightarrow> bool list \<Rightarrow> bool" where
  "accepts_CL M x \<longleftrightarrow> output_CL M x = [accept_symbol]"

lemma conf_CL_at_steps [simp]:
  "conf_CL M x (steps_CL M x) =
     execute M (start_config k_tapes (bool_to_symbols x)) (steps_CL M x)"
  by (simp add: conf_CL_def)

lemma singleton_list_eq_eq [simp]:
  "([a] = [b]) = (a = b)"
  by simp

lemma accepts_CL_iff_symbol_at_output_head:
  "accepts_CL M x =
     (let t = steps_CL M x; cfg = conf_CL M x t
      in |.| (cfg <!> 1) = accept_symbol)"
  unfolding accepts_CL_def output_CL_def
  by (metis list.inject)

lemma accepts_CL_iff_symbol_at_output_head_iff [simp]:
  "accepts_CL M x \<longleftrightarrow>
     (let t = steps_CL M x; cfg = conf_CL M x t
      in |.| (cfg <!> 1) = accept_symbol)"
  using accepts_CL_iff_symbol_at_output_head by simp

definition accepts_CL_halt :: "machine \<Rightarrow> bool list \<Rightarrow> bool" where
  "accepts_CL_halt M x \<longleftrightarrow> halts_CL M x \<and> accepts_CL M x"

lemma accepts_CL_haltD1:
  "accepts_CL_halt M x \<Longrightarrow> halts_CL M x"
  by (simp add: accepts_CL_halt_def)

lemma accepts_CL_haltD2:
  "accepts_CL_halt M x \<Longrightarrow> accepts_CL M x"
  by (simp add: accepts_CL_halt_def)

text \<open>
The predicate \verb|accepts_CL_halt| is the notion of \emph{correct acceptance}
used when stating solver correctness.  It ensures that acceptance is asserted
only for computations that actually halt, avoiding any ambiguity arising from
partial or nonterminating executions.

In particular, all solver-correctness assumptions below are phrased in terms of
\verb|accepts_CL_halt| rather than \verb|accepts_CL| alone.
\<close>

text \<open>
We reason about Cook--Levin machines mainly via the abstract notions
\verb|steps_CL| and \verb|accepts_CL|, without unfolding low-level
configuration details.  Later, in the locale \verb|CL_SubsetSum_Solver|,
these Cook--Levin--level notions are specialised to SUBSET--SUM instances
\verb|(as, s)| via an encoding \verb|enc as s|, yielding the derived
quantities \verb|steps_TM| and \verb|read0_TM|.
\<close>

subsection \<open>Which input bits does a Cook--Levin machine read?\<close>

text \<open>
The set \verb|read0_CL M x| collects all indices on the input tape (tape~0)
that the head visits before halting on input~\verb|x|.  This abstracts away
from the timing or frequency of visits and records only which input positions
the machine has actually inspected.

These Cook--Levin--level read-sets are raw observations of machine behaviour
on Boolean strings.  The LR-read interface introduced later in
\verb|LR_Read_TM| packages this low-level reading behaviour into
\emph{canonical} ``seen'' sets on the SUBSET--SUM side, aligned with the
LHS/RHS candidate families at a suitable split position.
\<close>

definition read0_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat set" where
  "read0_CL M x =
     { nat h | t h.
        let cfg = conf_CL M x t in
        h = head0_CL cfg \<and>
        t < steps_CL M x \<and> 0 \<le> h \<and> nat h < length x }"
text \<open>
  Here the index set is expressed in terms of the Boolean input length.
  Since \<open>bool_to_symbols\<close> is length-preserving, this agrees with the
  corresponding tape-0 symbol positions.
\<close>
lemma length_bool_to_symbols[simp]:
  "length (bool_to_symbols bs) = length bs"
  by (simp add: bool_to_symbols_def)

lemma read0_CL_subset_indices:
  "read0_CL M x \<subseteq> {..<length x}"
  unfolding read0_CL_def by auto

subsection \<open>The mathematical SUBSET--SUM predicate\<close>

text \<open>
We now introduce the \emph{mathematical} SUBSET--SUM predicate, independent
of any machine model or input encoding.  It asks whether there exists a
$0/1$--vector \verb|xs| selecting a subset of \verb|as| whose weighted sum
is equal to the target value \verb|s|.

This predicate represents the underlying decision problem that our
Cook--Levin machines are intended to solve.
\<close>

definition subset_sum_true :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "subset_sum_true as s \<longleftrightarrow>
     (\<exists>xs \<in> bitvec (length as).
        (\<Sum> i<length as. as ! i * xs ! i) = s)"


subsection \<open>Certificate-based view of SUBSET--SUM\<close>

text \<open>
A natural certificate for SUBSET--SUM is a $0/1$--vector \verb|xs| of length
\verb|length as| indicating which elements of the list \verb|as| are chosen.
The predicate \verb|ss_cert_ok as s xs| expresses the following conditions:

\begin{itemize}
\item \verb|xs| has the correct length;
\item all entries of \verb|xs| are either \verb|0| or \verb|1|;
\item the weighted sum of the selected entries is equal to the target value
      \verb|s|.
\end{itemize}

The next lemma shows that this certificate notion is equivalent to the
predicate \verb|subset_sum_true|.  This equivalence is used later to prove
that SUBSET--SUM lies in \(\mathcal{NP}\) via a verifier machine in the
Cook--Levin framework.
\<close>

definition ss_cert_ok :: "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool" where
  "ss_cert_ok as s xs \<longleftrightarrow>
     length xs = length as \<and>
     set xs \<subseteq> {0,1} \<and>
     (\<Sum> i<length as. as ! i * xs ! i) = s"

lemma subset_sum_true_iff_cert:
  "subset_sum_true as s \<longleftrightarrow> (\<exists>xs. ss_cert_ok as s xs)"
proof
  assume "subset_sum_true as s"
  then obtain xs where
    xs_bitvec: "xs \<in> bitvec (length as)" and
    sum_eq:     "(\<Sum> i<length as. as ! i * xs ! i) = s"
    unfolding subset_sum_true_def by blast
  hence len: "length xs = length as"
    and vals: "set xs \<subseteq> {0,1}"
    unfolding bitvec_def by auto
  hence "ss_cert_ok as s xs"
    unfolding ss_cert_ok_def using sum_eq by simp
  thus "\<exists>xs. ss_cert_ok as s xs"
    by blast
next
  assume "\<exists>xs. ss_cert_ok as s xs"
  then obtain xs where
    ok: "ss_cert_ok as s xs"
    by blast
  from ok have len: "length xs = length as"
    and vals: "set xs \<subseteq> {0,1}"
    and sum_eq: "(\<Sum> i<length as. as ! i * xs ! i) = s"
    unfolding ss_cert_ok_def by auto
  hence "xs \<in> bitvec (length as)"
    unfolding bitvec_def by auto
  thus "subset_sum_true as s"
    unfolding subset_sum_true_def
    using sum_eq by blast
qed

subsection \<open>SUBSET--SUM is in NP (via an abstract verifier)\<close>

text \<open>
We now introduce an abstract verifier locale matching the
\verb|Cook_Levin.NP| characterisation of the class \(\mathcal{NP}\).

A verifier instance consists of the following components:

\begin{itemize}
\item an instance encoding \verb|enc0 :: int list \<Rightarrow> int \<Rightarrow> string|;
\item a certificate encoding
      \verb|enc_cert :: int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> string|;
\item a Turing machine \verb|V| computing a Boolean verification function
      \verb|fverify|;
\item a polynomial bound \verb|p| on the certificate length as a function of
      the instance length; and
\item a time bound \verb|T| on the verifier computation.
\end{itemize}

The locale assumptions express that \verb|V| is a correct NP-style verifier
for SUBSET--SUM with respect to \verb|enc0| and \verb|enc_cert|:

\begin{itemize}
\item for every true SUBSET--SUM instance \verb|(as, s)|, there exists a
      certificate \verb|xs| such that the verifier accepts
      \verb|enc0 as s| together with \verb|enc_cert as s xs|;
\item whenever the verifier accepts an encoded instance and certificate,
      the corresponding certificate \verb|xs| satisfies the SUBSET--SUM
      specification.
\end{itemize}

From these assumptions we obtain the standard NP-membership statement
\[
  \verb|SUBSETSUM_lang enc0| \in \mathcal{NP},
\]
for any instance encoding \verb|enc0| admitting such a verifier.
\<close>

locale SS_Verifier_NP =
  fixes k G V p T fverify enc0 enc_cert
  assumes V_tm:
    "turing_machine k G V"
  assumes p_poly:
    "polynomial p"
  assumes T_poly:
    "big_oh_poly T"
  assumes V_time:
    "computes_in_time k V fverify T"
  assumes V_outlen:
    "\<And>y. length (fverify y) = 1"
  assumes V_complete:
    "\<And>as s. subset_sum_true as s \<Longrightarrow>
       \<exists>xs.
         ss_cert_ok as s xs \<and>
         length (enc_cert as s xs) = p (length (enc0 as s)) \<and>
         fverify \<langle>enc0 as s, enc_cert as s xs\<rangle> = [\<bbbI>]"
  assumes V_sound:
    "\<And>as s u.
       fverify \<langle>enc0 as s, u\<rangle> = [\<bbbI>] \<Longrightarrow>
       length u = p (length (enc0 as s)) \<Longrightarrow>
       \<exists>xs. ss_cert_ok as s xs \<and> u = enc_cert as s xs"
  assumes V_wf:
    "\<And>x u. fverify \<langle>x, u\<rangle> = [\<bbbI>] \<Longrightarrow> \<exists>as s. x = enc0 as s"


section \<open>SUBSET--SUM as a language\<close>

text \<open>
Given an instance-encoding function \verb|enc0|, we obtain the language
\verb|SUBSETSUM_lang enc0| consisting of all strings that encode true
SUBSET--SUM instances.
\<close>

definition SUBSETSUM_lang :: "(int list \<Rightarrow> int \<Rightarrow> string) \<Rightarrow> language" where
  "SUBSETSUM_lang enc0 \<equiv>
     {x. \<exists>as s. x = enc0 as s \<and> subset_sum_true as s}"

subsection \<open>SUBSET--SUM is in NP (relative to enc0)\<close>

text \<open>
The following lemma packages the locale \verb|SS_Verifier_NP| into the
alternative NP characterization \verb|NP_output_len_1| provided by
\verb|Cook_Levin.NP|.

It shows that any suitable verifier yields a language
\verb|SUBSETSUM_lang enc0| that belongs to \(\mathcal{NP}\).

This is the formal statement that SUBSET--SUM lies in NP with respect to
the chosen instance encoding \verb|enc0|.
\<close>

lemma SUBSETSUM_in_NP_from_verifier:
  fixes k G V p T fverify enc0 enc_cert
  assumes verif: "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 \<in> \<N>\<P>"
proof -
  interpret V: SS_Verifier_NP k G V p T fverify enc0 enc_cert
    using verif .

  have witness:
    "\<exists>k G M p T fver.
       turing_machine k G M \<and>
       polynomial p \<and>
       big_oh_poly T \<and>
       computes_in_time k M fver T \<and>
       (\<forall>y. length (fver y) = 1) \<and>
       (\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
              (\<exists>u. length u = p (length x) \<and> fver \<langle>x, u\<rangle> = [\<bbbI>]))"
  proof (intro exI conjI)
    show "turing_machine k G V"
      by (rule V.V_tm)
    show "polynomial p"
      by (rule V.p_poly)
    show "big_oh_poly T"
      by (rule V.T_poly)
    show "computes_in_time k V fverify T"
      by (rule V.V_time)
    show "\<forall>y. length (fverify y) = 1"
      using V.V_outlen by simp

    show "\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
              (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])"
    proof
      fix x :: string
      show "x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
              (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])"
      proof
        (* (\<Rightarrow>) completeness: from x \<in> language to a suitable witness u *)
        assume "x \<in> SUBSETSUM_lang enc0"
        then obtain as s where
          x_def: "x = enc0 as s" and
          sat:   "subset_sum_true as s"
          unfolding SUBSETSUM_lang_def by blast

        from V.V_complete[OF sat] obtain xs where
          xs_ok: "ss_cert_ok as s xs" and
          len_u: "length (enc_cert as s xs) = p (length (enc0 as s))" and
          acc:   "fverify \<langle>enc0 as s, enc_cert as s xs\<rangle> = [\<bbbI>]"
          by blast

        have "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]"
          using x_def len_u acc by blast
        thus "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]" .
      next
        (* (\<Leftarrow>) soundness: from a witness u back to x \<in> language *)
        assume RHS: "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]"
        then obtain u where
          len_u: "length u = p (length x)" and
          acc:   "fverify \<langle>x, u\<rangle> = [\<bbbI>]"
          by blast

        from V.V_wf[OF acc] obtain as s where
          x_def: "x = enc0 as s"
          by blast

        from acc x_def have acc_enc:
          "fverify \<langle>enc0 as s, u\<rangle> = [\<bbbI>]"
          by simp
        from len_u x_def have len_u_enc:
          "length u = p (length (enc0 as s))"
          by simp

        from V.V_sound[OF acc_enc len_u_enc]
        obtain xs where xs_ok: "ss_cert_ok as s xs" and u_enc: "u = enc_cert as s xs"
          by blast

        from xs_ok have "subset_sum_true as s"
          using subset_sum_true_iff_cert by blast
        hence "x \<in> SUBSETSUM_lang enc0"
          unfolding SUBSETSUM_lang_def using x_def by blast
        thus "x \<in> SUBSETSUM_lang enc0" .
      qed
    qed
  qed

  from witness
  obtain k G M p T fver where
    tm:      "turing_machine k G M" and
    poly_p:  "polynomial p" and
    T_poly:  "big_oh_poly T" and
    time:    "computes_in_time k M fver T" and
    outlen:  "\<forall>y. length (fver y) = 1" and
    corr:    "\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
                   (\<exists>u. length u = p (length x) \<and> fver \<langle>x, u\<rangle> = [\<bbbI>])"
    by blast

  have witness':
    "\<exists>k G M.
       turing_machine k G M \<and>
       (\<exists>p. polynomial p \<and>
        (\<exists>T. big_oh_poly T \<and>
         (\<exists>fver.
            computes_in_time k M fver T \<and>
            (\<forall>y. length (fver y) = 1) \<and>
            (\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
                   (\<exists>u. length u = p (length x) \<and> fver \<langle>x, u\<rangle> = [\<bbbI>])))))"
    using tm poly_p T_poly time outlen corr by blast

  show "SUBSETSUM_lang enc0 \<in> \<N>\<P>"
    unfolding NP_output_len_1
    using witness' by blast
qed


subsection \<open>A Cook--Levin machine that solves SUBSET--SUM\<close>

text \<open>
The locale \verb|CL_SubsetSum_Solver| packages the basic assumptions for a
Cook--Levin Turing machine that decides SUBSET--SUM.

It is parameterised by:

\begin{itemize}
\item a machine \verb|M| that is well formed as a \verb|k_tapes| machine with
      start state \verb|q0|;
\item an encoding function \verb|enc| that maps instances \((as,s)\) to Boolean
      input strings;
\item a correctness condition stating that \verb|M| accepts exactly the
      encodings of true SUBSET--SUM instances:
      \[
        \verb|accepts_CL M (enc as s)| \;\longleftrightarrow\;
        \verb|subset_sum_true as s|.
      \]
\end{itemize}

The parameter \verb|q0| is included to match the Cook--Levin library’s
well-formedness predicate \verb|turing_machine k_tapes q0 M|.
All execution semantics used below start from the corresponding
\verb|start_config|.
\<close>

locale CL_SubsetSum_Solver =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list \<Rightarrow> int \<Rightarrow> bool list"
  assumes turing: "turing_machine k_tapes q0 M"
  assumes solves_subset_sum:
    "\<And>as s. accepts_CL_halt M (enc as s) \<longleftrightarrow> subset_sum_true as s"
begin

text \<open>
We will later relate the abstract cost \verb|steps_TM| to the concrete
Cook--Levin step count \verb|steps_CL M (enc as s)| in the
\verb|LR_Read_TM| locale.
\<close>

definition read0_TM :: "int list \<Rightarrow> int \<Rightarrow> nat set" where
  "read0_TM as s = read0_CL M (enc as s)"

lemma read0_TM_subset:
  "read0_TM as s \<subseteq> {..<length (enc as s)}"
  unfolding read0_TM_def
  using read0_CL_subset_indices by simp

end  (* context CL_SubsetSum_Solver *)

section \<open>LR-read TM interface and lower bound inheritance\<close>

text \<open>
We now introduce the Cook--Levin--side LR-read interface and import the
abstract lower bound via \verb|SubsetSum_Reader_Model| (from
\verb|SubsetSum_DecisionTree|).

A Cook--Levin machine is considered polynomial-time on SUBSET-SUM if its
step count on an instance \verb|(as, s)| is bounded by some polynomial in
\verb|length as|.  We deliberately take \verb|length as| as the size
parameter and ignore the bit-length of \verb|enc as s| at this stage.

This choice aligns the Cook--Levin execution semantics with the abstract
decision-tree model used in \verb|SubsetSum_DecisionTree|.  It is not
intended to claim robustness under arbitrary encodings.  In particular,
this file does not attempt to relate \verb|length (enc as s)| to the
bit-length of the integers in \verb|as|.

These modelling assumptions are captured by the LR-read interface
introduced below.
\<close>

definition polytime_CL_machine
  :: "machine \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> bool list) \<Rightarrow> bool"
where
  "polytime_CL_machine M enc \<longleftrightarrow>
     (\<exists>(c::real)>0. \<exists>(d::nat).
        \<forall>as s. steps_CL M (enc as s)
               \<le> nat (ceiling (c * (real (length as)) ^ d)))"

text \<open>
The size parameter used here is \verb|length as|, matching the abstract
decision-tree model.  We do not claim robustness under alternative
encodings or under bit-length measures.  This theory provides only a
bridge between the LR-read model and Cook--Levin execution semantics.
This is a modelling choice for the bridge, not a claim about standard
bit-complexity for SUBSET-SUM.
\<close>

text \<open>
The locale \verb|LR_Read_TM| is the Cook--Levin analogue of
\verb|SubsetSum_Reader_Model|.  It assumes the following:

\begin{itemize}
\item \verb|M, q0, enc| form a SUBSET-SUM solver in the sense of
      \verb|CL_SubsetSum_Solver|.

\item For each instance \verb|(as, s)| with \verb|distinct_subset_sums as|,
      there exists a split index \verb|k| at which the abstract ``seen''
      sets \verb|seenL_TM| and \verb|seenR_TM| coincide with the canonical
      split sets
      \[
        \verb|LHS (e_k as s k) (length as)| \quad\text{and}\quad
        \verb|RHS (e_k as s k) (length as)|.
      \]

      That is, for some \verb|k \<le> length as| we postulate the equalities
      \[
        \verb|seenL_TM as s k| =
        \verb|LHS (e_k as s k) (length as)|,
      \]
      \[
        \verb|seenR_TM as s k| =
        \verb|RHS (e_k as s k) (length as)|.
      \]

      These equalities constitute the core LR-read assumption.  They assert
      that, at some split position \verb|k|, the machine's observable
      information flow covers exactly the canonical LHS/RHS candidate
      families.

      This is a strong LR-read requirement: at the critical split \verb|k|,
      the machine's information covers precisely the LHS/RHS families that
      drive the decision-tree lower bound, not merely a subset of them.
      The hypothesis is expressed as set equalities rather than inclusions,
      so that the abstract decision-tree lower bound transfers directly
      to the Cook--Levin setting.

\item For all \verb|as|, \verb|s|, and \verb|k|, the step count satisfies the
      lower bound
      \[
        \verb|steps_TM as s| \ge
        \verb|card (seenL_TM as s k)| +
        \verb|card (seenR_TM as s k)|.
      \]
\end{itemize}

These conditions are assumptions about the machine's information flow.
They are not derived from Cook--Levin execution semantics alone.  They
match exactly the abstract axioms of \verb|SubsetSum_Reader_Model| under
the identifications
\[
  \verb|steps = steps_TM|,\quad
  \verb|seenL = seenL_TM|,\quad
  \verb|seenR = seenR_TM|.
\]

Once the interpretation succeeds, the \(\sqrt{2^n}\) lower bound is
obtained specialised to the Cook--Levin step count of \verb|M|.  In
particular, this yields the impossibility of a single polynomial upper
bound on \verb|steps_TM| over all distinct-subset-sums instances.
\<close>

locale LR_Read_TM =
  CL_SubsetSum_Solver M q0 enc
  for M   :: machine
    and q0 :: nat
    and enc :: "int list \<Rightarrow> int \<Rightarrow> bool list" +
  fixes steps_TM :: "int list \<Rightarrow> int \<Rightarrow> nat"
    and seenL_TM :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set"
    and seenR_TM :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set"
  assumes steps_TM_CL:
    "\<And>as s. steps_TM as s = steps_CL M (enc as s)"
  assumes LR_read_coverage:
    "\<And>as s. distinct_subset_sums as \<Longrightarrow>
       \<exists>k\<le>length as.
         seenL_TM as s k = LHS (e_k as s k) (length as) \<and>
         seenR_TM as s k = RHS (e_k as s k) (length as)"
  assumes LR_read_cost:
    "\<And>as s k. k \<le> length as \<Longrightarrow>
       steps_TM as s \<ge> card (seenL_TM as s k) + card (seenR_TM as s k)"
begin


text \<open>
We instantiate the abstract lower-bound locale
\verb|SubsetSum_Reader_Model| with the concrete objects
\verb|steps_TM|, \verb|seenL_TM|, and \verb|seenR_TM|.
All theorems proved in \verb|SubsetSum_Reader_Model| then become available
under the locale interpretation prefix \verb|Reader|.
\<close>

interpretation Reader:
  SubsetSum_Reader_Model steps_TM seenL_TM seenR_TM
proof
  fix as s
  assume dist: "distinct_subset_sums as"
  obtain k where
    k_le: "k \<le> length as"
    and covL: "seenL_TM as s k = LHS (e_k as s k) (length as)"
    and covR: "seenR_TM as s k = RHS (e_k as s k) (length as)"
    using LR_read_coverage[OF dist] by blast
  have step_ge: "steps_TM as s \<ge> card (seenL_TM as s k) + card (seenR_TM as s k)"
    using LR_read_cost[OF k_le] .
  show "\<exists>k\<le>length as.
          seenL_TM as s k = LHS (e_k as s k) (length as) \<and>
          seenR_TM as s k = RHS (e_k as s k) (length as) \<and>
          steps_TM as s \<ge> card (seenL_TM as s k) + card (seenR_TM as s k)"
    using k_le covL covR step_ge by blast
qed

text \<open>
From this point on, all lower-bound statements are inherited from
\verb|SubsetSum_Reader_Model| and applied to the Cook--Levin specialised
cost measures.

In particular, specialising
\verb|Reader.subset_sum_sqrt_lower_bound| yields the concrete lower bound
for \verb|steps_TM|.  This is the Turing-machine-level analogue of the
\(\sqrt{2^n}\) decision-tree lower bound.
\<close>

theorem subset_sum_sqrt_lower_bound_TM:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as"
      and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) \<le> real (steps_TM as s)"
  using Reader.subset_sum_sqrt_lower_bound[OF distinct n_def]
  by simp

corollary subset_sum_sqrt_lower_bound_CL:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) \<le> real (steps_CL M (enc as s))"
proof -
  have lb: "2 * sqrt ((2::real) ^ n) \<le> real (steps_TM as s)"
    using subset_sum_sqrt_lower_bound_TM[OF n_def distinct] .
  have "steps_TM as s = steps_CL M (enc as s)"
    by (simp add: steps_TM_CL)
  hence "real (steps_TM as s) = real (steps_CL M (enc as s))"
    by simp
  from lb this show ?thesis
    by simp
qed

text \<open>
We now show that no machine satisfying the LR-read assumptions can have its
step count bounded by a single polynomial over all instances with
\verb|distinct_subset_sums as|.  The proof combines the analytic lemma
\verb|exp_beats_poly_ceiling_strict_TM| with the
\(\sqrt{2^n}\) lower bound and the canonical distinct-subset-sums family
provided by \verb|exists_distinct_family_TM|.

The scope of this impossibility result is deliberately restricted:

\begin{itemize}
\item It is stated only for the subfamily of instances satisfying
      \verb|distinct_subset_sums as|.

\item It does \emph{not} assert that the machine \verb|M| fails to run in
      polynomial time on arbitrary inputs.  Rather, it rules out the
      existence of a \emph{single} polynomial bound that holds uniformly
      over all distinct-subset-sums instances.
\end{itemize}

This is exactly the quantitative content imported from
\verb|SubsetSum_DecisionTree| via \verb|SubsetSum_Reader_Model| and the
LR-read assumptions, and no stronger claim is made.
\<close>

theorem no_polytime_TM_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
             \<forall>as s. distinct_subset_sums as \<longrightarrow>
               steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "\<exists>(c::real)>0. \<exists>(d::nat).
       \<forall>as s. distinct_subset_sums as \<longrightarrow>
         steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "\<forall>as s. distinct_subset_sums as \<longrightarrow>
                    steps_TM as s
                      \<le> nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  from exp_beats_poly_ceiling_strict_TM[OF cpos]
  obtain N :: nat where N:
    "\<forall>n\<ge>N. of_int (ceiling (c * (real n) ^ d))
           < 2 * sqrt ((2::real) ^ n)"
    by blast

  have N_ge: "N \<ge> N" by simp

  (* Choose a distinct-subset-sums instance of length N. *)
  from exists_distinct_family_TM
  obtain as where len_as: "length as = N"
    and dist_as: "distinct_subset_sums as"
    by blast

  from N[rule_format, OF N_ge]
  have ceil_lt:
    "of_int (ceiling (c * (real N) ^ d))
       < 2 * sqrt ((2::real) ^ N)"
    by simp
  hence ceil_lt':
    "of_int (ceiling (c * (real (length as)) ^ d))
       < 2 * sqrt ((2::real) ^ (length as))"
    by (simp add: len_as)

  (* Lower bound from the imported \<surd>(2ⁿ) theorem, instantiated at s = 0. *)
  have lb:
    "2 * sqrt ((2::real) ^ N) \<le> real (steps_TM as 0)"
  proof -
    have "2 * sqrt ((2::real) ^ N) \<le> real (steps_TM as 0)"
    proof (rule subset_sum_sqrt_lower_bound_TM)
      show "N = length as"
        using len_as by simp
    next
      show "distinct_subset_sums as"
        using dist_as .
    qed
    thus ?thesis .
  qed

  (* Polynomial upper bound assumption, instantiated to as, s = 0. *)
  have ub_nat:
    "steps_TM as 0 \<le> nat (ceiling (c * (real (length as)) ^ d))"
    using bound dist_as by simp

  (* Relate \<open>nat \<lceil>\<dots>\<rceil>\<close> and \<open>of_int \<lceil>\<dots>\<rceil>\<close>. *)
  have nonneg: "0 \<le> c * (real (length as)) ^ d"
    using cpos by simp
  hence ceil_ge0: "0 \<le> ceiling (c * (real (length as)) ^ d)"
    by simp
  hence conv:
    "real (nat (ceiling (c * (real (length as)) ^ d)))
       = of_int (ceiling (c * (real (length as)) ^ d))"
    by simp

  from ub_nat have ub_real:
    "real (steps_TM as 0)
       \<le> of_int (ceiling (c * (real (length as)) ^ d))"
    using conv by simp

  (* Lower bound, upper bound, and strict separation contradict each other. *)
  from ceil_lt' lb ub_real
  show False using len_as by auto
qed

text \<open>
The same impossibility result can be restated directly in terms of the
underlying Cook--Levin step count \verb|steps_CL| on encoded instances.
This is the CL-level formulation used in the P~$\neq$~NP theory, captured
by the theorem \verb|no_polytime_CL_on_distinct_family|.

It states that, under the LR-read assumptions, there exists no single
polynomial that bounds \verb|steps_CL M (enc as s)| uniformly over all
inputs satisfying \verb|distinct_subset_sums as|.
\<close>

corollary no_polytime_CL_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
             \<forall>as s. distinct_subset_sums as \<longrightarrow>
               steps_CL M (enc as s)
                 \<le> nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "\<exists>(c::real)>0. \<exists>(d::nat).
       \<forall>as s. distinct_subset_sums as \<longrightarrow>
         steps_CL M (enc as s)
           \<le> nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound_CL: "\<forall>as s. distinct_subset_sums as \<longrightarrow>
                      steps_CL M (enc as s)
                        \<le> nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  (* Transfer the polynomial bound from steps_CL to steps_TM using steps_TM_CL. *)
  have bound_TM:
    "\<forall>as s. distinct_subset_sums as \<longrightarrow>
       steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
  proof (intro allI impI)
    fix as s
    assume "distinct_subset_sums as"
    then have "steps_CL M (enc as s)
                 \<le> nat (ceiling (c * (real (length as)) ^ d))"
      using bound_CL by simp
    moreover have "steps_TM as s = steps_CL M (enc as s)"
      by (simp add: steps_TM_CL)
    ultimately show "steps_TM as s
                       \<le> nat (ceiling (c * (real (length as)) ^ d))"
      by simp
  qed

  have "\<exists>(c::real)>0. \<exists>(d::nat).
          \<forall>as s. distinct_subset_sums as \<longrightarrow>
            steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound_TM by blast
  with no_polytime_TM_on_distinct_family show False
    by blast
qed

end  (* locale LR_Read_TM *)

end  (* theory *)