theory SubsetSum_PneqNP_Conditional
  imports SubsetSum_CookLevin
begin

text ‹
\section{A conditional $\neg(\mathcal{P}=\mathcal{NP})$ implication from an 
information-flow principle}

\paragraph{Origin and purpose.}
This development is motivated by the informal lower-bound discussion in

\begin{quote}
C.\ A.\ Feinstein, \emph{``Dialogue Concerning the Two Chief World Views,''}
arXiv:1605.08639.
\end{quote}

The paper is used only as motivation: no statement from it is imported as a
formal fact.  The formal contribution here is to isolate a single
\emph{information-flow} requirement suggested by that discussion and to state it
precisely in Isabelle/HOL.

The requirement, called \emph{LR-read}, is an interface property describing when
a SUBSET--SUM solver exposes and distinguishes the canonical left-hand and
right-hand candidate values induced by splitting the verification equation.
Once LR-read is assumed, all remaining steps are derived inside Isabelle/HOL
from (i) the abstract reader-style lower bound in ‹SubsetSum_DecisionTree› and
(ii) Cook--Levin Turing-machine semantics from the AFP \emph{Cook\_Levin} entry,
connected by ‹SubsetSum_CookLevin›.

\paragraph{Scope note: size measure.}
All running-time statements in this development measure the size of an instance
\((as,s)\) by the \emph{unary} parameter \verb|length as| (the number of weights),
not by the bit-length of an encoding such as \verb|enc0 as s|.  Consequently:

\begin{itemize}
\item this is \emph{not} a proof of $\mathcal{P}\neq\mathcal{NP}$ in the standard
      bit-complexity sense; and
\item no encoding-robustness claim is made (the analysis is not intended to be
      invariant under arbitrary changes of representation).
\end{itemize}

\paragraph{Scope note: languages versus machines.}
The Cook--Levin library defines \(\mathcal{P}\) and \(\mathcal{NP}\) at the level
of \emph{languages}.  To connect the language-level statement
\(\text{SUBSET--SUM} \in \mathcal{P}\) to the existence of a concrete Cook--Levin
machine that decides SUBSET--SUM on a designated Boolean encoding, 
we state an explicit \emph{realisability bridge} (defined below as 
\verb|P_impl_CL_SubsetSum_Solver enc0 encB|). Throughout this theory, \verb|encB| 
is treated as a fixed parameter, namely the Boolean representation with respect to 
which Cook–Levin machines are assumed to operate. This bridge is logically independent 
of LR-read and is kept separate so that all modelling dependencies remain explicit.

\bigskip
\begin{center}
\textbf{Summary of the logical structure}
\end{center}
\bigskip

\begin{enumerate}
\item \textbf{Abstract lower bound.}
  In ‹SubsetSum_DecisionTree› we prove that any solver satisfying a reader-style
  candidate-distinguishing condition must take \(\Omega(\sqrt{2^n})\) steps on
  instances with \verb|distinct_subset_sums as|, where \(n = \verb|length as|\).

\item \textbf{Transfer to Cook--Levin machines (LR-read interface).}
  In ‹SubsetSum_CookLevin› we show that any Cook--Levin machine deciding
  SUBSET--SUM and satisfying LR-read inherits the same
  \(\Omega(\sqrt{2^n})\) lower bound (still measured in \(n=\verb|length as|\)).

\item \textbf{Global LR-read hypothesis.}
  Because Cook--Levin machines may preprocess and reorganise their input
  arbitrarily, LR-read is not a semantic consequence of the execution model and
  must be assumed explicitly.  We therefore package a global hypothesis asserting
  that every polynomial-time SUBSET--SUM solver admits an LR-read presentation.

\item \textbf{Conditional implication.}
  Assuming \(\mathcal{P}=\mathcal{NP}\) and SUBSET--SUM \(\in\mathcal{NP}\) yields
  SUBSET--SUM \(\in\mathcal{P}\).  The realisability bridge then provides a
  polynomial-time Cook--Levin solver; the global LR-read hypothesis upgrades it
  to an LR-read solver; and the inherited \(\Omega(\sqrt{2^n})\) lower bound
  contradicts polynomial time on a canonical distinct-family.  Hence
  \(\neg(\mathcal{P}=\mathcal{NP})\) follows \emph{relative to the stated
  modelling assumptions}.
\end{enumerate}

\paragraph{Acknowledgement.}
The author received assistance from AI systems (ChatGPT by OpenAI and Claude by
Anthropic) in drafting explanatory text and in iteratively refining Isabelle/HOL
proof scripts.  All formal results and final proofs are the responsibility of
the author.
›

section ‹Roadmap›

text ‹
This file proceeds in three stages.

\begin{itemize}
\item We state the modelling assumptions used later: the language-to-machine
      realisability bridge and the global LR-read hypothesis.

\item Using these assumptions, we rule out polynomial-time Cook--Levin solvers
      for SUBSET--SUM by importing an \(\Omega(\sqrt{2^n})\) lower bound on a
      canonical family of instances with \verb|distinct_subset_sums as|.

\item We combine this impossibility with SUBSET--SUM \(\in\mathcal{NP}\) and the
      consequence of \(\mathcal{P}=\mathcal{NP}\) (namely SUBSET--SUM
      \(\in\mathcal{P}\)), deriving \(\neg(\mathcal{P}=\mathcal{NP})\) relative to
      the stated assumptions.
\end{itemize}
›

section ‹The LR-read assumption›

text ‹
We begin with the elementary task of deciding whether two integers
\verb|L| and \verb|R| are equal.

Suppose the solver does not initially know the values of \verb|L| and \verb|R|,
and can obtain information about them only through its observable interactions
with the input.  Then correctness requires that the solver obtain some
distinguishing information from \emph{both} sides.

By itself, this observation concerns only a single pair of integers.
Its relevance to SUBSET--SUM arises from the canonical split of the
verification equation.

For any split position \verb|k|, the decomposition \verb|e_k (as, s)|
gives rise to two families of possible integer values:

\begin{itemize}
\item \verb|LHS (e_k as s k)|, containing up to \verb|2^k| left-hand values;
\item \verb|RHS (e_k as s k)|, containing up to \verb|2^(n - k)| right-hand values.
\end{itemize}

Each element of these sets is a concrete integer that the left-hand or
right-hand side of the equation could take under some hidden choice of
the Boolean vector \verb|xs| consistent with the same instance
\verb|(as, s)|.

In an information-flow (reader-style) model, correctness is expressed by
requiring that, for some split position \verb|k|, the solver's observable
behaviour distinguish all canonical candidates on both sides.  If some
candidate value were never distinguished, the solver could not reliably
tell the difference between instances with and without a valid equality.

Viewed through this basic equality principle, we obtain a per-candidate
requirement: for some split position \verb|k|, a correct solver in the 
reader-style model must effectively distinguish every possible numerical 
value in both \verb|LHS (e_k as s k)| and \verb|RHS (e_k as s k)|.  Otherwise, 
an adversary could keep the solver's observations fixed while choosing hidden
subsets that differ in whether an equality \verb|L = R| exists.

This per-candidate requirement is exactly what drives the abstract reader
lower bound proved earlier.
›

section ‹Why LR-read is assumed rather than proved›

text ‹
A natural question is why the predicate \verb|LR_read| is not proved
directly from the Cook--Levin Turing-machine semantics.

The reason is conceptual rather than technical.

The Cook--Levin model permits a machine to preprocess, compress, and
reorganise its input arbitrarily before performing any semantic
distinctions.  Nothing in the execution semantics alone enforces a
correspondence between a machine's observable behaviour and the canonical
left/right candidate values induced by the subset-sum decomposition
\verb|e_k (as, s)|.

As a result, the abstract information-flow principle used in
\verb|SubsetSum_DecisionTree|, which reasons in terms of distinguishing
individual candidate values, does not directly transfer to the
Cook--Levin model.  The semantics do not require a machine's observable
behaviour to expose these distinctions at the level needed for a
per-candidate adversary argument.

Establishing \verb|LR_read| from first principles would therefore require
an additional structural theorem about polynomial-time Turing machines,
namely that any such machine deciding equality-type problems admits a
presentation in which canonical left-hand and right-hand candidate values
are separately observable.  This does not follow from the Cook--Levin
execution semantics developed here and is therefore stated explicitly as a
modelling hypothesis.

The contribution of the present formalisation is to show that:

\begin{itemize}
\item once \verb|LR_read| is assumed, the exponential lower bound follows
      formally; and
\item once the realisability bridge is made explicit, the only additional 
      information-flow assumption is \verb|LR_read|.
\end{itemize}

In this sense, the theory isolates a single, sharply defined
information-flow predicate as the exact point on which the present
conditional implication hinges.

From a methodological perspective, the role played by \verb|LR_read| is
not unusual in complexity-theoretic lower-bound arguments.  Most known
unconditional lower bounds are proved relative to models that impose
explicit or implicit structural restrictions on how information may be
accessed or combined, such as monotonicity, bounded fan-in, fixed
communication partitions, read-once conditions, or explicit query
interfaces.

The present formalisation differs only in that this restriction is made
explicit as a separate predicate rather than being built silently into
the computational model.  Once stated, the resulting lower bound follows
formally.
›

section ‹A global LR-read axiom for Cook--Levin solvers›

text ‹
We now state the key bridge axiom in a direct form.

If a Cook--Levin machine \verb|M| correctly decides SUBSET--SUM and runs in
polynomial time, then it satisfies the locale \verb|LR_Read_TM_Derived| for some
choice of observable ``seen'' sets and a step counter.

Intuitively, \verb|seenL_TM| and \verb|seenR_TM| record which canonical
left-hand and right-hand candidates are distinguished by the machine's
observable behaviour.  The locale \verb|LR_Read_TM_Derived| is the concrete
machine-level formalisation of the informal LR-read principle described
above.

Once \verb|LR_Read_TM_Derived| holds, the contradiction with polynomial time is
already established in \verb|SubsetSum_CookLevin| (as
\verb|no_polytime_CL_on_distinct_family|).  We therefore first present the
implication ``polynomial-time solver implies LR-read'' as a locale-local
axiom for a fixed machine, and later package it as a global hypothesis
quantified over all machines.
›

locale LR_Read_Axiom =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list ⇒ int ⇒ bool list"
  assumes poly_solver_admits_LR_Read:
    "⟦ CL_SubsetSum_Solver M q0 enc;
       polytime_CL_machine M enc ⟧
     ⟹ ∃isL candL_of_pos candR_of_pos.
           LR_Read_TM_Derived M q0 enc isL candL_of_pos candR_of_pos"
begin

text ‹
Main consequence inside this locale.

Under the assumption \emph{LR\_Read\_Axiom}, there exists no polynomial-time
Cook--Levin solver for SUBSET--SUM.

The reason is as follows.  If a Cook--Levin machine \verb|M| were to decide
SUBSET--SUM in polynomial time, the axiom would yield an instance of
\verb|LR_Read_TM_Derived| for \verb|M|.  However, the Cook--Levin development already
establishes that \verb|LR_Read_TM_Derived| implies an exponential lower bound on the
machine's running time on the family of instances with
\verb|distinct_subset_sums as|.

Thus the LR-read assumption, when combined with polynomial-time solvability,
leads to a contradiction inside this locale.
›

lemma no_polytime_CL_SubsetSum_solver:
  assumes solver: "CL_SubsetSum_Solver M q0 enc"
      and poly:   "polytime_CL_machine M enc"
  shows False
proof -
  (* 1. From the axiom, get LR_Read_TM_Derived for this solver *)
  from poly_solver_admits_LR_Read[OF solver poly]
  obtain isL candL_of_pos candR_of_pos
    where LR: "LR_Read_TM_Derived M q0 enc isL candL_of_pos candR_of_pos"
    by blast

  interpret LR: LR_Read_TM_Derived M q0 enc isL candL_of_pos candR_of_pos
    by (rule LR)

  (* 3. Unpack the polynomial-time assumption for M, enc *)
  from poly obtain c d where
    cpos: "c > 0" and
    bound_all:
      "∀as s. steps_CL M (enc as s)
                ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def
    by blast

  (* 4. Restrict that bound to distinct-subset-sum instances *)
  have bound_restricted:
    "∀as s. distinct_subset_sums as ⟶
             steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound_all by blast

  (* 5. Package it into the existential form that contradicts
        no_polytime_CL_on_distinct_family *)
  have ex_poly_on_distinct:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by (intro exI[of _ c] exI[of _ d] conjI cpos bound_restricted)

  (* 6. Contradiction with the LR_Read_TM_Derived-level impossibility theorem *)
  (* 6'. Derive a contradiction directly from the sqrt lower bound + exp beats poly *)
  obtain N where H:
    "∀n≥N. of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
    using exp_beats_poly_ceiling_strict_TM[OF cpos]
    by blast

  (* Pick a large enough n and a distinct-subset-sums instance of that length *)
  let ?n = "N"
  obtain as where len_as: "length as = ?n" and dist_as: "distinct_subset_sums as"
    using exists_distinct_family_TM[rule_format, of ?n]
    by blast
  let ?s = "0::int"

  (* Upper bound from polytime *)
  have ub_nat:
    "steps_CL M (enc as ?s) ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound_all by blast

  have ub_real_direct:
    "real (steps_CL M (enc as ?s)) ≤ real (nat (ceiling (c * (real (length as)) ^ d)))"
    using ub_nat by simp

  (* Lower bound from LR-read transfer *)
  have n_def': "N = length as"
    by (simp add: len_as)

  have lb:
    "2 * sqrt ((2::real) ^ N) ≤ real (steps_CL M (enc as ?s))"
    using LR.subset_sum_sqrt_lower_bound_CL[OF n_def' dist_as, of ?s] .

  (* Strict inequality from exp beats poly, instantiated at n = length as = N *)
  have strict:
    "of_int (ceiling (c * (real (length as)) ^ d))
       < 2 * sqrt ((2::real) ^ (length as))"
  proof -
    have "length as ≥ N"
      by (simp add: len_as)
    from H[rule_format, OF this]
    show ?thesis .
  qed

  (* Contradiction: ub_real and lb force ≤, but strict says < in the opposite direction *)
  have lb_len:
    "2 * sqrt ((2::real) ^ (length as)) ≤ real (steps_CL M (enc as ?s))"
    using lb by (simp add: len_as)

  have ceil_nonneg:
    "0 ≤ ceiling (c * (real (length as)) ^ d)"
  proof -
    let ?y = "c * (real (length as)) ^ d"

    have y_nonneg: "0 ≤ ?y"
      using cpos by simp

    have y_le_ceiling: "?y ≤ (of_int (ceiling ?y) :: real)"
      by (rule le_of_int_ceiling)

    have ofint_ceiling_nonneg: "0 ≤ (of_int (ceiling ?y) :: real)"
      using y_nonneg y_le_ceiling
      by (rule order_trans)

    (* turn real nonnegativity into int nonnegativity WITHOUT simp-ing ceiling *)
    have "0 ≤ ceiling ?y"
    proof (rule ccontr)
      assume "¬ 0 ≤ ceiling ?y"
      hence ce_neg: "ceiling ?y < 0" by simp
      hence "(of_int (ceiling ?y) :: real) < 0" by simp
      with ofint_ceiling_nonneg show False by simp
    qed
    thus ?thesis by simp
  qed

  have ub_int:
    "real (steps_CL M (enc as ?s))
       ≤ of_int (ceiling (c * (real (length as)) ^ d))"
  proof -
    from ub_nat have
      "real (steps_CL M (enc as ?s))
         ≤ real (nat (ceiling (c * (real (length as)) ^ d)))"
      by simp
    also have "... = of_int (ceiling (c * (real (length as)) ^ d))"
      using ceil_nonneg by simp
    finally show ?thesis .
  qed

  have "2 * sqrt ((2::real) ^ (length as))
        ≤ of_int (ceiling (c * (real (length as)) ^ d))"
    using lb_len ub_int by linarith
  thus False
    using strict by linarith
qed

text ‹
A convenient corollary is that, assuming \verb|LR_Read_Axiom|, there exists
no polynomial-time Cook--Levin machine that solves SUBSET--SUM.
›

corollary no_polytime_SubsetSum:
  assumes solver: "CL_SubsetSum_Solver M q0 enc"
  shows "¬ polytime_CL_machine M enc"
proof
  assume poly: "polytime_CL_machine M enc"
  from no_polytime_CL_SubsetSum_solver[OF solver poly]
  show False .
qed

end  (* locale LR_Read_Axiom *)

section ‹SUBSET--SUM is in NP (formalised)›

text ‹
We reuse the verifier-based NP result established in
\verb|SubsetSum_CookLevin|.

In particular, if a standard NP verifier package
\verb|SS_Verifier_NP| is provided, then the language
\verb|SUBSETSUM_lang enc0| belongs to the class
\(\mathcal{NP}\).
›

lemma SUBSETSUM_in_NP_global:
  assumes "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  using SUBSETSUM_in_NP_from_verifier[OF assms] .

section ‹Definition of \(\mathcal{P} = \mathcal{NP}\)›

text ‹
We use the standard language-theoretic definition.

The equality \(\mathcal{P} = \mathcal{NP}\) means that a language belongs to
\(\mathcal{P}\) if and only if it belongs to \(\mathcal{NP}\).
›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

lemma P_eq_NP_imp: "P_eq_NP ⟹ (L ∈ 𝒩𝒫 ⟶ L ∈ 𝒫)"
  by (simp add: P_eq_NP_def)

lemma P_eq_NP_iff_sets: "P_eq_NP ⟷ (𝒫 = 𝒩𝒫)"
  using P_eq_NP_def by blast

section ‹From \(\mathcal{P}\)-membership to a Cook--Levin solver›

text ‹
This section provides a bridge from \emph{language complexity} to
\emph{machine existence}.

If SUBSET--SUM (with instance encoding \verb|enc0|) belongs to
\(\mathcal{P}\), then there exists a Cook--Levin Turing machine \verb|M|,
over the designated Boolean encoding \verb|encB|, such that \verb|M| decides
SUBSET--SUM correctly and runs in polynomial time.

We keep this bridge explicit because the language-level encoding \verb|enc0|
need not coincide with the designated Boolean encoding \verb|encB|.
Only the language \verb|SUBSETSUM_lang enc0| is relevant to the complexity-theoretic 
statement.

Here \verb|enc0| is the string encoding used to define the language
\verb|SUBSETSUM_lang enc0|, while the Cook--Levin solver is assumed to operate on
\verb|encB|.  The bridge axiom therefore relates only the language, not the concrete 
representations.
›

definition P_impl_CL_SubsetSum_Solver ::
  "(int list ⇒ int ⇒ string) ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool" where
" P_impl_CL_SubsetSum_Solver enc0 encB ⟷
    (SUBSETSUM_lang enc0 ∈ 𝒫 ⟶
       (∃M q0. CL_SubsetSum_Solver M q0 encB ∧ polytime_CL_machine M encB))"

definition admits_LR_read_TM_Derived ::
  "machine ⇒ nat ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool" where
  "admits_LR_read_TM_Derived M q0 enc ⟷
     (∃isL candL_of_pos candR_of_pos.
        LR_Read_TM_Derived M q0 enc isL candL_of_pos candR_of_pos)"

section ‹Global LR\_read hypothesis›

text ‹
This section states the single modelling assumption used in the final
conditional implication.

The predicate \verb|LR_read_hypothesis enc0 encB| consists of
two logically distinct components.

\begin{itemize}
\item \emph{Realisability bridge (complexity to machines).}
      If SUBSET--SUM (with instance encoding \verb|enc0|) belongs to
      \(\mathcal{P}\), then there exists a Cook--Levin Turing machine that
      decides SUBSET--SUM on \verb|encB| and runs in polynomial time.

\item \emph{Information-flow bridge (the LR-read content).}
      Every such polynomial-time Cook--Levin solver on \verb|encB| 
      admits an LR-read presentation, that is, it satisfies
      \verb|admits_LR_read_TM| and therefore exposes the canonical
      left/right per-candidate structure required to transfer the
      abstract decision-tree lower bound.
\end{itemize}

No NP-membership assumption is included in this hypothesis.
Membership of SUBSET--SUM in \(\mathcal{NP}\) is established independently,
via the verifier construction formalised earlier.
›

definition LR_read_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool" where
"LR_read_hypothesis enc0 encB ⟷
   P_impl_CL_SubsetSum_Solver enc0 encB ∧
   (∀M q0. CL_SubsetSum_Solver M q0 encB ⟶ polytime_CL_machine M encB ⟶
           admits_LR_read_TM_Derived M q0 encB)"

section ‹Core conditional theorem›

text ‹
The core argument can be summarised in a single paragraph.

Assume \(\mathcal{P} = \mathcal{NP}\). Since SUBSET--SUM belongs to \(\mathcal{NP}\), 
it would then also belong to \(\mathcal{P}\). By the realisability component of 
\verb|LR_read_hypothesis enc0 encB|, there would therefore exist a polynomial-time 
Cook--Levin Turing machine \verb|M| (with start state \verb|q0|) that decides 
SUBSET--SUM on the encoding \verb|encB|.

By the information-flow component of the same hypothesis, the machine
\verb|M| admits an LR-read presentation. However, the development in 
\verb|SubsetSum_CookLevin| already establishes that any LR-read Cook--Levin 
solver for SUBSET--SUM incurs an \(\Omega(\sqrt{2^n})\) lower bound on a family of 
instances with \verb|distinct_subset_sums|, and hence cannot run in polynomial time.

This contradiction shows that the assumptions cannot all hold simultaneously.
Formally, the theory proves the implication
\[
  \verb|LR_read_hypothesis enc0 encB| \;\Longrightarrow\;
  \neg (\mathcal{P} = \mathcal{NP}).
\]
›

lemma P_neq_NP_if_LR_read_hypothesis:
  fixes enc0 :: "int list ⇒ int ⇒ string"
    and encB :: "int list ⇒ int ⇒ bool list"
  assumes H:       "LR_read_hypothesis enc0 encB"
  assumes NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  shows "¬ P_eq_NP"
proof -
  from H have
    bridge_P: "P_impl_CL_SubsetSum_Solver enc0 encB"
    and all_LR_read:
      "∀M q0. CL_SubsetSum_Solver M q0 encB ⟶ polytime_CL_machine M encB ⟶
             admits_LR_read_TM_Derived M q0 encB"
    unfolding LR_read_hypothesis_def
    by blast+

  show "¬ P_eq_NP"
  proof
    assume eq: "P_eq_NP"

    have inP_SUBSETSUM: "SUBSETSUM_lang enc0 ∈ 𝒫"
      using NP_enc0 eq
      unfolding P_eq_NP_def
      by simp

    from bridge_P[unfolded P_impl_CL_SubsetSum_Solver_def] inP_SUBSETSUM
    obtain M q0 where
      solver: "CL_SubsetSum_Solver M q0 encB"
      and poly: "polytime_CL_machine M encB"
      by blast

    from all_LR_read solver poly
    have adm: "admits_LR_read_TM_Derived M q0 encB"
      by blast

    from adm obtain isL candL_of_pos candR_of_pos where lr:
      "LR_Read_TM_Derived M q0 encB isL candL_of_pos candR_of_pos"
      unfolding admits_LR_read_TM_Derived_def
      by blast

    interpret LR: LR_Read_TM_Derived M q0 encB isL candL_of_pos candR_of_pos
      by (rule lr)

    (* unpack polytime bound *)
    from poly obtain c d where
      cpos: "c > 0"
      and bound_all:
        "∀as s. steps_CL M (encB as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d))"
      unfolding polytime_CL_machine_def
      by blast

    (* exp beats poly ceiling *)
    obtain N where Hexp:
      "∀n≥N. of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
      using exp_beats_poly_ceiling_strict_TM[OF cpos]
      by blast

    (* choose a distinct-subset-sums instance of length N *)
    obtain as where len_as: "length as = N" and dist_as: "distinct_subset_sums as"
      using exists_distinct_family_TM[rule_format, of N]
      by blast
    let ?s = "0::int"

    have ub_nat:
      "steps_CL M (encB as ?s) ≤ nat (ceiling (c * (real (length as)) ^ d))"
      using bound_all by blast

    have ub_int:
      "real (steps_CL M (encB as ?s))
        ≤ of_int (ceiling (c * (real (length as)) ^ d))"
    proof -
      let ?y = "c * (real (length as)) ^ d"

      have y_nonneg: "0 ≤ ?y"
        using cpos by simp

      have ceil_nonneg: "0 ≤ ceiling (c * (real (length as)) ^ d)"
      proof -
        let ?y = "c * (real (length as)) ^ d"

        have y_nonneg: "0 ≤ ?y"
          using cpos by simp

        have y_le: "?y ≤ (of_int (ceiling ?y) :: real)"
          by (rule le_of_int_ceiling)

        have "0 ≤ (of_int (ceiling ?y) :: real)"
          using y_nonneg y_le by linarith

        thus ?thesis
          by simp
      qed

      from ub_nat have
        "real (steps_CL M (encB as ?s)) ≤ real (nat (ceiling ?y))"
        by simp
      also have "... = of_int (ceiling ?y)"
        using ceil_nonneg by simp
      finally show ?thesis
        by simp
    qed


    have n_def: "N = length as"
      by (simp add: len_as)

    have lb:
      "2 * sqrt ((2::real) ^ N) ≤ real (steps_CL M (encB as ?s))"
      using LR.subset_sum_sqrt_lower_bound_CL[OF n_def dist_as] .

    have lb_len:
      "2 * sqrt ((2::real) ^ (length as)) ≤ real (steps_CL M (encB as ?s))"
      using lb by (simp add: len_as)

    have le_poly:
      "2 * sqrt ((2::real) ^ (length as))
         ≤ of_int (ceiling (c * (real (length as)) ^ d))"
      using lb_len ub_int by linarith

    have strict:
      "of_int (ceiling (c * (real (length as)) ^ d))
         < 2 * sqrt ((2::real) ^ (length as))"
    proof -
      have "length as ≥ N" by (simp add: len_as)
      from Hexp[rule_format, OF this] show ?thesis .
    qed

    show False
      using le_poly strict by linarith
  qed
qed

section ‹Final packaged theorem›

text ‹
The final result can now be stated in a single packaged form.

If the LR-read hypothesis holds for the instance encoding \verb|enc0|, and
if SUBSET--SUM admits an NP verifier with respect to \verb|enc0|, then
\[
  \neg (\mathcal{P} = \mathcal{NP}).
\]

Equivalently, the development shows that the following assumptions are
jointly inconsistent:

\begin{itemize}
\item SUBSET--SUM lies in \(\mathcal{NP}\) (witnessed by a verifier);
\item every polynomial-time Cook--Levin solver for SUBSET--SUM admits an
      LR-read presentation; and
\item \(\mathcal{P} = \mathcal{NP}\).
\end{itemize}

Thus the entire argument isolates a single remaining informational question:
whether polynomial-time SUBSET--SUM solvers must satisfy the LR-read
information-flow condition.
›

theorem P_neq_NP_under_LR_read:
  fixes enc0 :: "int list ⇒ int ⇒ string"
    and encB :: "int list ⇒ int ⇒ bool list"
  assumes LR_read: "LR_read_hypothesis enc0 encB"
  assumes Ver: "SS_Verifier_NP k G Vtm p T fverify enc0 enc_cert"
  shows "¬ P_eq_NP"
proof -
  have NP_enc0: "SUBSETSUM_lang enc0 ∈ \<N>\<P>"
    using SUBSETSUM_in_NP_from_verifier[OF Ver] .
  show "¬ P_eq_NP"
    using P_neq_NP_if_LR_read_hypothesis[OF LR_read NP_enc0] .
qed

end
