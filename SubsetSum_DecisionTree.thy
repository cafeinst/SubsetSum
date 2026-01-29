theory SubsetSum_DecisionTree
  imports "HOL-Real_Asymp.Real_Asymp"
      "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
begin

section \<open>Overview\<close>

text \<open>
SUBSET--SUM is the decision problem: given an integer list
$as = [a_0,\dots,a_{n-1}]$ and an integer target $s$, decide whether there exists
a $0/1$ vector $xs \in \{0,1\}^n$ such that
\[
  \sum_{i<n} a_i \cdot xs_i = s .
\]

This theory develops an abstract information-theoretic lower bound for
SUBSET--SUM. The argument does not depend on any particular *implementation* of a 
solver. Instead, it is carried out in an abstract *information-access model* (the
reader model) that postulates a single information-flow axiom about how a
solver distinguishes numerical candidates arising from a canonical split of
the verification equation.

The key observation is that a solver never sees the hidden solution vector $xs$.
Instead, from the solver's point of view, many different subset choices remain
possible for the same instance $(as,s)$.

To make this precise, we consider a canonical way of splitting the verification
equation into a ``left'' part and a ``right'' part. For a split position $k \le n$,
the left side depends only on the first $k$ choices, and the right side depends
on the remaining $n-k$ choices. Each side can therefore take on many different
\emph{numerical values}, depending on the hidden subset.

We formalise these families of values using the canonical split function
\verb|e_k| and its induced value sets \verb|LHS| and \verb|RHS|. Intuitively:

\begin{itemize}
\item \verb|LHS| contains all possible left partial sums,
\item \verb|RHS| contains all possible right residual values.
\end{itemize}

On instances with \emph{distinct subset sums}---that is, where different $0/1$
vectors always produce different total sums---these sets attain their maximal
sizes:
\[
  \mathrm{card}(\mathrm{LHS}(e_k(as,s,k),n)) = 2^k,\qquad
  \mathrm{card}(\mathrm{RHS}(e_k(as,s,k),n)) = 2^{\,n-k}.
\]

Applying the AM--GM inequality to $\mathrm{card}(\mathrm{LHS})$ and
$\mathrm{card}(\mathrm{RHS})$ yields
\[
  \mathrm{card}(\mathrm{LHS}) + \mathrm{card}(\mathrm{RHS})
  \ge 2 \sqrt{2^n}.
\]

To turn this counting fact into a time lower bound, we assume a single abstract
\emph{reader axiom}: on each distinct-subset-sums instance, there exists some
split $k$ at which the solver must effectively distinguish all canonical
candidates, and each such distinction costs at least one unit of work.

Under this assumption, any solver must perform $\Omega(\sqrt{2^n})$ work on 
these instances.

The rest of the file has four main parts:

\begin{enumerate}
\item Bitvectors and the canonical split sets \verb|e_k|, \verb|LHS|, and \verb|RHS|.
\item Distinct-subset-sums instances, including the powers-of-two family.
\item The counting/AM--GM lower bound under the reader axiom
      (locale \verb|SubsetSum_Reader_Model|).
\item A decision-tree semantics that instantiates the locale, followed by a
      polynomial-encoding/time contradiction wrapper.
\end{enumerate}
\<close>

section \<open>0/1 integer vectors and bounded sums\<close>

text \<open>
We encode a \emph{choice} of subset by a $0/1$ vector of fixed length.

For a list \verb|as :: int list| and a $0/1$ vector \verb|xs :: int list|,
the subset-sum value is the dot product restricted to a set of indices.
This is implemented by \verb|sum_as_on|, which sums the products
\verb|as ! i * xs ! i| over an index set $I$.
\<close>

(* A bitvector of length k is a list of k elements from {0,1}. *)
definition bitvec :: "nat \<Rightarrow> int list set" where
  "bitvec k = {xs. length xs = k \<and> set xs \<subseteq> {0::int, 1}}"

(* Basic lemmas about bitvectors: cardinality, finiteness, etc. *)
lemma bitvec_0[simp]: "bitvec 0 = {[]}"
  unfolding bitvec_def by auto

lemma sum_pow2_int: "(\<Sum> i<k. (2::int)^i) = 2^k - 1"
  by (induction k) simp_all

(* Bitvectors of length n+1 are exactly {0::xs} \<union> {1::xs} where xs has length n. *)
lemma bitvec_Suc_partition:
  "bitvec (Suc n) =
    {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
proof (rule subset_antisym)
  show "bitvec (Suc n) \<subseteq> {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
  proof
    fix x assume x: "x \<in> bitvec (Suc n)"
    then obtain h t where HT: "x = h # t" and len: "length t = n"
      and sub: "set t \<subseteq> {0,1}"
      by (cases x) (auto simp: bitvec_def)
    from x HT have h01: "h = 0 \<or> h = 1"
      by (auto simp: bitvec_def)
    have t_in: "t \<in> bitvec n" using len sub by (simp add: bitvec_def)
    show "x \<in> {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
      using HT h01 t_in by auto
  qed
  next
  show "{0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n} \<subseteq> bitvec (Suc n)"
  proof
    fix x assume "x \<in> {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
    then show "x \<in> bitvec (Suc n)"
      by (auto simp: bitvec_def)
  qed
qed

(* The two halves of the partition are disjoint. *)
lemma bitvec_Suc_disjoint:
  "{0 # xs | xs. xs \<in> bitvec n} \<inter> {1 # xs | xs. xs \<in> bitvec n} = {}"
  by auto

(* There are exactly 2^n bitvectors of length n. *)
lemma finite_bitvec[simp]: "finite (bitvec n)"
proof (induction n)
  case 0
  show ?case by (simp add: bitvec_def)
next
  case (Suc n)
  have part: "bitvec (Suc n) =
     {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
    by (rule bitvec_Suc_partition)
  have eq0: "{0 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 0 # xs) ` bitvec n" by auto
  have eq1: "{1 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 1 # xs) ` bitvec n" by auto
  have fin0: "finite {0 # xs | xs. xs \<in> bitvec n}"
    unfolding eq0 by (intro finite_imageI Suc.IH)
  have fin1: "finite {1 # xs | xs. xs \<in> bitvec n}"
    unfolding eq1 by (intro finite_imageI Suc.IH)
  show ?case by (simp add: part fin0 fin1)
qed

lemma card_bitvec: "card (bitvec n) = 2 ^ n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have part: "bitvec (Suc n) =
       {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
    by (rule bitvec_Suc_partition)
  have disj: "{0 # xs | xs. xs \<in> bitvec n} \<inter> {1 # xs | xs. xs \<in> bitvec n} = {}"
    by (rule bitvec_Suc_disjoint)
  have eq0: "{0 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 0 # xs) ` bitvec n" by auto
  have eq1: "{1 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 1 # xs) ` bitvec n" by auto
  have "card (bitvec (Suc n))
     = card {0 # xs | xs. xs \<in> bitvec n} + card {1 # xs | xs. xs \<in> bitvec n}"
    by (simp add: part disj card_Un_disjoint)
  also have "... = card ((\<lambda>xs. 0 # xs) ` bitvec n) + card ((\<lambda>xs. 1 # xs) ` bitvec n)"
    by (simp add: eq0 eq1)
  also have "... = card (bitvec n) + card (bitvec n)"
    by (simp add: card_image)
  also have "... = 2 ^ n + 2 ^ n" using Suc.IH by simp
  also have "... = 2 ^ Suc n" by simp
  finally show ?case .  
qed

section \<open>The split function \<open>e_k\<close> and the LHS/RHS sets\<close>

text \<open>
We split a SUBSET--SUM instance at position $k$:

\begin{itemize}
\item the first $k$ bits of $xs$ determine the left partial sum $L$,
\item the remaining bits determine the right residual value
      $R = s - (\text{suffix sum})$.
\end{itemize}

Thus $e_k(as,s,k,xs) = (L,R)$. The sets \verb|LHS| and \verb|RHS| collect all
values of $L$ and $R$ as $xs$ ranges over \verb|bitvec n|.
\<close>

(* Sum of as[i] * xs[i] over index set I. *)
definition sum_as_on :: "int list \<Rightarrow> nat set \<Rightarrow> int list \<Rightarrow> int" where
  "sum_as_on as I xs = (\<Sum> i \<in> I. as ! i * xs ! i)"

(* Left-hand side: sum over first k indices. *)
definition lhs_of :: "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int" where
  "lhs_of as k xs = sum_as_on as {0..<k} xs"

(* Right-hand side: target s minus sum over indices k..n. *)
definition rhs_of :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int" where
  "rhs_of as k s xs = s - sum_as_on as {k..<length as} xs"

subsection \<open>Canonical split family\<close>
text \<open>
The SUBSET--SUM verification equation can be written in many equivalent ways.
For example, one may group variables differently, rearrange the order of the
$0/1$ choices, or apply other injective reparametrisations. All such rewritings 
preserve correctness, differing only in \emph{how} the same underlying numerical 
possibilities are presented to the solver.

In this formal development we do not range over all possible reparametrisations.
Instead, we fix a single, canonical family of split equations, indexed by a
split position $k$. We therefore make no claim that *every* solver must expose 
its progress through this canonical family; the canonical family is used only as 
a fixed reference presentation for the assumed reader-style information-flow 
condition.

Intuitively, the split equation has the form
\[
  e_k(as,s,k,xs) =
  (\text{sum of selected entries with index } < k,\;
   \text{residual value contributed by indices } \ge k).
\]

For each split position $k$, the induced sets
\verb|LHS (e_k ...)| and \verb|RHS (e_k ...)| collect \emph{all numerical values}
that the left-hand and right-hand sides can assume under different hidden
$0/1$ choices consistent with the same instance $(as,s)$.

This canonical split family is sufficient *for the present lower-bound
argument* because the reader axiom we assume is stated in terms of the
numerical candidate sets induced by these canonical splits.  We do not claim
that every solver, or every encoding-level model, must expose its information
flow through this particular family; rather, we analyse solvers that admit an
information-access presentation of this form.

Fixing a canonical split family therefore provides a uniform and transparent way
to expose the intrinsic information that any solver must acquire, while avoiding
an unnecessary proliferation of equivalent cases.
\<close>

definition e_k :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int \<times> int" where
  "e_k as s k xs = (lhs_of as k xs, rhs_of as k s xs)"

(* LHS: the set of all possible left-hand-side values. *)
definition LHS :: "(int list \<Rightarrow> int \<times> int) \<Rightarrow> nat \<Rightarrow> int set" where
  "LHS e n = {fst (e xs) | xs. xs \<in> bitvec n}"

(* RHS: the set of all possible right-hand-side values. *)
definition RHS :: "(int list \<Rightarrow> int \<times> int) \<Rightarrow> nat \<Rightarrow> int set" where
  "RHS e n = {snd (e xs) | xs. xs \<in> bitvec n}"


section \<open>Distinct subset sums (full length)\<close>

text \<open>
A weight list $as$ has \emph{distinct subset sums} if different $0/1$ vectors
of the same length always produce different total sums. This is a very strong
injectivity property: the map
\[
  xs \longmapsto \sum_{i<\mathrm{length}(as)} as_i \cdot xs_i
\]
is injective on the set \verb|bitvec (length as)|.

In this setting, injectivity is what forces the canonical split images to have
their maximal possible cardinalities.
\<close>

definition distinct_subset_sums :: "int list \<Rightarrow> bool" where
  "distinct_subset_sums as \<equiv>
    (\<forall>xs\<in>bitvec (length as). \<forall>ys\<in>bitvec (length as).
       xs \<noteq> ys \<longrightarrow> (\<Sum> i < length as. as ! i * xs ! i) \<noteq> 
       (\<Sum> i < length as. as ! i * ys ! i))"

section \<open>Padding lemmas for prefix/suffix reasoning\<close>

text \<open>
The following lemmas are technical devices used to relate sums over prefixes
and suffixes to sums over the full $0/1$ vector.

Conceptually:

\begin{itemize}
\item To realise any left-hand-side value, we pad the right-hand part of the
      vector with zeros. This shows that the values in \verb|LHS| can be
      generated from arbitrary prefixes.

\item To realise any right-hand-side value, we pad the left-hand part with
      zeros. This shows that the values in \verb|RHS| can be generated from
      arbitrary suffixes.
\end{itemize}

The padding lemmas guarantee that these zero extensions behave exactly as
expected under the subset-sum map.
\<close>

lemma pad_suffix_zeros_in_bitvec:
  assumes "p \<in> bitvec k" "n \<ge> k"
  shows "p @ replicate (n - k) 0 \<in> bitvec n"
    using assms by (auto simp: bitvec_def)

lemma pad_prefix_zeros_in_bitvec:
  assumes "q \<in> bitvec (n - k)" "k \<le> n"
  shows "(replicate k 0) @ q \<in> bitvec n"
    using assms by (auto simp: bitvec_def)

lemma drop_in_bitvec:
  assumes "xs \<in> bitvec n" "k \<le> n"
  shows   "drop k xs \<in> bitvec (n - k)"
proof -
  have len: "length xs = n" and xs01: "set xs \<subseteq> {0,1}"
    using assms(1) by (auto simp: bitvec_def)
  have "length (drop k xs) = n - k"
    using assms(2) len by simp
  moreover have "set (drop k xs) \<subseteq> {0,1}"
    using xs01 by (auto dest: in_set_dropD)
  ultimately show ?thesis by (simp add: bitvec_def)
qed

lemma sum_as_on_prefix_pad:
  assumes "xs \<in> bitvec n" "k \<le> n"
  shows "sum_as_on as {0..<k} xs =
        sum_as_on as {0..<k} (take k xs @ replicate (n - k) 0)"
    using assms
    by (simp add: sum_as_on_def bitvec_def atLeast0LessThan less_diff_conv nth_append min_def)

lemma sum_reindex_add:
  fixes k n :: nat
  shows "(\<Sum> i \<in> {k..<n}. g i) = (\<Sum> j \<in> {0..<n - k}. g (k + j))"
proof -
  have inj: "inj_on ((+) k) {0..<n - k}" by auto
  have E: "sum g ((+) k ` {0..<n - k}) = sum (g \<circ> ((+) k)) {0..<n - k}"
    by (rule sum.reindex[OF inj])
  have F: "sum (g \<circ> ((+) k)) {0..<n - k} = (\<Sum> j = 0..<n - k. g (k + j))"
    by (simp add: o_def)
  from E F show ?thesis by (metis sum.atLeastLessThan_shift_0)
qed

lemma sum_as_on_suffix_pad_shift:
  assumes lenq: "length q = n - k" and kn: "k \<le> n"
  shows
    "sum_as_on as {k..<n} ((replicate k 0) @ q)
      = (\<Sum> j \<in> {0..<n - k}. as ! (k + j) * q ! j)"
proof -
  have A: "\<And>i. i \<in> {k..<n} \<Longrightarrow> ((replicate k 0) @ q) ! i = q ! (i - k)"
    using lenq by (auto simp: nth_append)

  have "sum_as_on as {k..<n} ((replicate k 0) @ q)
       = (\<Sum> i \<in> {k..<n}. as ! i * ((replicate k 0) @ q) ! i)"
    by (simp add: sum_as_on_def)
  also have "... = (\<Sum> i \<in> {k..<n}. as ! i * q ! (i - k))"
    by (simp add: A)
  also have "... = (\<Sum> j \<in> {0..<n - k}. as ! (k + j) * q ! ((k + j) - k))"
    by (subst sum_reindex_add) simp
  also have "... = (\<Sum> j \<in> {0..<n - k}. as ! (k + j) * q ! j)"
    by simp
  finally show ?thesis .  
qed

lemma sum_as_on_suffix_drop_shift:
  assumes xs: "xs \<in> bitvec n" and kn: "k \<le> n"
  shows "sum_as_on as {k..<n} xs
      = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * (drop k xs) ! j)"
proof -
  have lenxs: "length xs = n" using xs by (simp add: bitvec_def)
  have "sum_as_on as {k..<n} xs = (\<Sum> i\<in>{k..<n}. as ! i * xs ! i)"
    by (simp add: sum_as_on_def)
  also have "... = (\<Sum> i\<in>{k..<n}. as ! i * (drop k xs) ! (i - k))"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {k..<n}"
    with lenxs kn show "as ! i * xs ! i = as ! i * (drop k xs) ! (i - k)"
      by simp
  qed
  also have "... = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * (drop k xs) ! j)"
    by (subst sum_reindex_add) simp
  finally show ?thesis .  
qed

lemma take_in_bitvec:
  assumes "xs \<in> bitvec n" "k \<le> n"
  shows   "take k xs \<in> bitvec k"
proof -
  have "length (take k xs) = k" using assms by (simp add: bitvec_def)
  moreover have "set (take k xs) \<subseteq> {0,1}"
    using assms by (auto simp: bitvec_def dest!: in_set_takeD)
  ultimately show ?thesis by (simp add: bitvec_def)
qed

(* padded tail entries are 0 for indices i \<in> {k..<n}. *)
lemma padded_tail_zero:
  assumes "length p = k" and "i \<in> {k..<n}"
  shows   "(p @ replicate (n - k) (0::int)) ! i = 0"
proof -
  have ik: "k \<le> i" and in_lt: "i < n" using assms(2) by auto
  have "(p @ replicate (n - k) (0::int)) ! i = (replicate (n - k) (0::int)) ! (i - k)"
    using assms(1) ik by (simp add: nth_append)
  moreover have "i - k < n - k" using in_lt ik by arith
  ultimately show ?thesis by simp  
qed

section \<open>Main counting theorem\<close>

text \<open>
We now prove the main combinatorial counting result,
denoted \verb|subset_sum_sqrt_lower_bound|.

Assume that the weight list has distinct subset sums, and consider a split
at position $k$. Then:

\begin{itemize}
\item the set of left-hand values has cardinality $2^k$, and
\item the set of right-hand values has cardinality $2^{\,n-k}$.
\end{itemize}

Consequently, the product of these cardinalities is exactly $2^n$.

The proof is based on padding arguments: by extending prefixes or suffixes
with zeros, and using the global injectivity of the full subset-sum map,
we obtain injectivity of the induced maps on prefixes and suffixes. This
forces the canonical split images to attain their maximal possible sizes.
\<close>

(* THEOREM: If weights have distinct subset sums, then |LHS| = 2^k. *)
lemma card_LHS_e_k:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n"
    and distinct: "distinct_subset_sums as"
  shows "card (LHS (e_k as s k) n) = 2 ^ k"
proof -
  let ?pref = "bitvec k"
  define f where "f p = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))" for p

(* Every LHS value arises from some prefix p. *)
  have LHS_subset: "LHS (e_k as s k) n \<subseteq> f ` ?pref"
  proof
    fix v assume "v \<in> LHS (e_k as s k) n"
    then obtain xs where xs: "xs \<in> bitvec n" and v: "v = fst (e_k as s k xs)"
      by (auto simp: LHS_def)
    define p where "p = take k xs"
    have p_in: "p \<in> ?pref" using xs k_le by (simp add: p_def take_in_bitvec)
    have "v = sum_as_on as {0..<k} xs"
      by (simp add: v e_k_def lhs_of_def sum_as_on_def)
    also have "... = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))"
      using xs k_le by (simp add: p_def sum_as_on_prefix_pad n_def)
    finally have "v = f p" by (simp add: f_def)
    thus "v \<in> f ` ?pref" using p_in by blast
  qed

(* Every prefix p gives a realizable LHS value. *)
  have subset_LHS: "f ` ?pref \<subseteq> LHS (e_k as s k) n"
  proof
    fix v assume "v \<in> f ` ?pref"
    then obtain p where p: "p \<in> ?pref" and v: "v = f p" by blast
    have xs_in: "p @ replicate (n - k) (0::int) \<in> bitvec n"
      using p k_le by (rule pad_suffix_zeros_in_bitvec)
    have "v = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))"
      by (simp add: v f_def)
    hence "v = fst (e_k as s k (p @ replicate (n - k) (0::int)))"
      by (simp add: e_k_def lhs_of_def)
    thus "v \<in> LHS (e_k as s k) n"
      using xs_in by (auto simp: LHS_def)
  qed

  have LHS_eq_img: "LHS (e_k as s k) n = f ` ?pref"
    using LHS_subset subset_LHS by blast

(* Injectivity on prefixes by padding with zeros and using distinct sums. *)
  have inj_f: "inj_on f ?pref"
  proof (rule inj_onI)
    fix p1 p2 assume p1: "p1 \<in> ?pref" and p2: "p2 \<in> ?pref" and eq: "f p1 = f p2"
    have lenp1: "length p1 = k" using p1 by (simp add: bitvec_def)
    have lenp2: "length p2 = k" using p2 by (simp add: bitvec_def)

    have pref_eq:
      "sum_as_on as {0..<k} (p1 @ replicate (n - k) (0::int))
      = sum_as_on as {0..<k} (p2 @ replicate (n - k) (0::int))"
      using eq by (simp add: f_def)

(* --- split the big sums and finish the equality --- *)
    let ?x1 = "p1 @ replicate (n - k) (0::int)"
    let ?x2 = "p2 @ replicate (n - k) (0::int)"
    let ?F1 = "(\<lambda>i. as ! i * ?x1 ! i)"
    let ?F2 = "(\<lambda>i. as ! i * ?x2 ! i)"

    have fin1: "finite ({0..<k}::nat set)" by simp
    have fin2: "finite ({k..<n}::nat set)" by simp
    have disj: "{0..<k} \<inter> {k..<n} = ({}::nat set)" by auto
    have un:   "{0..<k} \<union> {k..<n} = {0..<n}" using k_le by auto

    have split1:
      "(\<Sum>i\<in>{0..<n}. ?F1 i)
      = (\<Sum>i\<in>{0..<k}. ?F1 i) + (\<Sum>i\<in>{k..<n}. ?F1 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

    have split2:
      "(\<Sum>i\<in>{0..<n}. ?F2 i)
       = (\<Sum>i\<in>{0..<k}. ?F2 i) + (\<Sum>i\<in>{k..<n}. ?F2 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

(* tails are zero because padded tail entries are 0 *)
    have tail1:
      "(\<Sum>i\<in>{k..<n}. as ! i * (p1 @ replicate (n - k) (0::int)) ! i) = 0"
      by (rule sum.neutral, intro ballI, simp add: padded_tail_zero[OF lenp1])

    have tail2:
      "(\<Sum>i\<in>{k..<n}. as ! i * (p2 @ replicate (n - k) (0::int)) ! i) = 0"
      by (rule sum.neutral, intro ballI, simp add: padded_tail_zero[OF lenp2])

(* prefixes equal via your pref_eq *)
    have pref1: "(\<Sum>i\<in>{0..<k}. ?F1 i) = sum_as_on as {0..<k} ?x1"
      by (simp add: sum_as_on_def)
    have pref2: "(\<Sum>i\<in>{0..<k}. ?F2 i) = sum_as_on as {0..<k} ?x2"
      by (simp add: sum_as_on_def)

    have full_eq_set:
      "(\<Sum>i\<in>{0..<n}. ?F1 i) = (\<Sum>i\<in>{0..<n}. ?F2 i)"
      using pref_eq tail1 tail2 by (simp add: split1 split2 pref1 pref2)

(* if you need the < n binder form *)
    have full_eq:
      "(\<Sum> i < n. as ! i * ?x1 ! i) = (\<Sum> i < n. as ! i * ?x2 ! i)"
      using full_eq_set by (simp add: atLeast0LessThan)

    have xs1: "?x1 \<in> bitvec n" using p1 k_le by (rule pad_suffix_zeros_in_bitvec)
    have xs2: "?x2 \<in> bitvec n" using p2 k_le by (rule pad_suffix_zeros_in_bitvec)

    from full_eq xs1 xs2 distinct n_def
    have "?x1 = ?x2"
      unfolding distinct_subset_sums_def by auto
    thus "p1 = p2" by simp
  qed

  have "card (LHS (e_k as s k) n) = card (f ` ?pref)"
    by (simp add: LHS_eq_img)
  also have "... = card ?pref" by (rule card_image; use inj_f in auto)
  also have "... = 2 ^ k" by (rule card_bitvec)
  finally show ?thesis .
qed

(* THEOREM: If weights have distinct subset sums, then |RHS| = 2^(n-k). *)
lemma card_RHS_e_k:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n"
    and distinct: "distinct_subset_sums as"
  shows "card (RHS (e_k as s k) n) = 2 ^ (n - k)"
proof -
  let ?suf = "bitvec (n - k)"
  define g where "g q = s - sum_as_on as {k..<n} ((replicate k (0::int)) @ q)" for q

(* Every RHS value arises from some suffix q. *)
  have RHS_subset: "RHS (e_k as s k) n \<subseteq> g ` ?suf"
  proof
    fix v assume "v \<in> RHS (e_k as s k) n"
    then obtain xs where xs: "xs \<in> bitvec n" and vdef: "v = snd (e_k as s k xs)"
      by (auto simp: RHS_def)

    define q where "q = drop k xs"
    have q_in: "q \<in> bitvec (n - k)"
      by (simp add: q_def drop_in_bitvec[OF xs k_le])
    have q_len: "length q = n - k"
      using q_in by (simp add: bitvec_def)

(* rewrite the xs-tail and the padded-tail to the same shifted sum *)
    have xs_tail:
      "sum_as_on as {k..<n} xs
      = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * q ! j)"
      by (simp add: q_def sum_as_on_suffix_drop_shift[OF xs k_le])
    have pad_tail:
      "sum_as_on as {k..<n} ((replicate k (0::int)) @ q)
      = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * q ! j)"
      using sum_as_on_suffix_pad_shift[OF q_len k_le] by simp

    have "v = s - sum_as_on as {k..<n} xs"
      by (simp add: vdef e_k_def rhs_of_def sum_as_on_def n_def)
    also have "... = s - (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * q ! j)"
      by (simp add: xs_tail)
    also have "... = s - sum_as_on as {k..<n} ((replicate k 0) @ q)"
      by (simp add: pad_tail)
    finally have "v = g q" by (simp add: g_def)

    thus "v \<in> g ` ?suf" using q_in by blast
  qed

(* Every suffix q gives a realizable RHS value. *)
  have subset_RHS: "g ` ?suf \<subseteq> RHS (e_k as s k) n"
  proof
    fix v assume "v \<in> g ` ?suf"
    then obtain q where q: "q \<in> ?suf" and v: "v = g q" by blast
    have xs_in: "(replicate k (0::int)) @ q \<in> bitvec n"
      using q k_le by (rule pad_prefix_zeros_in_bitvec)
    have "v = s - sum_as_on as {k..<n} ((replicate k (0::int)) @ q)"
      by (simp add: v g_def)
    hence "v = snd (e_k as s k ((replicate k (0::int)) @ q))"
      by (simp add: e_k_def rhs_of_def sum_as_on_def n_def)
    thus "v \<in> RHS (e_k as s k) n"
      using xs_in by (auto simp: RHS_def)
  qed

  have RHS_eq_img: "RHS (e_k as s k) n = g ` ?suf"
    using RHS_subset subset_RHS by blast

(* Injectivity on suffixes by padding with zeros and using distinct sums. *)
  have inj_g: "inj_on g ?suf"
  proof (rule inj_onI)
    fix q1 q2 assume q1: "q1 \<in> ?suf" and q2: "q2 \<in> ?suf" and eq: "g q1 = g q2"
    have xs1: "(replicate k (0::int)) @ q1 \<in> bitvec n"
      using q1 k_le by (rule pad_prefix_zeros_in_bitvec)
    have xs2: "(replicate k (0::int)) @ q2 \<in> bitvec n"
      using q2 k_le by (rule pad_prefix_zeros_in_bitvec)

(* from g q1 = g q2, tails are equal *)
    from eq have tails_eq:
      "sum_as_on as {k..<n} ((replicate k 0) @ q1)
      = sum_as_on as {k..<n} ((replicate k 0) @ q2)"
      by (simp add: g_def)

(* --- turn tail equality into full-sum equality --- *)
    let ?x1 = "(replicate k (0::int)) @ q1"
    let ?x2 = "(replicate k (0::int)) @ q2"
    let ?F1 = "(\<lambda>i. as ! i * ?x1 ! i)"
    let ?F2 = "(\<lambda>i. as ! i * ?x2 ! i)"

    have fin1: "finite ({0..<k}::nat set)" by simp
    have fin2: "finite ({k..<n}::nat set)" by simp
    have disj: "{0..<k} \<inter> {k..<n} = ({}::nat set)" by auto
    have un:   "{0..<k} \<union> {k..<n} = {0..<n}" using k_le by auto

    have split1:
      "(\<Sum>i\<in>{0..<n}. ?F1 i)
      = (\<Sum>i\<in>{0..<k}. ?F1 i) + (\<Sum>i\<in>{k..<n}. ?F1 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)
    have split2:
      "(\<Sum>i\<in>{0..<n}. ?F2 i)
      = (\<Sum>i\<in>{0..<k}. ?F2 i) + (\<Sum>i\<in>{k..<n}. ?F2 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

(* prefixes are 0: the first k entries are the replicated zeros *)
    have pref1: "(\<Sum>i\<in>{0..<k}. ?F1 i) = 0" by (simp add: nth_append)
    have pref2: "(\<Sum>i\<in>{0..<k}. ?F2 i) = 0" by (simp add: nth_append)

(* tails equal, rewrite via sum_as_on_def / n_def *)
    have tails_eq_set:
      "(\<Sum>i\<in>{k..<n}. ?F1 i) = (\<Sum>i\<in>{k..<n}. ?F2 i)"
      using tails_eq by (simp add: sum_as_on_def n_def atLeast0LessThan)

    have full_eq_set:
      "(\<Sum>i\<in>{0..<n}. ?F1 i) = (\<Sum>i\<in>{0..<n}. ?F2 i)"
      by (simp add: split1 split2 pref1 pref2 tails_eq_set)

    have full_eq:
      "(\<Sum> i < n. as ! i * ?x1 ! i) = (\<Sum> i < n. as ! i * ?x2 ! i)"
      using full_eq_set by (simp add: atLeast0LessThan)

(* Make the “distinct subset sums” assumption into an injectivity fact. *)
    have inj_sum:
      "inj_on (\<lambda>xs. (\<Sum>i < n. as ! i * xs ! i)) (bitvec n)"
      using distinct
      unfolding distinct_subset_sums_def n_def
      by (intro inj_onI) (auto simp: atLeast0LessThan)

(* Apply injectivity to the two padded vectors. *)
    have "?x1 = ?x2"
      using inj_sum xs1 xs2 full_eq
      by (force simp: inj_on_def)

(* Cancel the common prefix. *)
    then have "q1 = q2" by simp
    thus "q1 = q2" .
  qed

  have "card (RHS (e_k as s k) n) = card (g ` ?suf)"
    by (simp add: RHS_eq_img)
  also have "... = card ?suf" by (rule card_image; use inj_g in auto)
  also have "... = 2 ^ (n - k)" by (simp add: card_bitvec)
  finally show ?thesis .
qed

(* COROLLARY (subset_sum_sqrt_lower_bound):
  The product |LHS| \<times> |RHS| = 2^n. *)
theorem subset_sum_sqrt_lower_bound_split:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n"
    and distinct: "distinct_subset_sums as"
  shows "card (LHS (e_k as s k) n) * card (RHS (e_k as s k) n) = 2 ^ n"
proof -
  have L: "card (LHS (e_k as s k) n) = 2 ^ k"
    by (rule card_LHS_e_k[OF n_def k_le distinct])
  have R: "card (RHS (e_k as s k) n) = 2 ^ (n - k)"
    by (rule card_RHS_e_k[OF n_def k_le distinct])
  have kn: "k + (n - k) = n" using k_le by simp
  from L R show ?thesis
    by (simp add: power_add[symmetric] kn)
qed

section \<open>AM–GM lower bound\<close>

text \<open>
This section contains the analytic part of the lower-bound argument.

From a product bound on two non-negative quantities we derive a lower bound
on their sum using the arithmetic–geometric mean inequality.

Concretely, if \<open>A \<ge> 0\<close> and \<open>B \<ge> 0\<close> and

  \<open>A * B = 2^n\<close>,

then the AM–GM inequality implies

  \<open>A + B \<ge> 2 * sqrt (2^n)\<close>.

We will apply this inequality to the cardinalities of the canonical split
value sets arising from SUBSET–SUM.
\<close>

text \<open>
In the SUBSET–SUM setting, for a fixed instance \<open>(as, s)\<close> of length \<open>n\<close>
and a split position \<open>k \<le> n\<close>, we define

  \<open>A = card (LHS (e_k as s k) n)\<close>,
  \<open>B = card (RHS (e_k as s k) n)\<close>.

On instances with distinct subset sums, earlier results show that

  \<open>A = 2^k\<close> and \<open>B = 2^(n - k)\<close>,

and hence

  \<open>A * B = 2^n\<close>.
\<close>

text \<open>
Applying the AM–GM inequality to these values yields the uniform lower bound

  \<open>card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)
     \<ge> 2 * sqrt (2^n)\<close>.

This bound is independent of the split position \<open>k\<close>.
It depends only on the instance length \<open>n\<close>.
\<close>

text \<open>
This analytic inequality is the final numerical ingredient in the lower-bound
proof.  In the next section, it is combined with the abstract
information-flow (reader) axiom to obtain a lower bound on the number of
steps required by any solver satisfying the reader assumptions.
\<close>

(* THEOREM: If A \<times> B \<ge> 2^n, then A + B \<ge> 2√(2^n) by AM–GM. *)
lemma lemma_AFP:
  fixes A B :: real and n :: nat
  assumes A0: "A \<ge> 0" and B0: "B \<ge> 0"
    and ABge: "A * B \<ge> (2::real) ^ n"
  shows "A + B \<ge> 2 * sqrt ((2::real) ^ n)"
proof -
(* AM–GM from AFP/Analysis. *)
  have amgm: "2 * sqrt (A * B) \<le> A + B"
    using A0 B0 arithmetic_geometric_mean_binary by force
(* sqrt is monotone on \<real>\<ge>0. *)
  have "sqrt ((2::real) ^ n) \<le> sqrt (A * B)"
    using ABge A0 B0 by simp
  hence "2 * sqrt ((2::real) ^ n) \<le> 2 * sqrt (A * B)" by simp
  with amgm show ?thesis by linarith
qed

corollary lhs_rhs_sum_lower_bound:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n" and distinct: "distinct_subset_sums as"
  shows "real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))
        \<ge> 2 * sqrt ((2::real) ^ n)"
proof -
  have prod_eq_nat:
    "card (LHS (e_k as s k) n) * card (RHS (e_k as s k) n) = 2 ^ n"
    by (rule subset_sum_sqrt_lower_bound_split[OF n_def k_le distinct])

(* same product in \<real>. *)
  have prod_eq_real:
    "real (card (LHS (e_k as s k) n)) * real (card (RHS (e_k as s k) n))
    = (2::real) ^ n"
    using prod_eq_nat
    by (metis numeral_power_eq_of_nat_cancel_iff of_nat_mult)

  have prod_ge:
    "(2::real) ^ n \<le> real (card (LHS (e_k as s k) n)) * real (card (RHS (e_k as s k) n))"
    by (simp add: prod_eq_real)

  have A0: "0 \<le> real (card (LHS (e_k as s k) n))" by simp
  have B0: "0 \<le> real (card (RHS (e_k as s k) n))" by simp

  from lemma_AFP[OF A0 B0 prod_ge]
  show "real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))
     \<ge> 2 * sqrt ((2::real) ^ n)"
    by simp
qed

section \<open>Decision-tree reader model and coverage\<close>

text \<open>
We now introduce a simple decision-tree model that abstracts how a solver
interacts with a SUBSET-SUM instance.

The decision tree is given only the instance \<open>(as, s)\<close>.
It never sees the hidden 0/1 solution vector \<open>xs\<close>.
Instead, it interacts with the instance through two abstract oracles:

  • a left oracle \<open>oL\<close>,
  • a right oracle \<open>oR\<close>.

These oracles answer queries about possible numerical values arising from
the canonical split of the verification equation.
\<close>

text \<open>
Fix a split position \<open>k \<le> length as\<close>.
The canonical split of the SUBSET-SUM equation gives rise to two sets
of integers:

  • \<open>LHS (e_k as s k) (length as)\<close>,
    the set of all possible left partial sums,

  • \<open>RHS (e_k as s k) (length as)\<close>,
    the set of all possible right residual values,

as the hidden vector \<open>xs\<close> ranges over all bit-vectors of the appropriate
length consistent with the instance \<open>(as, s)\<close>.
\<close>

text \<open>
This is an information-level query model.
The decision tree does not query bits of an input encoding.
Each query asks for one bit of information about a candidate value—an abstract oracle 
label—used to distinguish candidates in the adversary argument.

We treat oracle answers abstractly. For our adversary arguments, we track only which 
candidates are queried during the run; unqueried candidates cannot influence the outcome. 
This abstracts away from machine-level details and focuses solely on the information 
that a solver must acquire in order to distinguish competing numerical possibilities.
\<close>

text \<open>
The reader-style model postulates the following information-flow principle:

to decide whether an equality \<open>L = R\<close> can hold, a solver must obtain
sufficient information about both sides of the equation to rule out (or
confirm) candidate matches.  In our formalisation this requirement is
packaged as an explicit coverage axiom.

Fix a split position \<open>k\<close>. Suppose the solver fails to distinguish 
between two distinct values \<open>L1 \<noteq> L2\<close> from the set 
\<open>LHS (e_k as s k) (length as)\<close>. By definition of <open>LHS<close>, 
there exist two distinct prefixes of 0/1-vectors producing these values.

Now fix any suffix (for example, the all-zero suffix) and extend both prefixes with 
this same suffix. The resulting vectors produce identical right-hand values, while their
left-hand values differ.

From the solver's point of view, these two cases are observationally
indistinguishable: all information obtained from the right-hand side is
the same, and the left-hand side has not been distinguished.
However, the existence of a solution to \<open>L = R\<close> may differ between
these cases.
\<close>

text \<open>
This motivates the following *assumed* coverage requirement, which we package
as an axiom in the decision-tree locale:

for instances with distinct subset sums, there exists a split position
\<open>k\<close> at which the solver must effectively distinguish all canonical
left-hand and right-hand candidates.

The decision-tree model below formalises this requirement precisely.
\<close>

text \<open>
In the locale \<open>DT_SubsetSum_Solver\<close> we specialise the decision tree so that:

  • left queries range over exactly the values in
    \<open>LHS (e_k as s k) (length as)\<close>,

  • right queries range over exactly the values in
    \<open>RHS (e_k as s k) (length as)\<close>.

Each query index therefore corresponds to a concrete numerical candidate.
The oracles simply assign Boolean answers to these candidates.
\<close>

text \<open>
The datatype \<open>('iL,'iR) dtr\<close> represents decision trees with three kinds
of nodes:

  • \<open>Leaf b\<close> — terminate and return the Boolean value \<open>b\<close>,

  • \<open>AskL i t0 t1\<close> — query the left oracle about value \<open>i\<close>
    and continue with subtree \<open>t0\<close> or \<open>t1\<close>,

  • \<open>AskR j t0 t1\<close> — query the right oracle about value \<open>j\<close>
    and continue with subtree \<open>t0\<close> or \<open>t1\<close>.
\<close>

text \<open>
For fixed oracles \<open>oL\<close> and \<open>oR\<close> we define:

  • \<open>run oL oR T\<close>, the Boolean output of the tree,

  • \<open>seenL_run oL oR T\<close>, the set of left-hand values queried,

  • \<open>seenR_run oL oR T\<close>, the set of right-hand values queried,

  • \<open>steps_run oL oR T\<close>, the total number of oracle queries.

The key lemma \<open>run_agree_on_seen\<close> formalises the standard adversary
principle for decision trees: if two oracles agree on all values queried during a 
given run of the tree, then replacing one oracle by the other leaves the execution 
invariant — the tree follows the same control path, issues the same queries, and
produces the same output.

Accordingly, modifying oracle answers on candidates that are *not queried along
the actual run* cannot affect that run, provided all answers on the queried
candidates are kept fixed (lemma \<open>run_agree_on_seen\<close>).
\<close>

text \<open>
Finally, lemma \<open>steps_ge_sum_seen\<close> shows that the total number of
distinct values queried on both sides is bounded above by the total
number of steps.

This connects the concrete decision-tree behaviour directly with the
abstract cost measure used in the locale \<open>SubsetSum_Reader_Model\<close>.
\<close>

(* A decision tree that can query left-oracle at indices iL and 
  right-oracle at indices iR. *)
datatype ('iL,'iR) dtr =
  Leaf bool
  | AskL 'iL "('iL,'iR) dtr" "('iL,'iR) dtr"
  | AskR 'iR "('iL,'iR) dtr" "('iL,'iR) dtr"

(* Run the tree with two oracles oL and oR. *)
fun run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> bool" where
  "run oL oR (Leaf b) = b"
  | "run oL oR (AskL i t0 t1) = run oL oR (if oL i then t1 else t0)"
  | "run oL oR (AskR j t0 t1) = run oL oR (if oR j then t1 else t0)"

(* Track which left-indices were queried during the run. *)
fun seenL_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> 'iL set" where
  "seenL_run oL oR (Leaf b) = {}"
  | "seenL_run oL oR (AskL i t0 t1) =
      insert i (seenL_run oL oR (if oL i then t1 else t0))"
  | "seenL_run oL oR (AskR j t0 t1) =
      seenL_run oL oR (if oR j then t1 else t0)"

(* Track which right-indices were queried. *)
fun seenR_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> 'iR set" where
  "seenR_run oL oR (Leaf b) = {}"
  | "seenR_run oL oR (AskL i t0 t1) =
      seenR_run oL oR (if oL i then t1 else t0)"
  | "seenR_run oL oR (AskR j t0 t1) =
      insert j (seenR_run oL oR (if oR j then t1 else t0))"

(* Count the number of queries made. *)
fun steps_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> nat" where
  "steps_run oL oR (Leaf b) = 0"
  | "steps_run oL oR (AskL i t0 t1) =
      Suc (steps_run oL oR (if oL i then t1 else t0))"
  | "steps_run oL oR (AskR j t0 t1) =
      Suc (steps_run oL oR (if oR j then t1 else t0))"

(* Well-formedness: tree only queries from declared index sets. *)
text \<open>
Well-formedness: the tree only queries declared L/R indices.
In this decision-tree model, the query *indices* are not bit positions.
They are the *numerical candidates themselves*:
  - a left query index i :: int represents the candidate value i ∈ LHS(...),
  - a right query index j :: int represents the candidate value j ∈ RHS(...).
Thus \<open>wf_dtr\<close> constrains the tree to ask only about values that 
can arise from the canonical split, not about syntactic positions of an input 
encoding.
\<close>

inductive wf_dtr :: "'iL set \<Rightarrow> 'iR set \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> bool" where
  Leaf[intro!]:  "wf_dtr L R (Leaf b)"
  | AskL[intro!]:  "i \<in> L \<Longrightarrow> wf_dtr L R t0 \<Longrightarrow> wf_dtr L R t1 \<Longrightarrow> wf_dtr L R (AskL i t0 t1)"
  | AskR[intro!]:  "j \<in> R \<Longrightarrow> wf_dtr L R t0 \<Longrightarrow> wf_dtr L R t1 \<Longrightarrow> wf_dtr L R (AskR j t0 t1)"

lemma seenL_subset:
  assumes "wf_dtr L R T" shows "seenL_run oL oR T \<subseteq> L"
  using assms by (induction T) auto

lemma seenR_subset:
  assumes "wf_dtr L R T" shows "seenR_run oL oR T \<subseteq> R"
  using assms by (induction T) auto

(* tiny helpers for the chosen branch *)
lemma seenL_sub_AskL:
  "seenL_run oL oR (if oL i then t1 else t0) \<subseteq> seenL_run oL oR (AskL i t0 t1)"
  by (cases "oL i") auto

lemma seenR_eq_AskL:
"seenR_run oL oR (if oL i then t1 else t0) = seenR_run oL oR (AskL i t0 t1)"
by (cases "oL i") auto

lemma seenR_sub_AskR:
  "seenR_run oL oR (if oR j then t1 else t0) \<subseteq> seenR_run oL oR (AskR j t0 t1)"
  by (cases "oR j") auto

lemma seenL_eq_AskR:
  "seenL_run oL oR (if oR j then t1 else t0) = seenL_run oL oR (AskR j t0 t1)"
  by (cases "oR j") auto

(* evaluation/seen simplifiers *)
lemmas run_simps   = run.simps
lemmas seenL_simps = seenL_run.simps
lemmas seenR_simps = seenR_run.simps

lemma run_Leaf[simp]:  "run oL oR (Leaf b) = b" by simp
lemma seenL_Leaf[simp]: "seenL_run oL oR (Leaf b) = {}" by simp
lemma seenR_Leaf[simp]: "seenR_run oL oR (Leaf b) = {}" by simp

(* single-path seen-sets are finite *)
lemma finite_seenL_run[simp]: "finite (seenL_run oL oR T)"
  by (induction T arbitrary: oL oR) auto
lemma finite_seenR_run[simp]: "finite (seenR_run oL oR T)"
  by (induction T arbitrary: oL oR) auto

(* card(seenL) \<le> steps and symmetrically for R: each step can introduce
  at most one new queried index. *)
lemma card_seenL_le_steps: "card (seenL_run oL oR T) \<le> steps_run oL oR T"
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  let ?S = "seenL_run oL oR (if oL i then t1 else t0)"
  have IH0: "card (seenL_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskL.IH(1))
  have IH1: "card (seenL_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskL.IH(2))
  have br: "card ?S \<le> steps_run oL oR (if oL i then t1 else t0)"
    by (cases "oL i"; simp add: IH0 IH1)
  have fin: "finite ?S"
    by simp
  have "card (seenL_run oL oR (AskL i t0 t1)) = card (insert i ?S)" by simp
  also have "... \<le> Suc (card ?S)" using fin by (simp add: card_insert_if)
  also have "... \<le> Suc (steps_run oL oR (if oL i then t1 else t0))"
    using br by simp
  also have "... = steps_run oL oR (AskL i t0 t1)" by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  have IH0: "card (seenL_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskR.IH(1))
  have IH1: "card (seenL_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskR.IH(2))
  have br: "card (seenL_run oL oR (if oR j then t1 else t0))
           \<le> steps_run oL oR (if oR j then t1 else t0)"
    by (cases "oR j"; simp add: IH0 IH1)
  have "card (seenL_run oL oR (AskR j t0 t1))
       = card (seenL_run oL oR (if oR j then t1 else t0))" by simp
  also have "... \<le> steps_run oL oR (if oR j then t1 else t0)" using br .
  also have "... \<le> Suc (steps_run oL oR (if oR j then t1 else t0))"
    by (simp add: le_SucI)
  also have "... = steps_run oL oR (AskR j t0 t1)" by simp
  finally show ?case .
qed

lemma card_seenR_le_steps: "card (seenR_run oL oR T) \<le> steps_run oL oR T"
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  have IH0: "card (seenR_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskL.IH(1))
  have IH1: "card (seenR_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskL.IH(2))
  have br: "card (seenR_run oL oR (if oL i then t1 else t0))
           \<le> steps_run oL oR (if oL i then t1 else t0)"
    by (cases "oL i"; simp add: IH0 IH1)
  have "card (seenR_run oL oR (AskL i t0 t1))
       = card (seenR_run oL oR (if oL i then t1 else t0))" by simp
  also have "... \<le> steps_run oL oR (if oL i then t1 else t0)" using br .
  also have "... \<le> Suc (steps_run oL oR (if oL i then t1 else t0))"
    by (simp add: le_SucI)
  also have "... = steps_run oL oR (AskL i t0 t1)" by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  let ?S = "seenR_run oL oR (if oR j then t1 else t0)"
  have IH0: "card (seenR_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskR.IH(1))
  have IH1: "card (seenR_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskR.IH(2))
  have br: "card ?S \<le> steps_run oL oR (if oR j then t1 else t0)"
    by (cases "oR j"; simp add: IH0 IH1)
  have fin: "finite ?S"
    by simp
  have "card (seenR_run oL oR (AskR j t0 t1)) = card (insert j ?S)" by simp
  also have "... \<le> Suc (card ?S)" using fin by (simp add: card_insert_if)
  also have "... \<le> Suc (steps_run oL oR (if oR j then t1 else t0))"
    using br by simp
  also have "... = steps_run oL oR (AskR j t0 t1)" by simp
  finally show ?case .
qed

(* Number of queries bounds the total number of distinct indices seen. *)
lemma steps_ge_sum_seen:
"steps_run oL oR T \<ge> card (seenL_run oL oR T) + card (seenR_run oL oR T)"
(* Each step either introduces a new index or re-reads an old one;
    the distinct indices from both sides cannot exceed the number of
    steps. *)
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  let ?SL = "seenL_run oL oR (if oL i then t1 else t0)"
  let ?SR = "seenR_run oL oR (if oL i then t1 else t0)"
  have IH0: "steps_run oL oR t0 \<ge> card (seenL_run oL oR t0) + card (seenR_run oL oR t0)"
    by (rule AskL.IH(1))
  have IH1: "steps_run oL oR t1 \<ge> card (seenL_run oL oR t1) + card (seenR_run oL oR t1)"
    by (rule AskL.IH(2))
  have br: "steps_run oL oR (if oL i then t1 else t0) \<ge> card ?SL + card ?SR"
    by (cases "oL i") (simp_all add: IH0 IH1)
  have fin: "finite ?SL" "finite ?SR"
    by (cases "oL i"; simp)+
  have "card (seenL_run oL oR (AskL i t0 t1)) + card (seenR_run oL oR (AskL i t0 t1))
       = card (insert i ?SL) + card ?SR" by simp
  also have "... \<le> Suc (card ?SL) + card ?SR"
    using fin(1) by (simp add: card_insert_if add_mono)
  also have "... = Suc (card ?SL + card ?SR)" by simp
  also have "... \<le> steps_run oL oR (AskL i t0 t1)"
    using br by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  let ?SL = "seenL_run oL oR (if oR j then t1 else t0)"
  let ?SR = "seenR_run oL oR (if oR j then t1 else t0)"
  have IH0: "steps_run oL oR t0 \<ge> card (seenL_run oL oR t0) + card (seenR_run oL oR t0)"
    by (rule AskR.IH(1))
  have IH1: "steps_run oL oR t1 \<ge> card (seenL_run oL oR t1) + card (seenR_run oL oR t1)"
    by (rule AskR.IH(2))
  have br: "steps_run oL oR (if oR j then t1 else t0) \<ge> card ?SL + card ?SR"
    by (cases "oR j") (simp_all add: IH0 IH1)
  have fin: "finite ?SL" "finite ?SR"
    by (cases "oR j"; simp)+
  have "card (seenL_run oL oR (AskR j t0 t1)) + card (seenR_run oL oR (AskR j t0 t1))
       = card ?SL + card (insert j ?SR)" by simp
  also have "... \<le> card ?SL + Suc (card ?SR)"
    using fin(2) by (simp add: card_insert_if add_mono)
  also have "... = Suc (card ?SL + card ?SR)" by simp
  also have "... \<le> steps_run oL oR (AskR j t0 t1)"
    using br by simp
  finally show ?case .
qed

(* This triple-lemma is an explicit version of the idea:
  "if you don't change any queried bits, the output and the set of
   queried indices stay the same." *)
lemma run_seen_agree_on_triple:
  assumes L: "\<And>i. i \<in> seenL_run oL oR T \<Longrightarrow> oL' i = oL i"
    and R: "\<And>j. j \<in> seenR_run oL oR T \<Longrightarrow> oR' j = oR j"
  shows "(run oL oR T, seenL_run oL oR T, seenR_run oL oR T)
      = (run oL' oR' T, seenL_run oL' oR' T, seenR_run oL' oR' T)"
  using L R
proof (induction T arbitrary: oL oR oL' oR')
  case (Leaf b)
  show ?case by simp
next
  case (AskL i t0 t1)
(* agreement on the queried index i *)
  have eq_i: "oL' i = oL i"
    using AskL.prems(1) by simp

(* IH packaged per subtree, guarded by the actual branch condition *)
  have rec_t1:
    "oL i \<Longrightarrow> (run oL oR t1, seenL_run oL oR t1, seenR_run oL oR t1)
          = (run oL' oR' t1, seenL_run oL' oR' t1, seenR_run oL' oR' t1)"
  proof -
    assume oi: "oL i"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t1 \<Longrightarrow> oL' x = oL x"
      using AskL.prems(1) seenL_sub_AskL by (simp add: oi)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t1 \<Longrightarrow> oR' x = oR x"
      using AskL.prems(2) seenR_eq_AskL by (simp add: oi)
    from AskL.IH(2)[OF Lb Rb] show ?thesis .
  qed

  have rec_t0:
    "\<not> oL i \<Longrightarrow> (run oL oR t0, seenL_run oL oR t0, seenR_run oL oR t0)
           = (run oL' oR' t0, seenL_run oL' oR' t0, seenR_run oL' oR' t0)"
  proof -
    assume noi: "\<not> oL i"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t0 \<Longrightarrow> oL' x = oL x"
      using AskL.prems(1) seenL_sub_AskL by (simp add: noi)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t0 \<Longrightarrow> oR' x = oR x"
      using AskL.prems(2) seenR_eq_AskL by (simp add: noi)
    from AskL.IH(1)[OF Lb Rb] show ?thesis .
  qed

(* combine the two guarded IHs to get the equality on the chosen branch *)
  have rec_if:
    "(run oL oR (if oL i then t1 else t0),
     seenL_run oL oR (if oL i then t1 else t0),
     seenR_run oL oR (if oL i then t1 else t0))
      =
    (run oL' oR' (if oL i then t1 else t0),
     seenL_run oL' oR' (if oL i then t1 else t0),
     seenR_run oL' oR' (if oL i then t1 else t0))"
    by (cases "oL i") (simp add: rec_t1, simp add: rec_t0)

(* reduce AskL on both sides and use oL' i = oL i for the condition *)
  have LHS_reduce:
    "(run oL oR (AskL i t0 t1),
     seenL_run oL oR (AskL i t0 t1),
     seenR_run oL oR (AskL i t0 t1))
      =
    (run oL oR (if oL i then t1 else t0),
     insert i (seenL_run oL oR (if oL i then t1 else t0)),
     seenR_run oL oR (if oL i then t1 else t0))" by simp
  have RHS_reduce:
    "(run oL' oR' (AskL i t0 t1),
     seenL_run oL' oR' (AskL i t0 t1),
     seenR_run oL' oR' (AskL i t0 t1))
      =
    (run oL' oR' (if oL i then t1 else t0),
     insert i (seenL_run oL' oR' (if oL i then t1 else t0)),
     seenR_run oL' oR' (if oL i then t1 else t0))"
    by (simp add: eq_i)

  show ?case
    using RHS_reduce rec_if by auto
next
  case (AskR j t0 t1)
(* agreement on the queried index j *)
  have eq_j: "oR' j = oR j"
    using AskR.prems(2) by simp

(* IH packaged per subtree, guarded by the actual branch condition *)
  have rec_t1:
    "oR j \<Longrightarrow> (run oL oR t1, seenL_run oL oR t1, seenR_run oL oR t1)
          = (run oL' oR' t1, seenL_run oL' oR' t1, seenR_run oL' oR' t1)"
  proof -
    assume oj: "oR j"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t1 \<Longrightarrow> oL' x = oL x"
      using AskR.prems(1) seenL_eq_AskR by (simp add: oj)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t1 \<Longrightarrow> oR' x = oR x"
      using AskR.prems(2) seenR_sub_AskR by (simp add: oj)
    from AskR.IH(2)[OF Lb Rb] show ?thesis .
  qed

  have rec_t0:
    "\<not> oR j \<Longrightarrow> (run oL oR t0, seenL_run oL oR t0, seenR_run oL oR t0)
           = (run oL' oR' t0, seenL_run oL' oR' t0, seenR_run oL' oR' t0)"
  proof -
    assume noj: "\<not> oR j"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t0 \<Longrightarrow> oL' x = oL x"
      using AskR.prems(1) seenL_eq_AskR by (simp add: noj)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t0 \<Longrightarrow> oR' x = oR x"
      using AskR.prems(2) seenR_sub_AskR by (simp add: noj)
    from AskR.IH(1)[OF Lb Rb] show ?thesis .
  qed

  have rec_if:
    "(run oL oR (if oR j then t1 else t0),
     seenL_run oL oR (if oR j then t1 else t0),
     seenR_run oL oR (if oR j then t1 else t0))
      =
      (run oL' oR' (if oR j then t1 else t0),
     seenL_run oL' oR' (if oR j then t1 else t0),
     seenR_run oL' oR' (if oR j then t1 else t0))"
    by (cases "oR j") (simp add: rec_t1, simp add: rec_t0)

  have LHS_reduce:
    "(run oL oR (AskR j t0 t1),
     seenL_run oL oR (AskR j t0 t1),
     seenR_run oL oR (AskR j t0 t1))
      =
    (run oL oR (if oR j then t1 else t0),
     seenL_run oL oR (if oR j then t1 else t0),
     insert j (seenR_run oL oR (if oR j then t1 else t0)))" by simp
  have RHS_reduce:
    "(run oL' oR' (AskR j t0 t1),
     seenL_run oL' oR' (AskR j t0 t1),
     seenR_run oL' oR' (AskR j t0 t1))
      =
    (run oL' oR' (if oR' j then t1 else t0),
     seenL_run oL' oR' (if oR' j then t1 else t0),
     insert j (seenR_run oL' oR' (if oR' j then t1 else t0)))" by simp
  have cond_swap: "(if oR' j then (X::'a) else Y) = (if oR j then X else Y)" 
    for X Y :: 'a by (simp add: eq_j)

  show ?case
    using eq_j rec_if by auto
qed

(* KEY CONSEQUENCE: If two oracles agree on all queried indices, they get
  the same result and query the same indices.  This is the formalisation
  of the “unread bits don't matter” principle used in adversary arguments. *)
lemma run_agree_on_seen:
  assumes L: "\<And>i. i \<in> seenL_run oL oR T \<Longrightarrow> oL' i = oL i"
    and R: "\<And>j. j \<in> seenR_run oL oR T \<Longrightarrow> oR' j = oR j"
  shows "run oL oR T = run oL' oR' T"
    and  "seenL_run oL oR T = seenL_run oL' oR' T"
    and  "seenR_run oL oR T = seenR_run oL' oR' T"
proof -
  from run_seen_agree_on_triple[OF L R]
  have "(run oL oR T, seenL_run oL oR T, seenR_run oL oR T)
     = (run oL' oR' T, seenL_run oL' oR' T, seenR_run oL' oR' T)" .
  thus "run oL oR T = run oL' oR' T"
    and "seenL_run oL oR T = seenL_run oL' oR' T"
    and "seenR_run oL oR T = seenR_run oL' oR' T" by auto
qed

section \<open>Concrete distinct-subset-sums instances: powers of two\<close>

text \<open>
As a concrete family of instances with distinct subset sums, we use the
standard *superincreasing* list in which each entry exceeds the sum of all
previous ones:

  \<open>pow2_list n = [1, 2, 4, ..., 2^(n - 1)]\<close>.

For this family, each subset corresponds to a unique integer via its binary
expansion.  We formalise this by proving that all subset sums are distinct,
captured by the lemma \<open>distinct_subset_sums_pow2_list\<close>.
\<close>

text \<open>
The proof follows the standard textbook argument: if two 0/1-vectors differ,
let \<open>i\<close> be the largest index at which they differ.  The contribution
\<open>2^i\<close> at this position strictly dominates the combined contributions
from all smaller indices, forcing the total sums to differ.
\<close>

text \<open>
*Caveat.*  The family \<open>pow2_list n\<close> is **not** intended to be algorithmically
hard in the usual RAM or Turing-machine sense.  Given a target value \<open>s\<close>,
one can reconstruct the unique candidate subset directly from the binary
expansion of \<open>s\<close>. These instances therefore show that the reader axiom does 
not express an intrinsic difficulty of the SUBSET--SUM problem.  Rather, it captures a
restriction on how a solver is allowed to obtain information: in the
oracle-style reader model, the solver must distinguish candidate values
explicitly and cannot exploit such global decoding shortcuts.

This is precisely why the lower bound developed in this theory is stated
*relative to the reader axiom*.  The argument does not claim that all algorithms require 
exponential time on these instances; it claims that any solver satisfying the abstract 
information-flow assumptions must do so.
\<close>

text \<open>
We therefore use \<open>pow2_list n\<close> solely as a clean and canonical source of
instances satisfying the injectivity property \<open>distinct_subset_sums\<close>.
This is the only property required by the counting and AM–GM arguments that follow.
\<close>

(* powers-of-two as ints. *)
definition pow2_list :: "nat \<Rightarrow> int list" where
"pow2_list n = map (\<lambda>i. (2::int)^i) [0..<n]"

lemma nth_pow2_list:
  assumes "i < n"
  shows "pow2_list n ! i = (2::int)^i"
  using assms by (simp add: pow2_list_def nth_map_upt)

lemma sum_prefix_pow2_list:
  assumes "k \<le> n"
  shows "(\<Sum> i<k. pow2_list n ! i) = (\<Sum> i<k. (2::int)^i)"
  using assms by (simp add: nth_pow2_list)

lemma pow2_gt_sum_prev_int:
  fixes k :: nat
  shows "(\<Sum> i<k. (2::int)^i) < 2^k"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "(\<Sum> i<Suc k. (2::int)^i) = (\<Sum> i<k. 2^i) + 2^k" by simp
  also have "... < 2^k + 2^k"
    using Suc.IH by (intro add_strict_right_mono)   (* int version *)
  also have "... = 2^(Suc k)" by simp
  finally show ?case .
qed

lemma sum_split_at:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "k < n"
  shows "sum f {..<n} = sum f {..<k} + f k + sum f {k+1..<n}"
proof -
(* split {..<n} into {..<k} ⪯ {k..<n} *)
  have part: "{..<n} = {..<k} \<union> {k..<n}"
    using \<open>k < n\<close> by auto
  have step1: "sum f {..<n} = sum f {..<k} + sum f {k..<n}"
    by (metis Un_upper1 lessThan_atLeast0 lessThan_subset_iff less_eq_nat.simps(1) 
        part sum.atLeastLessThan_concat)

(* peel k from {k..<n} *)
  have step2set: "{k..<n} = insert k {Suc k..<n}"
    by (metis Suc_leD assms atLeastLessThan_empty atLeastLessThan_empty_iff 
        atLeastLessThan_singleton insert_is_Un ivl_disj_un_two(3) not_less_eq_eq)
  have step2: "sum f {k..<n} = f k + sum f {Suc k..<n}"
    by (subst step2set) simp

(* combine *)
  have "sum f {..<n} = sum f {..<k} + f k + sum f {k+1..<n}"
    using step1 step2 by (metis Suc_eq_plus1 add.assoc)
  show ?thesis
    using \<open>sum f {..<n} = sum f {..<k} + f k + sum f {k + 1..<n}\<close> by blast
qed

(* triangle inequality for sums over {..<k} *)
lemma abs_sum_le_sum_abs_upto:
  shows "abs (\<Sum> i<k. (f i::int)) \<le> (\<Sum> i<k. abs (f i))"
  by (rule sum_abs)

(* handy nth fact over a mapped [0..<n] *)
lemma nth_map_upt:
  assumes "k < n"
  shows "(map f [0..<n]) ! k = f k"
  using assms by simp

lemma pow2_list_nth:
  assumes "k < n"
  shows "pow2_list n ! k = (2::int)^k"
  using assms by (simp add: pow2_list_def nth_map_upt)

(* the superincreasing property you want:
  each weight is larger than the sum of all previous weights. *)
lemma pow2_superincreasing:
  assumes "k < n"
  shows "pow2_list n ! k > (\<Sum> i<k. pow2_list n ! i)"
proof -
  have A: "pow2_list n ! k = (2::int)^k"
    using assms by (simp add: pow2_list_def nth_map_upt)
  have B: "(\<Sum> i<k. pow2_list n ! i) = (\<Sum> i<k. (2::int)^i)"
    using assms by (simp add: sum_prefix_pow2_list)
  show ?thesis
    by (simp add: A B pow2_gt_sum_prev_int)
qed

lemma sum_lessThan_split_at:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "k < n"
  shows "(\<Sum> i<n. f i) =
        (\<Sum> i<k. f i) + f k + (\<Sum> i = Suc k..<n. f i)"
proof -
  have "{..<n} = {..<k} \<union> {k} \<union> {Suc k..<n}"
    using assms by auto
  moreover have "finite ({..<k}::nat set)" and "finite {k}" and "finite {Suc k..<n}" by simp_all
  moreover have "{..<k} \<inter> {k} = {}" and "({..<k} \<union> {k}) \<inter> {Suc k..<n} = {}" by auto
  ultimately show ?thesis
    by (metis Un_insert_right add.commute boolean_algebra.disj_zero_right 
        disjoint_insert(1) finite_UnI sum.insert sum_Un_eq)
qed

lemma distinct_subset_sums_pow2_list:
  fixes n :: nat
  shows "distinct_subset_sums (pow2_list n)"
proof -
  let ?as = "pow2_list n"

  have uniq:
    "\<And>xs ys. xs \<in> bitvec n \<Longrightarrow> ys \<in> bitvec n \<Longrightarrow>
            (\<Sum> i<n. ?as!i * xs!i) = (\<Sum> i<n. ?as!i * ys!i) \<Longrightarrow> xs = ys"
  proof -
    fix xs ys assume xsB: "xs \<in> bitvec n" and ysB: "ys \<in> bitvec n"
      and EQ: "(\<Sum> i<n. ?as!i * xs!i) = (\<Sum> i<n. ?as!i * ys!i)"
    show "xs = ys"
    proof (rule ccontr)
      assume "xs \<noteq> ys"
      let ?D = "{i. i < n \<and> xs!i \<noteq> ys!i}"
      have finD: "finite ?D" by simp

      from xsB have xs_len: "length xs = n" and xs01_set: "set xs \<subseteq> {0,1}"
        by (auto simp: bitvec_def)
      from ysB have ys_len: "length ys = n" and ys01_set: "set ys \<subseteq> {0,1}"
        by (auto simp: bitvec_def)
      have xs01_i: "\<And>i. i < n \<Longrightarrow> xs!i \<in> {0,1}"
        using xs_len xs01_set by (metis in_mono nth_mem)
      have ys01_i: "\<And>i. i < n \<Longrightarrow> ys!i \<in> {0,1}"
        using ys_len ys01_set by (metis in_mono nth_mem)

      have D_ne: "?D \<noteq> {}" 
      proof 
        assume "?D = {}" 
        hence "\<forall>i<n. xs!i = ys!i" 
          by auto with xs_len ys_len 
        have "xs = ys" 
          by (intro nth_equalityI) auto with \<open>xs \<noteq> ys\<close> 
        show False by contradiction 
      qed 
      define k where "k = Max ?D" 
      have k_in: "k \<in> ?D" 
        using D_ne Max_in finD k_def by blast 
      hence k_lt: "k < n" and k_diff: "xs!k \<noteq> ys!k" by auto 
      have agree_after: "\<And>i. k < i \<Longrightarrow> i < n \<Longrightarrow> xs!i = ys!i" 
        using Max_less_iff finD k_def by blast

(* Tail after k cancels. *)
      have tail0: "(\<Sum> i\<in>{k+1..<n}. ?as!i * (xs!i - ys!i)) = 0"
        by (rule sum.neutral) (use agree_after in auto)

(* Turn EQ into 0 = sum of differences and split at k. *)
      have zero_sum: "0 = (\<Sum> i<n. ?as!i * (xs!i - ys!i))"
        using EQ by (simp add: sum_subtractf algebra_simps)
      have split_k:
        "(\<Sum> i<n. ?as!i * (xs!i - ys!i)) =
          (\<Sum> i<k. ?as!i * (xs!i - ys!i)) + ?as!k * (xs!k - ys!k)
          + (\<Sum> i = Suc k..<n. ?as!i * (xs!i - ys!i))"
        using k_lt by (rule sum_lessThan_split_at)

      from zero_sum split_k tail0
      have eq_abs:
        "abs (?as!k * (xs!k - ys!k))
        = abs (\<Sum> i<k. ?as!i * (xs!i - ys!i))" by simp

(* Triangle inequality and |xs!i - ys!i| \<le> 1. *)
      have abs_sum_le:
        "abs (\<Sum> i<k. ?as ! i * (xs ! i - ys ! i)) \<le> (\<Sum> i<k. abs (?as ! i))"
      proof -
        have "abs (\<Sum> i<k. ?as!i * (xs!i - ys!i))
             \<le> (\<Sum> i<k. abs (?as!i * (xs!i - ys!i)))" by (rule sum_abs)
        also have "... \<le> (\<Sum> i<k. abs (?as!i))"
        proof -
          have "\<forall>i<k. abs (?as!i * (xs!i - ys!i)) \<le> abs (?as!i)"
          proof (intro allI impI)
            fix i assume ik: "i < k"
            with k_lt have in_n: "i < n" by simp
            have "abs (?as!i * (xs!i - ys!i)) = abs (?as!i) * abs (xs!i - ys!i)"
              by (simp add: abs_mult)
            also have "... \<le> abs (?as!i) * 1"
              using xs01_i[OF in_n] ys01_i[OF in_n] by (intro mult_left_mono) auto
            finally show "abs (?as!i * (xs!i - ys!i)) \<le> abs (?as!i)" by simp
          qed
          then show ?thesis by (intro sum_mono) simp
        qed
        finally show ?thesis .
      qed

(* Drop abs on the prefix because weights are \<ge> 0. *)
      have prefix_nonneg: "\<And>i. i<k \<Longrightarrow> 0 \<le> ?as!i"
        using k_lt by (simp add: pow2_list_def)
      have abs_drop: "(\<Sum> i<k. abs (?as!i)) = (\<Sum> i<k. ?as!i)"
        by (rule sum.cong[OF refl]) (use prefix_nonneg in \<open>simp\<close>)

(* Also |xs!k - ys!k| = 1 and weights are \<ge> 0. *)
      have abs1: "abs (xs ! k - ys ! k) = 1"
        using xs01_i[OF k_lt] ys01_i[OF k_lt] k_diff by auto
      have nonneg_k: "0 \<le> ?as ! k"
        using k_lt by (simp add: pow2_list_def)
      have abs_prod: "abs (?as!k * (xs ! k - ys ! k)) = ?as!k"
        by (simp add: abs_mult abs1 nonneg_k)

(* pointwise bound: for every i<k, |a_i * (xs_i - ys_i)| \<le> |a_i| *)
      have term_le:
        "\<And>i. i < k \<Longrightarrow> abs (?as!i * (xs ! i - ys ! i)) \<le> abs (?as!i)"
      proof -
        fix i assume ik: "i < k"
        then have in_n: "i < n" using k_lt by simp
        have diff_le1: "abs (xs ! i - ys ! i) \<le> (1::int)"
          using xs01_i[OF in_n] ys01_i[OF in_n] by auto
        have "abs (?as!i * (xs ! i - ys ! i))
          = abs (?as!i) * abs (xs ! i - ys ! i)" by (simp add: abs_mult)
        also have "... \<le> abs (?as!i) * 1"
          using diff_le1 by (intro mult_left_mono) simp_all
        finally show "abs (?as!i * (xs ! i - ys ! i)) \<le> abs (?as!i)" by simp
      qed

(* now the chain for main_le goes through *)
      have main_le: "?as!k \<le> (\<Sum> i<k. ?as!i)"
      proof -
        have "?as!k = abs (?as!k * (xs ! k - ys ! k))" by (simp add: abs_prod)
        also have "... = abs (\<Sum> i<k. ?as!i * (xs ! i - ys ! i))" using eq_abs by simp
        also have "... \<le> (\<Sum> i<k. abs (?as!i * (xs ! i - ys ! i)))" by (rule sum_abs)
        also have "... \<le> (\<Sum> i<k. abs (?as!i))"
          by (intro sum_mono term_le) simp
        also have "... = (\<Sum> i<k. ?as!i)" by (simp add: abs_drop)
        finally show ?thesis .
      qed

(* Rewrite both sides as powers of 2. *)
      have lhs_pow: "?as!k = (2::int)^k"
        using k_lt by (simp add: pow2_list_def)
      have rhs_pow: "(\<Sum> i<k. ?as!i) = (\<Sum> i<k. (2::int)^i)"
      proof (rule sum.cong[OF refl])
        fix i assume "i \<in> {..<k}"
        with k_lt have "i < n" by auto
        thus "?as!i = (2::int)^i" by (simp add: pow2_list_def)
      qed

      have "(2::int)^k \<le> (\<Sum> i<k. (2::int)^i)"
        using main_le by (simp add: lhs_pow rhs_pow)

(* Final contradiction via closed form. *)
      hence "(2::int)^k \<le> (2::int)^k - 1"
        by (simp add: sum_pow2_int)
      thus False by linarith
    qed
  qed

(* length of the weight list is n, so the binders match *)
  have len_as[simp]: "length ?as = n" by (simp add: pow2_list_def)

  show ?thesis
    unfolding distinct_subset_sums_def
    by (simp; metis uniq)
qed

lemma diff_of_bits:
  fixes x y :: int
  assumes "x \<in> {0,1}" "y \<in> {0,1}" "x \<noteq> y"
  shows "x - y = 1 \<or> x - y = -1"
    using assms by auto

section \<open>Ruling out polynomial time in the decision-tree model\<close>

text \<open>
This section introduces the abstract locale
\<open>SubsetSum_Reader_Model\<close>, which captures a single
\emph{information-flow assumption} about solving SUBSET–SUM.

The locale is parameterised by:

\begin{itemize}
\item a cost measure \verb|steps as s|;
\item two families of sets \verb|seenL as s k| and \verb|seenR as s k|,
      representing the integer values that the solver has effectively
      distinguished on the left and right sides of the canonical split
      at position \verb|k|.
\end{itemize}

\medskip
\noindent
\textbf{Reader axiom.}
On every instance with distinct subset sums, there exists a split
position \verb|k \<le> n| such that:

\begin{itemize}
\item the solver’s distinguished values coincide exactly with the
      canonical split sets,
      \[
        \verb|seenL as s k| = \verb|LHS (e_k as s k) n|,
        \qquad
        \verb|seenR as s k| = \verb|RHS (e_k as s k) n|;
      \]
\item the total cost is at least the number of distinguished values,
      \[
        \verb|steps as s| \ge
        \verb|card (seenL as s k)| + \verb|card (seenR as s k)|.
      \]
\end{itemize}

From this single assumption, the locale derives the counting lower bound
\[
  \verb|steps as s| \ge 2 \cdot \sqrt{2^n}
\]
for all distinct-subset-sums instances of length \verb|n|.

\medskip
This axiom is \emph{not} proved in this theory. It formalises an
information-flow principle that is later instantiated for the
decision-tree model. No claim is made that it holds for arbitrary
machine models.
\<close>

locale SubsetSum_Reader_Model =
  fixes steps :: "int list \<Rightarrow> int \<Rightarrow> nat"
    and seenL :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set"
    and seenR :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set"
  assumes reader_axiom:
    "\<And>as s. distinct_subset_sums as \<Longrightarrow>
      \<exists>k\<le>length as.
        seenL as s k = LHS (e_k as s k) (length as) \<and>
        seenR as s k = RHS (e_k as s k) (length as) \<and>
        steps as s \<ge> card (seenL as s k) + card (seenR as s k)"
begin

lemma subset_sum_sqrt_lower_bound:
  assumes dist: "distinct_subset_sums as"
      and n_def: "n = length as"
  shows "2 * sqrt ((2::real)^n) \<le> real (steps as s)"
proof -
  obtain k where k_le: "k \<le> length as"
    and covL: "seenL as s k = LHS (e_k as s k) (length as)"
    and covR: "seenR as s k = RHS (e_k as s k) (length as)"
    and step_ge: "steps as s \<ge> card (seenL as s k) + card (seenR as s k)"
    using reader_axiom[OF dist] by blast

  have step_ge': "real (steps as s) \<ge>
        real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))"
    using step_ge n_def covL covR by simp

  have lower:
    "2 * sqrt ((2::real)^n) \<le>
     real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))"
    using lhs_rhs_sum_lower_bound[OF n_def] k_le dist
    by (simp add: n_def)

  show ?thesis
    using lower step_ge' by linarith
qed

end (* end of locale SubsetSum_Reader_Model *)

section \<open>Interpretation by the decision-tree model\<close>

text \<open>
We now show that the abstract locale \<open>SubsetSum_Reader_Model\<close> 
can be instantiated by our concrete decision-tree semantics, assuming an 
explicit coverage (information-flow) axiom.

Recall that the decision tree operates at the level of numerical
candidates, not at the level of bit encodings.  For a fixed split
position \verb|k|, the tree queries values drawn from the canonical
sets

\begin{itemize}
\item \verb|LHS (e_k as s k) (length as)| on the left, and
\item \verb|RHS (e_k as s k) (length as)| on the right.
\end{itemize}

The observable behaviour of a tree run is summarised by three quantities:

\begin{itemize}
\item \verb|seenL_run| — the set of left-hand values queried,
\item \verb|seenR_run| — the set of right-hand values queried,
\item \verb|steps_run| — the total number of oracle queries performed.
\end{itemize}

We postulate (as an explicit information-flow axiom) that on 
distinct-subset-sums instances there exists a split k at which the tree 
distinguishes all canonical candidates on both sides.  At such a split, 
we obtain the equalities

\[
  \verb|seenL_run| = \verb|LHS (e_k as s k) (length as)|,
  \qquad
  \verb|seenR_run| = \verb|RHS (e_k as s k) (length as)|.
\]

Moreover, each oracle query accounts for at most one newly distinguished
value, so the total number of queries bounds the total number of
distinguished candidates:

\[
  \verb|steps_run| \ge
  \verb|card seenL_run| + \verb|card seenR_run|.
\]

These facts exactly match the assumptions of
\<open>SubsetSum_Reader_Model\<close>.  We therefore obtain an
interpretation of the abstract locale with:

\begin{itemize}
\item \verb|steps = steps_run|,
\item \verb|seenL = seenL_run|,
\item \verb|seenR = seenR_run|.
\end{itemize}

All lower-bound results proved abstractly in \<open>SubsetSum_Reader_Model\<close> 
are thus inherited by the decision-tree model as concrete theorems. This locale does 
not model arbitrary arithmetic on as and s; it models solvers whose progress is 
measured by explicit oracle-style distinctions among canonical candidates.
\<close>

locale DT_SubsetSum_Solver =
  fixes T :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int,int) dtr"
  fixes oL :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool"
  fixes oR :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool"
  assumes wf_T:
    "\<And>as s k. wf_dtr (LHS (e_k as s k) (length as))
                    (RHS (e_k as s k) (length as))
                    (T as s k)"
  assumes coverage_axiom_DT:
    "\<And>as s. distinct_subset_sums as \<Longrightarrow>
      \<exists>k\<le>length as.
        seenL_run (oL as s k) (oR as s k) (T as s k)
        = LHS (e_k as s k) (length as) \<and>
        seenR_run (oL as s k) (oR as s k) (T as s k)
        = RHS (e_k as s k) (length as)"
begin

definition steps_DT :: "int list \<Rightarrow> int \<Rightarrow> nat" where
"steps_DT as s =
    Max { steps_run (oL as s k) (oR as s k) (T as s k)
        | k. k \<le> length as }"

definition seenL_DT :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set" where
"seenL_DT as s k =
    seenL_run (oL as s k) (oR as s k) (T as s k)"

definition seenR_DT :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set" where
"seenR_DT as s k =
    seenR_run (oL as s k) (oR as s k) (T as s k)"

lemma coverage_axiom_DT_DT:
  assumes "distinct_subset_sums as"
  shows "\<exists>k\<le>length as.
          seenL_DT as s k = LHS (e_k as s k) (length as) \<and>
          seenR_DT as s k = RHS (e_k as s k) (length as)"
proof -
  from coverage_axiom_DT[OF assms]
  obtain k where
    k_le: "k \<le> length as" and
    L: "seenL_run (oL as s k) (oR as s k) (T as s k)
        = LHS (e_k as s k) (length as)" and
    R: "seenR_run (oL as s k) (oR as s k) (T as s k)
        = RHS (e_k as s k) (length as)"
    by blast
  then show ?thesis
    by (intro exI[of _ k]) (simp_all add: seenL_DT_def seenR_DT_def)
qed

lemma steps_DT_lb:
  assumes "k \<le> length as"
  shows "steps_DT as s \<ge>
          card (seenL_DT as s k) + card (seenR_DT as s k)"
proof -
  let ?S = "{ steps_run (oL as s k') (oR as s k') (T as s k')
          | k'. k' \<le> length as }"

(* The Max is over a finite set of naturals *)
  have fin_S: "finite ?S"
  proof -
    let ?K = "{k'. k' \<le> length as}"
    have K_fin: "finite ?K" by simp
    have S_eq:
      "?S = (\<lambda>k'. steps_run (oL as s k') (oR as s k') (T as s k')) ` ?K"
      by auto
    have "finite ((\<lambda>k'. steps_run (oL as s k') (oR as s k') (T as s k')) ` ?K)"
      using K_fin by (rule finite_imageI)
    thus ?thesis
      by (simp add: S_eq)
  qed

(* Our particular k is indeed in the index range *)
  have in_S: "steps_run (oL as s k) (oR as s k) (T as s k) \<in> ?S"
    using assms by auto

(* So its value is \<le> Max of that set *)
  have le_Max:
    "steps_run (oL as s k) (oR as s k) (T as s k) \<le> steps_DT as s"
    unfolding steps_DT_def
    using fin_S in_S
    by simp

(* Per-run lower bound: steps \<ge> card(seenL)+card(seenR) *)
  have base:
    "steps_run (oL as s k) (oR as s k) (T as s k)
      \<ge> card (seenL_run (oL as s k) (oR as s k) (T as s k))
      + card (seenR_run (oL as s k) (oR as s k) (T as s k))"
    by (rule steps_ge_sum_seen)

(* Rewrite seenL_DT/seenR_DT in terms of seenL_run/seenR_run *)
  have "card (seenL_DT as s k) + card (seenR_DT as s k)
        = card (seenL_run (oL as s k) (oR as s k) (T as s k))
         + card (seenR_run (oL as s k) (oR as s k) (T as s k))"
    by (simp add: seenL_DT_def seenR_DT_def)

  also have "... \<le> steps_run (oL as s k) (oR as s k) (T as s k)"
    using base by simp

  also have "... \<le> steps_DT as s"
    using le_Max by simp

  finally show ?thesis by simp
qed

(* shape match with SubsetSum_Reader_Model.steps_lb *)
lemma steps_lb_DT:
  assumes "k \<le> length as"
  shows "steps_DT as s \<ge> card (seenL_DT as s k) + card (seenR_DT as s k)"
    using steps_DT_lb[OF assms] .

text \<open>
We now connect the abstract framework of the locale
\<open>SubsetSum_Reader_Model\<close> to the concrete decision-tree model defined
earlier.

Recall that \<open>SubsetSum_Reader_Model\<close> is parameterised by:

\begin{itemize}
\item a cost function \verb|steps as s|;
\item value families \verb|seenL as s k| and \verb|seenR as s k|.
\end{itemize}

The locale assumes a single packaged axiom (the \emph{reader axiom}): on every
instance with \verb|distinct_subset_sums as|, there exists a split position
\verb|k \<le> length as| such that

\[
  \verb|seenL as s k| = \verb|LHS (e_k as s k) (length as)|,
  \qquad
  \verb|seenR as s k| = \verb|RHS (e_k as s k) (length as)|,
\]

and moreover the cost is bounded below by the number of distinguished values,

\[
  \verb|steps as s| \ge
  \verb|card (seenL as s k)| + \verb|card (seenR as s k)|.
\]

\medskip
In the decision-tree model we have already defined:

\begin{itemize}
\item \verb|steps_DT as s| — a worst-case query bound, defined as the maximum
      of \verb|steps_run| over all split positions \verb|k \<le> length as|;
\item \verb|seenL_DT as s k| — the set of left-hand values queried by the tree
      corresponding to split \verb|k|;
\item \verb|seenR_DT as s k| — the analogous set of right-hand values.
\end{itemize}

The interpretation

\begin{center}
\verb|interpretation DT_Model: SubsetSum_Reader_Model steps_DT seenL_DT seenR_DT|
\end{center}

instantiates the abstract locale with these decision-tree objects.  Isabelle
generates a single proof obligation, corresponding to the reader axiom.

\medskip
This obligation is discharged by combining:

\begin{itemize}
\item \verb|coverage_axiom_DT|, which provides (for every
      \verb|distinct_subset_sums| instance) a split position \verb|k| at which
      the tree’s seen-sets coincide with the canonical
      \verb|LHS| and \verb|RHS| sets;
\item \verb|steps_lb_DT|, which yields the corresponding lower bound
      \[
        \verb|steps_DT as s| \ge
        \verb|card (seenL_DT as s k)| + \verb|card (seenR_DT as s k)|.
      \]
      This bound is derived from the per-run inequality
      \verb|steps_ge_sum_seen| together with the definition of
      \verb|steps_DT| as a maximum over \verb|k|.
\end{itemize}

After this interpretation, all conclusions of
\<open>SubsetSum_Reader_Model\<close> are available specialised to the
decision-tree model.  In particular, for every distinct-subset-sums instance
of length \verb|n| we obtain the lower bound

\[
  2 \cdot \sqrt{2^n} \le \verb|real (steps_DT as s)|.
\]
\<close>

interpretation DT_Model:
  SubsetSum_Reader_Model steps_DT seenL_DT seenR_DT
proof
  fix as s
  assume dist: "distinct_subset_sums as"

  (* get the witnessing split k with exact LHS/RHS coverage *)
  obtain k where
    k_le: "k \<le> length as" and
    covL: "seenL_DT as s k = LHS (e_k as s k) (length as)" and
    covR: "seenR_DT as s k = RHS (e_k as s k) (length as)"
    using coverage_axiom_DT_DT[OF dist] by blast

  (* for that same k, get the steps lower bound *)
  have step_ge:
    "steps_DT as s \<ge> card (seenL_DT as s k) + card (seenR_DT as s k)"
    using steps_lb_DT[OF k_le] .

  (* package everything into the single reader_axiom obligation *)
  show "\<exists>k\<le>length as.
          seenL_DT as s k = LHS (e_k as s k) (length as) \<and>
          seenR_DT as s k = RHS (e_k as s k) (length as) \<and>
          steps_DT as s \<ge> card (seenL_DT as s k) + card (seenR_DT as s k)"
    using k_le covL covR step_ge by blast
qed

end

text \<open>
This section introduces an abstract wrapper locale,
\<open>SubsetSum_To_Polytime\<close>, which packages the lower bound obtained from
\<open>SubsetSum_Reader_Model\<close> together with two high-level complexity
assumptions.

The assumptions are intentionally stated at a coarse level:

\begin{itemize}
\item there exists an encoding \verb|enc as s| whose length is bounded by a
      polynomial in \verb|n = length as|, at least on the family of
      distinct-subset-sums instances;
\item the cost function \verb|steps as s| is bounded above by a polynomial in
      the length of the encoding.
\end{itemize}

Within this abstract setting, we show that these assumptions contradict the
\(\sqrt{2^n}\) lower bound derived earlier from
\<open>SubsetSum_Reader_Model\<close>.  Concretely, when instantiated on a canonical
distinct-subset-sums family such as \verb|as = pow2_list n|, the polynomial
upper bounds are incompatible with the exponential lower bound.

The final theorem of the locale, \verb|reader_axiom_incompatible_with_poly_bounds|, 
therefore states that the assumptions of \<open>SubsetSum_To_Polytime\<close> are jointly
inconsistent.  Informally:

\begin{quote}
the reader axiom, together with polynomially bounded encodings and
polynomially bounded step counts, cannot simultaneously hold on the
distinct-subset-sums family.
\end{quote}

The locale \<open>SubsetSum_To_Polytime\<close> thus combines three ingredients:

\begin{itemize}
\item the abstract LR-reader model supplied by
      \<open>SubsetSum_Reader_Model\<close>;
\item a polynomial bound on the length of the instance encoding
      \verb|enc as s|;
\item a polynomial bound on the cost \verb|steps as s| in terms of that length.
\end{itemize}

Under these assumptions, a contradiction is derived on the concrete
distinct-subset-sums family \verb|as = pow2_list n|.
\<close>

locale SubsetSum_To_Polytime =
  SubsetSum_Reader_Model +
  fixes enc :: "int list \<Rightarrow> int \<Rightarrow> bool list"
  assumes enc_len_poly:
    "\<exists>(C::real)>0. \<exists>(D::nat).
     \<forall>as s. distinct_subset_sums as \<longrightarrow>
       real (length (enc as s)) \<le> C * (real (length as)) ^ D"
  assumes steps_poly_of_enc:
    "\<exists>(c::real)>0. \<exists>(d::nat).
     \<forall>as s. steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
begin

lemma steps_poly_in_n_on_distinct:
shows "\<exists>(c'::real)>0. \<exists>(d'::nat).
          \<forall>as s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
                   steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
proof -
  obtain C :: real and D :: nat
    where Cpos: "C > 0"
      and enc_bd:
      "\<forall>as s. distinct_subset_sums as \<longrightarrow>
          real (length (enc as s)) \<le> C * (real (length as)) ^ D"
    using enc_len_poly by blast
  obtain c :: real and d :: nat
    where cpos: "c > 0"
      and step_bd:
      "\<forall>as s. steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
    using steps_poly_of_enc by blast
  define c' where "c' = c * C ^ d"
  define d' where "d' = D * d"
  have c'pos: "c' > 0" using cpos Cpos by (simp add: c'_def)

  have main:
    "\<forall>as s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
      steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
  proof (intro allI impI)
    fix as s n assume n_def: "n = length as" and dist: "distinct_subset_sums as"
    have step0: "steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
      using step_bd by blast
    have enc_real: "real (length (enc as s)) \<le> C * (real n) ^ D"
      using enc_bd dist n_def by simp
    have nonneg_x: "0 \<le> real (length (enc as s))" by simp
    have nonneg_y: "0 \<le> C * (real n) ^ D"
      using Cpos by (intro mult_nonneg_nonneg) simp_all
    have pow_mono:
      "(real (length (enc as s))) ^ d \<le> (C * (real n) ^ D) ^ d"
      by (rule power_mono) (use enc_real nonneg_x nonneg_y in auto)
    have mult_mono:
      "c * (real (length (enc as s))) ^ d \<le> c * (C * (real n) ^ D) ^ d"
      using pow_mono cpos by (simp add: mult_left_mono)
    have step1:
      "nat (ceiling (c * (real (length (enc as s))) ^ d))
        \<le> nat (ceiling (c * (C * (real n) ^ D) ^ d))"
      using mult_mono by (intro nat_mono ceiling_mono) simp_all
    from step0 step1
    have "steps as s \<le> nat (ceiling (c * (C * (real n) ^ D) ^ d))" by linarith
    also have "... = nat (ceiling ((c * C ^ d) * (real n) ^ (D * d)))"
      by (simp add: power_mult_distrib mult_ac power_mult)
    finally show "steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
      by (simp add: c'_def d'_def)
  qed
  show ?thesis using c'pos main by blast
qed

(* Standard asymptotic fact: exponentials beat polynomials.

  We use it to show that for sufficiently large n, the polynomial
  upper bound on steps as s is strictly smaller than the exponential
  lower bound 2 * sqrt(2^n), which yields a contradiction.
*)
lemma exp_beats_poly_ceiling_strict:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "\<exists>N::nat. \<forall>n\<ge>N.
          of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
(* Eventually: c * n^d \<le> (√2)^n *)
  have ev: "eventually (\<lambda>n. c * (real n) ^ d \<le> (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 where N1: "\<forall>n\<ge>N1. c * (real n) ^ d \<le> (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)
  define N where "N = max N1 1"

  have ceil_le: "of_int (ceiling y) \<le> y + 1" for y :: real by linarith
  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n \<ge> N"
    hence nN1: "n \<ge> N1" and n_ge1: "n \<ge> 1" by (auto simp: N_def)
    from N1 nN1 have bound: "c * (real n) ^ d \<le> (sqrt 2) ^ n" by simp
    have up: "of_int (ceiling (c * (real n) ^ d)) \<le> (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith
    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by auto
    from up step have L: "of_int (ceiling (c * (real n) ^ d)) < 2 * (sqrt 2) ^ n"
      by linarith
    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with L show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)" by simp
  qed
qed

section \<open>Inconsistency of the reader axiom with polynomial-time bounds\<close>

text \<open>
This final section combines the abstract \(\sqrt{2^n}\) lower bound obtained
from \<open>SubsetSum_Reader_Model\<close> with the polynomial upper-bound assumptions
packaged in the locale \<open>SubsetSum_To_Polytime\<close>.

Recall that the family \verb|as = pow2_list n| was shown earlier in this theory
to satisfy the property \verb|distinct_subset_sums as|.  On this family, the reader 
axiom yields a lower bound of order \(\sqrt{2^n}\) on the cost \<open>steps as s\<close> 
*within the reader model*.

Inside the locale \<open>SubsetSum_To_Polytime\<close>, we additionally assume that:

\begin{itemize}
\item the instance encoding length is bounded by a polynomial in
      \verb|n = length as|; and
\item the cost function \verb|steps as s| is bounded above by a polynomial in
      the encoding length.
\end{itemize}

These assumptions are incompatible on the distinct-subset-sums family
\verb|pow2_list n|.  The polynomial upper bound contradicts the exponential
lower bound, and we therefore derive \verb|False|.

\medskip
The contradiction is derived \emph{only within the locale}
\<open>SubsetSum_To_Polytime\<close>.  It expresses inconsistency of the stated
assumptions, not inconsistency of HOL itself.  Outside this locale, no
contradiction is asserted.
\<close>

theorem reader_axiom_incompatible_with_poly_bounds:
  False
proof -
(* 1. Get the polynomial bound on steps as a function of n *)
  obtain c' :: real and d' :: nat
    where c'pos: "c' > 0"
      and poly_bd:
      "\<forall>as s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
          steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
    using steps_poly_in_n_on_distinct by blast

(* 2. Exponential (2 * sqrt(2^n)) eventually dominates c' * n^d' *)
  obtain N :: nat
    where N_prop:
      "\<forall>n\<ge>N. of_int (ceiling (c' * (real n) ^ d')) < 2 * sqrt ((2::real) ^ n)"
    using exp_beats_poly_ceiling_strict[OF c'pos] by blast

(* 3. Pick a large n where the separation holds *)
  let ?n = "max N 1"
  have n_ge_N: "?n \<ge> N" by simp

(* 4. Use the concrete weights as = pow2_list ?n *)
  define as where "as = pow2_list ?n"
  have n_def: "?n = length as"
    by (simp add: as_def pow2_list_def)

  have distinct: "distinct_subset_sums as"
    by (simp add: as_def distinct_subset_sums_pow2_list)

(* 5. Lower bound: \<Omega>(√(2^n)) *)
  have lb: "2 * sqrt ((2::real) ^ ?n) \<le> real (steps as 0)"
    using subset_sum_sqrt_lower_bound[OF distinct n_def] .

(* 6. Upper bound: polynomial in n from the encoding assumptions *)
  have ub_nat: "steps as 0 \<le> nat (ceiling (c' * (real ?n) ^ d'))"
  proof -
(* specialize poly_bd to this particular as *)
    have poly_bd_as:
      "\<forall>s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
          steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
      using poly_bd by blast

(* now specialize to s = 0, n = ?n *)
    have specd:
      "?n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
        steps as 0 \<le> nat (ceiling (c' * (real ?n) ^ d'))"
    proof -
      from poly_bd_as
      have "\<forall>n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
             steps as 0 \<le> nat (ceiling (c' * (real n) ^ d'))"
        by (drule_tac x=0 in spec)
      then show ?thesis
        by (drule_tac x="?n" in spec) simp
    qed

(* discharge the premises using your n_def and distinct *)
    show ?thesis
      using specd n_def distinct by simp
  qed

  have ub: "real (steps as 0) \<le> real_of_int \<lceil>c' * (real ?n) ^ d'\<rceil>"
  proof -
    from ub_nat have
      "real (steps as 0) \<le> real (nat \<lceil>c' * (real ?n) ^ d'\<rceil>)" by simp
    also have "... = real_of_int \<lceil>c' * (real ?n) ^ d'\<rceil>"
      using c'pos by force
    finally show ?thesis .
  qed

(* 7. Combine with the asymptotic separation at n \<ge> N *)
  have sep: "of_int (ceiling (c' * (real ?n) ^ d')) < 2 * sqrt ((2::real) ^ ?n)"
    using N_prop n_ge_N by simp

  from lb ub sep show False by linarith
qed

end (* SubsetSum_To_Polytime *)

end (* Theory *)
