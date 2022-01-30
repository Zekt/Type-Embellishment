\documentclass[acmsmall,review]{acmart}

%% Rights management information.  This information is sent to you
%% when you complete the rights form.  These commands have SAMPLE
%% values in them; it is your responsibility as an author to replace
%% the commands and values with those provided to you when you
%% complete the rights form.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\copyrightyear{2018}
%\acmYear{2018}
%\acmDOI{10.1145/1122445.1122456}

%%
%% These commands are for a JOURNAL article.
\acmJournal{PACMPL}
\acmVolume{0}
\acmNumber{0}
\acmArticle{0}
\acmMonth{0}

%%
%% Submission ID.
%% Use this when submitting an article to a sponsored event. You'll
%% receive a unique submission ID from the organizers
%% of the event, and this ID should be used as the parameter to this command.
%%\acmSubmissionID{123-A56-BU3}

%%
%% The majority of ACM publications use numbered citations and
%% references.  The command \citestyle{authoryear} switches to the
%% "author year" style.
%%
%% If you are preparing content for an event
%% sponsored by ACM SIGGRAPH, you must use the "author year" style of
%% citations and references.
%% Uncommenting
%% the next command will enable that style.
\citestyle{acmauthoryear}

\settopmatter{printacmref=false}

%\usepackage{bbold}
\usepackage[euler]{textgreek}

\usepackage{cleveref}

\usepackage[color=yellow,textsize=scriptsize]{todonotes}
\setlength{\marginparwidth}{1.25cm}

\newenvironment{halfcol}{\begin{minipage}{.45\textwidth}\setlength{\mathindent}{0em}}{\end{minipage}}

\newcommand{\arXiv}[1]{\href{http://arxiv.org/abs/#1}{arXiv:\nolinkurl{#1}}}

\let\Bbbk\relax
%include agda.fmt

\setlength{\mathindent}{.5\parindent}
%\renewcommand{\Varid}{\texttt}
%\renewcommand{\Conid}{\texttt}
\newcommand{\iden}{\mathit}

%format pattern = "\Keyword{pattern}"

%format : = "\mathop:"
%format → = "\mathop\to"
%format × = "\mathop\times"
%format ⊎ = "\mathop\uplus"
%format ≡ = "\mathop\equiv"
%format ∘ = "\mathop\circ"
%format ⊔ = "\mathop\sqcup"

%format Acc< = Acc "_<"
%format Acc<D = Acc "_<\Conid{D}"
%format foldAcc< = fold Acc<
%format foldAcc<Alg = foldAcc< Alg

%format ᵗ = "_{\Conid T}"
%format ⟦_⟧ᵗ = ⟦_⟧ ᵗ
%format ⟧ᵗ = ⟧ ᵗ
%format Curriedᵗ = Curried ᵗ
%format uncurryᵗ = uncurry ᵗ

%format ʳ = "_{\Conid R}"
%format ⟦_⟧ʳ = ⟦_⟧ ʳ
%format ⟧ʳ = ⟧ ʳ
%format fmapʳ = fmap ʳ

%format ᶜ = "_{\Conid C}"
%format ⟦_⟧ᶜ = ⟦_⟧ ᶜ
%format ⟧ᶜ = ⟧ ᶜ
%format fmapᶜ = fmap ᶜ
%format Algᶜ = Alg ᶜ
%format FoldOpTᶜ = FoldOpT ᶜ
%format fold-opᶜ = fold-op ᶜ

%format ᶜˢ = "_{\Conid{Cs}}"
%format ⟦_⟧ᶜˢ = ⟦_⟧ ᶜˢ
%format ⟧ᶜˢ = ⟧ ᶜˢ
%format fmapᶜˢ = fmap ᶜˢ
%format Algᶜˢ = Alg ᶜˢ
%format FoldOpTelᶜˢ = FoldOpTel ᶜˢ
%format fold-opᶜˢ = fold-op ᶜˢ
%format FoldOpTelᶜˢ = FoldOpTel ᶜˢ

%format ᵖ = "_{\Conid P}"
%format Dᵖ = D "\kern.5pt" ᵖ

%format A = "\iden A"
%format C = "\iden C"
%format D = "\iden D"
%format E = "\iden E"
%format Ds = "\iden{Ds}"
%format I = "\iden I"
%format N = "\iden N"
%format P = "\iden P"
%format X = "\iden X"
%format Y = "\iden Y"
%format a = "\iden a"
%format accs = "\iden{accs}"
%format alg = "\iden{alg}"
%format args = "\iden{args}"
%format cb = "\iden{cb}"
%format cbs = "\iden{cbs}"
%format d = "\iden d"
%format ds = "\iden{ds}"
%format eq = "\iden{eq}"
%format f = "\iden f"
%format fs = "\iden{fs}"
%format i = "\iden i"
%format j = "\iden j"
%format ℓs = "\iden{" ℓ "\kern-1pt s}"
%format lt = "\iden{lt}"
%format m = "\iden m"
%format n = "\iden n"
%format ns = "\iden{ns}"
%format p = "\iden p"
%format ps = "\iden{ps}"
%format x = "\iden x"
%format xs = "\iden{xs}"
%format xs' = "\iden{xs^\prime}"

%%
%% end of the preamble, start of the body of the document source.
\begin{document}

%%
%% The "title" command has an optional parameter,
%% allowing the author to define a "short title" to be used in page headers.
\title{Datatype-Generic Programming Meets Metaprogramming}

%%
%% The "author" command and its associated commands are used to define
%% the authors and their affiliations.
%% Of note is the shared affiliation of the first two authors, and the
%% "authornote" and "authornotemark" commands
%% used to denote shared contribution to the research.
\author{Hsiang-Shang Ko}
\email{joshko@@iis.sinica.edu.tw}
\orcid{0000-0002-2439-1048}
\author{Liang-Ting Chen}
\email{liang.ting.chen.tw@@gmail.com}
\orcid{0000-0002-3250-1331}
\author{Tzu-Chi Lin}
%\orcid{0000-0000-0000-0000}
\email{vik@@iis.sinica.edu.tw}
\affiliation{%
  \institution{Institute of Information Science, Academia Sinica}
  \streetaddress{128 Academia Road, Section 2, Nankang}
  \city{Taipei}
  \country{Taiwan}
  \postcode{115201}
}

%%
%% By default, the full list of authors will be used in the page
%% headers. Often, this list is too long, and will overlap
%% other information printed in the page headers. This command allows
%% the author to define a more concise list
%% of authors' names for this purpose.
%\renewcommand{\shortauthors}{Trovato and Tobin, et al.}

%%
%% The abstract is a short summary of the work to be presented in the
%% article.
\begin{abstract}
  Datatype-generic programming is typed metaprogramming over datatypes.
\end{abstract}

%\begin{CCSXML}
%<ccs2012>
%   <concept>
%       <concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
%       <concept_desc>Software and its engineering~Functional languages</concept_desc>
%       <concept_significance>500</concept_significance>
%       </concept>
%   <concept>
%       <concept_id>10003752.10003790.10011740</concept_id>
%       <concept_desc>Theory of computation~Type theory</concept_desc>
%       <concept_significance>100</concept_significance>
%       </concept>
%   <concept>
%       <concept_id>10011007.10011006.10011008.10011024.10011028</concept_id>
%       <concept_desc>Software and its engineering~Data types and structures</concept_desc>
%       <concept_significance>500</concept_significance>
%       </concept>
% </ccs2012>
%\end{CCSXML}
%
%\ccsdesc[500]{Software and its engineering~Functional languages}
%\ccsdesc[300]{Theory of computation~Type theory}
%\ccsdesc[300]{Software and its engineering~Data types and structures}
%
%\keywords{typed metaprogramming, datatype-generic programming, inductive families, ornaments}

\maketitle

\section{What Does the Dependently Typed Programmer Want from Datatype-Generic Libraries?}

\todo[inline]{2 pages}

\todo[inline]{Problems with the current state of dependently typed DGP (the kind of DGP discussed in this paper; no qualification thereafter)}

\todo[inline]{What we really want from generic libraries, using lists and vectors as familiar examples: we want to generate functions for native datatypes as if they are hand-written so that they are efficient to compute (no back-and-forth representation conversions), easy to reason about (again without the conversions and no excessive abstraction), and can fully benefit from whatever language facilities there are (e.g., Agda's interactive features and compiler optimisations); moreover, we want to generate not only, for example, fold operators but also their theorems such as fold fusion; particularly important in a dependently typed setting is the ability to generate new \emph{datatypes}, and then their functions and properties (e.g., algebraic ornamentation and the associated isomorphism)}

\todo[inline]{Staging? No! Enter elaborator reflection.}

\todo[inline]{Some actual demo}

\todo[inline]{
Contributions:

$\bullet$ Encoding of universe-polymorphic and parametrised inductive families (precise calculation of universe levels)

$\bullet$ Better interoperability with native datatypes and functions (generating new native datatypes and functions, and connecting with existing ones for which generic constructions are specialised)

$\bullet$ A new use case of elaborator reflection where traditional datatype-generic programs are simply normalised to yield native programs (and do not need more radical adaptations like staging)

$\bullet$ Simpler and less error-prone `object-level' binder-manipulating techniques with (Agda's) elaborator reflection (bypassing the manipulation of de Bruijn indices; a tutorial for Agda's reflection mechanism)}

\section{A Recap of Datatype-Generic Programming}

\todo[inline]{3 pages}

\todo[inline]{A recap of the standard approach (except for some minor details), also serving as an outline}

\todo[inline]{Typesetting conventions (in a footnote)}

We start from a recap of standard datatype-generic programming (DGP) within a dependently typed setting, but use a three-layered encoding of datatypes that more closely follows the structure of a native datatype definition, which has a list of constructors made up of a series of fields, some of which can be potentially higher-order recursive occurrences of the datatype being defined.%
\footnote{This choice of layered structure has also been adopted elsewhere, for example by \citet{de-Vries-true-SoP}.}
As a small example that covers all the essential components of datatype definitions (in particular higher-order recursive occurrence), consider this datatype |Acc<| of accessibility proofs:%
\footnote{Although the meaning of |Acc<| is not important here, a quick explanation is that a proof |acc accs : Acc< n| that |n|~is accessible captures the fact that any descending chain from~|n| with respect to~|_<_| is finite: if we deconstruct the proof by applying |accs| to some~|m| such that |m < n|, we will get a proof of |Acc< m|, which we can keep deconstructing, but can only do so a finite number of times because |Acc<| is an inductive datatype.}
\begin{code}
data Acc< : ℕ → Set where
  acc : {n : ℕ} (accs : (m : ℕ) (lt : m < n) → Acc< m) → Acc< n
\end{code}
The first layer is the list of constructors, which for |Acc<| consists of only |acc|;
the type of |acc| has two fields |n|~and |accs|, which constitute the second layer;
the type of the field |accs| is described in the third layer as it ends with the recursive occurrence |Acc< m|, in front of which there are function arguments |m|~and~|lt| (making the recursive occurrence higher-order).
Corresponding to the three layers, we use three datatypes of \emph{datatype descriptions} ---all parametrised by an index type~|I|--- to encode datatype definitions,
\begin{code}
data ConDs (I : Set) : Set₁ where
  []   : ConDs I
  _∷_  : (D : ConD I) (Ds : ConDs I) → ConDs I

data ConD (I : Set) : Set₁ where
  ι  : (i : I) → ConD I
  σ  : (A : Set) (D : A → ConD I) → ConD I
  ρ  : (D : RecD I) (E : ConD I) → ConD I

data RecD (I : Set) : Set₁ where
  ι   : (i : I) → RecD I
  π   : (A : Set) (D : A → RecD I) → RecD I
\end{code}
with which |Acc<| is described by
\begin{code}
Acc<D : ConDs ℕ
Acc<D = (σ ℕ (λ n → ρ (π ℕ (λ m → π (m < n) (λ lt → ι m))) (ι n))) ∷ []
\end{code}
Inhabitants of |ConDs I| are just lists of constructor (type) descriptions of type |ConD I|.
Inhabitants of |ConD I| are also list-like, where the elements can either be the type of an ordinary field, marked by~|σ|, or describe a recursive occurrence, marked by~|ρ|, and the `lists' end with~|ι|.
Different from ordinary lists, in the case of |σ A D| a new variable of type~|A| is brought into the context of~|D| (for example, |n|~appears in the type of |accs|); this is done by making~|D| a function with an argument of type~|A|, using the host language's function space to extend the context.\todo{forward reference about detecting abuses}%
\footnote{The expressive power of the host language's function space has been better utilised in the DGP literature (for example by \citet[Section~2.1]{McBride-ornaments}), but we will refrain from abusing the function space in the datatype descriptions for tasks beyond context extension, and it will be easy to detect abuses at the meta-level.}
Moreover, the~|ι| at the end of a |ConD I| should specify the index targeted by the constructor (e.g., the final~|n| in the type of |acc|).
Inhabitants of |RecD I| use the same structure to describe dependent function types ending with a recursive occurrence.

In the standard recipe, a datatype description |D : ConDs I| is converted to an actual type family |μ D : I → Set| by the operator~|μ| which takes the least fixed point of the base functor |⟦ D ⟧ᶜˢ : (I → Set) → (I → Set)|:
\begin{code}
data μ (D : ConDs I) : I → Set where
  con : ∀ {i} → ⟦ D ⟧ᶜˢ (μ D) i → μ D i
\end{code}
For example, we can redefine |Acc<| as
\begin{code}
Acc< : ℕ → Set
Acc< = μ Acc<D
\end{code}
whose inhabitants are now constructed by the generic constructor |con|.
The argument of |con| (of type |⟦ D ⟧ᶜˢ (μ D) i|) encodes the constructor choice and the arguments of the chosen constructor in a sum-of-products structure; for example, in Agda it is more convenient to use a pattern synonym to define |acc| in terms of |con|,
\begin{code}
pattern acc {n} accs = con (inl (n , accs , refl))
\end{code}
where the arguments |n|~and |accs| of |acc| are collected in a tuple, which is injected into a sum type by |inl|, and finally wrapped up with |con| as an inhabitant of |μ Acc<D n|.
The equality proof |refl| at the end of the tuple needs a bit more explanation: in the type of |con|, the index~|i| is universally quantified, which seems to suggest that we could construct inhabitants of |μ D i| for any~|i|, but the equality proof forces~|i| to be~|n|, the index targeted by |acc|.
The sum and product structures are defined respectively on the first two layers of datatype descriptions:
\begin{code}
⟦_⟧ᶜˢ : ConDs I → (I → Set) → (I → Set)
⟦ []      ⟧ᶜˢ X i = ⊥
⟦ D ∷ Ds  ⟧ᶜˢ X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i

⟦_⟧ᶜ : ConD I → (I → Set) → (I → Set)
⟦ ι j      ⟧ᶜ X i = i ≡ j
⟦ σ A  D   ⟧ᶜ X i = Σ[ a ∈ A ] ⟦ D a ⟧ᶜ X i
⟦ ρ D  E   ⟧ᶜ X i = ⟦ D ⟧ʳ X × ⟦ E ⟧ᶜ X i
\end{code}
In the |ρ|~case we need to translate~|D| into the type of the recursive occurrence, which is done by
\begin{code}
⟦_⟧ʳ : RecD I → (I → Set) → Set
⟦ ι i    ⟧ʳ X = X i
⟦ π A D  ⟧ʳ X = (a : A) → ⟦ D a ⟧ʳ X
\end{code}

Now we can write programs on |Acc<|, for example its fold operator:%
\footnote{This operator proves the strong induction principle on accessible natural numbers.}
\begin{code}
foldAcc< :  {P : ℕ → Set} → (∀ {n} → (∀ m → m < n → P m) → P n) →
            ∀ {n} → Acc< n → P n
foldAcc< p (acc accs) = p (λ m lt → foldAcc< p (accs m lt))
\end{code}
However, the point of using encoded datatypes such as |μ Acc<D| is that we do not have to write |foldAcc<| ourselves but can simply derive it as an instantiation of a generic grogram parametrised by a datatype description.
One useful class of generic programs is ($F$-)algebras (where the functor~$F$ is always some base functor |⟦ D ⟧ᶜˢ| in this paper), whose type is defined by
\begin{code}
Alg : ConDs I → (I → Set) → Set
Alg D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i
\end{code}
An algebra of type |Alg D X| is the non-recursive part of a fold of type |∀ {i} → μ D i → X i|, while the recursive part can be expressed by this generic |fold| operator%
\footnote{There are safer ways to make Agda see that |fold| is terminating than using the \textsc{terminating} pragma, but they are not important for our purposes since we will not use |fold| later in the paper.}
\begin{code}
{-# TERMINATING #-}
fold : (D : ConDs I) → Alg D X → ∀ {i} → μ D i → X i
fold D f = f ∘ fmapᶜˢ D (fold D f) ∘ decon
\end{code}
where |fmapᶜˢ D| is the functorial map for |⟦ D ⟧ᶜˢ| (which we will define shortly), and |decon| is the inverse of |con|:
\begin{code}
decon : ∀ {i} → μ D i → ⟦ D ⟧ᶜˢ (μ D) i
decon (con ds) = ds
\end{code}
For example, the (parametrised) algebra for |foldAcc<| is
\begin{code}
foldAcc<Alg :  {P : ℕ → Set} → (∀ {n} → (∀ m → m < n → P m) → P n) →
               Alg Acc<D P
foldAcc<Alg p (inl (_ , ps , refl)) = p ps
\end{code}
(which will be an instantiation of a generic program in \Cref{sec:fold-and-induction-operators} and will not need to be written manually), and we obtain |foldAcc<| by applying the |fold| operator to the algebra:
\begin{code}
foldAcc< :  {P : ℕ → Set} → (∀ {n} → (∀ m → m < n → P m) → P n) →
            ∀ {n} → Acc< n → P n
foldAcc< p = fold Acc<D (foldAcc<Alg p)
\end{code}
It is instructive to take a closer look at the functorial map because it is a typical generic program, which is parametrised by a datatype description and analyses the description layer by layer:
\begin{code}
fmapᶜˢ : (D : ConDs I) → (∀ {i} → X i → Y i) → ∀ {i} → ⟦ D ⟧ᶜˢ X i → ⟦ D ⟧ᶜˢ Y i
fmapᶜˢ (D ∷ Ds) f (inl  xs) = inl  (fmapᶜ   D   f xs)
fmapᶜˢ (D ∷ Ds) f (inr  xs) = inr  (fmapᶜˢ  Ds  f xs)

fmapᶜ : (D : ConD I) → (∀ {i} → X i → Y i) → ∀ {i} → ⟦ D ⟧ᶜ X i → ⟦ D ⟧ᶜ Y i
fmapᶜ (ι i     ) f eq             = eq
fmapᶜ (σ A  D  ) f (a ,   xs   )  = a , fmapᶜ (D a) f xs
fmapᶜ (ρ D  E  ) f (xs ,  xs'  )  = fmapʳ D f xs , fmapᶜ E f xs'

fmapʳ : (D : RecD I) → (∀ {i} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ (ι i    ) f x   = f x
fmapʳ (π A D  ) f xs  = λ a → fmapʳ (D a) f (xs a)
\end{code}
The functorial map should apply a given function~|f| to all the recursive positions in a sum-of-products structure while leaving everything else intact, so |fmapᶜˢ| keeps the choices of |inl| or |inr|, |fmapᶜ| keeps the |σ|-fields and |ι|-equalities, and finally |fmapʳ| applies~|f| to its input of type |⟦ D ⟧ʳ X| ---which is (in general) a function--- pointwise.

Being able to treat folds generically means that we are able to write generic programs whose types have the form |∀ {i} → μ D i → X i|, but this is not enough when, for example, we want to write generic proofs by induction on |d : μ D i| and the result types depend on~|d|, in which case the types of the proofs take the more complex form |∀ {i} (d : μ D i) → P d| for some |P : ∀ {i} → μ D i → Set|.
Our library thus provides another set of definitions for treating induction generically.
The treatment of induction is largely standard and analogous to the treatment of folds, however, so we omit the technical details from the presentation.

\section{Datatype Parameters and Universe Polymorphism}

\section{Connecting Generic and Native Entities}

\section{Establishing Connections via Metaprogramming}

\todo[inline]{Introduction to reflection in Agda}

\section{Examples}

\subsection{Fold and Induction Operators}
\label{sec:fold-and-induction-operators}

\todo[inline]{In contrast to an untyped approach, the datatype-generic version also proves that the arguments to the fold operator do constitute an algebra.}

\begin{code}
FoldOpTᶜ : (D : ConD I cb) → (I → Set ℓ) → Set (max-π cb ⊔ max-σ cb ⊔ ℓ)
FoldOpTᶜ (ι  i     ) X = X i
FoldOpTᶜ (σ  A  D  ) X = (a : A) → FoldOpTᶜ (D a) X
FoldOpTᶜ (ρ  D  E  ) X = ⟦ D ⟧ʳ X → FoldOpTᶜ E X
\end{code}

\begin{code}
FoldOpTelᶜˢ :  (D : ConDs I cbs) → (I → Set ℓ) →
               Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
FoldOpTelᶜˢ []        X = []
FoldOpTelᶜˢ (D ∷ Ds)  X = [ _ ∶ FoldOpTᶜ D X ] FoldOpTelᶜˢ Ds X
\end{code}

\begin{code}
fold-opᶜ : (D : ConD I cb) → FoldOpTᶜ D X → Algᶜ D X
fold-opᶜ (ι  i     ) f refl           = f
fold-opᶜ (σ  A  D  ) f (a   , xs   )  = fold-opᶜ (  D a)  (f  a   ) xs
fold-opᶜ (ρ  D  E  ) f (xs  , xs'  )  = fold-opᶜ    E     (f  xs  ) xs'
\end{code}

\begin{code}
fold-opᶜˢ : (D : ConDs I cbs) → ⟦ FoldOpTelᶜˢ D X ⟧ᵗ → Algᶜˢ D X
fold-opᶜˢ (D ∷ Ds) (f , fs) (inl  xs) = fold-opᶜ   D   f   xs
fold-opᶜˢ (D ∷ Ds) (f , fs) (inr  xs) = fold-opᶜˢ  Ds  fs  xs
\end{code}

\begin{code}
fold-operator : DataC D N → FoldP
fold-operator {D} C = record
  {  Conv     =  C
  ;  #levels  =  suc (#levels D)
  ;  level    =  snd
  ;  Param    =  λ (ℓ , ℓs) → let Dᵖ = applyL D ℓs in
                   [[ ps ∶ Param Dᵖ ]] [ X ∶ Curriedᵗ true (Index Dᵖ ps) (λ _ → Set ℓ) ]
                   FoldOpTelᶜˢ (applyP Dᵖ ps) (uncurryᵗ X)
  ;  param    =  fst
  ;  Carrier  =  λ _ (_ , X , _) → uncurryᵗ X
  ;  algebra  =  λ (ps , _ , args) → fold-opᶜˢ (applyP (applyL D _) ps) args }
\end{code}

\subsection{Algebraic Ornamentation}

\subsection{Predicates on Simple Containers}

\section{Practical Issues}

\subsection{Portability}
\todo[inline]{Address the statement that our development is not specific to Agda.
So, what features do we need to implement?}
\todo[inline]{Axiom K is used for ornaments but this axiom is not generally desirable especially for homotopy type theory.
This seemingly conflicting requirement in fact originates in the false belief that only one identity type is allowed in a type theory.
Indeed, it is possible to have more than one identity type with different strength.
For example, the two-level type theory proposed by \citet{Capriotti2017} consists of a strict equality (satisfying the axiom K) and a weak equality compatible with the homotopy-theoretic interpretation.
Agda has an experimental option \texttt{--two-level} in the cubical mode which introduces additional universes \texttt{SSet}.
This extra sort of universes will make our library portable to proof assistants based on homotopy type theory.
(A bit of experiments should be performed to testify.)
}
\todo[inline]{Elaborator reflection}

\subsection{Naming, Visibility, and Order of Arguments}

\todo[inline]{Chosen by generic programs, dependency analysis, refactoring tools, heuristics, machine learning; interaction with generalised variables; the wrapper trick retains all these possibilities}

\subsection{Normalisation and Printing}

\todo[inline]{`type preservation', optimisation, name scope and qualification}

\subsection{Interactive User Interface}

\subsection{Automatic Resolution of Arguments to Generic Programs}

\todo[inline]{Type classes, instance arguments}
\section{Discussion}

\paragraph{Simply Typed DGP}

\todo[inline]{\citet{Gibbons-DGP}.
The Haskell programmer produces recursive function definitions~\citep{de-Vries-true-SoP}.
We adopt the approach where generic function representations are non-recursive and then weaved into recursive definitions.
Efficiency problem due to conversion between generic and native representations (see below).
Deriving new datatypes?
Put our work within the spectrum of generic libraries?~\citep{Magalhaes-GGP}}

\paragraph{Dependently Typed DGP}

\todo[inline]{\citet{Altenkirch-GP-within-DTP}; contrast with single generic representation offered by the generic |μ|, |fold|, and |induction| operators, which avoid code duplication/explosion but (potentially?) sacrificing efficiency~\citep{Allais-n-ary-functions}; interoperability between generic libraries and native entities~\citep{McBride-pivotal, Allais-binding-syntax-universe-JFP}}

\paragraph{Ornaments}
\todo[inline]{\citet{McBride-ornaments}; porting some constructions from \citet{Ko-OAOAOO}; more experimental developments~\citep{Ko-OrnJFP, Dagand-functional-ornaments}; theory and developments about function transportation in simply typed settings~\cite{Williams-principle-ornamentation, Williams-ornaments-in-practice}; realistic dependently typed application and automated synthesis of ornaments~\citep{Ringer-ornaments-Coq}}

\paragraph{Metaprogramming}

\todo[inline]{\citet{Christiansen-elaborator-reflection}: type checking and inference in metaprogramming; respond to their comments about datatype-generic programming (untyped vs typed metaprogramming)}

\todo[inline]{Object-level binder-manipulating techniques~\citep{Chen-Mtac-Agda}}

\todo[inline]{\citet{Pickering-staged-SoP, Yallop-staged-generic-programming, Jones-partial-evaluation, de-Vries-masters-thesis}; partial evaluation is more programmer-friendly than staging, and elaborator reflection provides, to some extent, the ability to do partial evaluation}

\todo[inline]{One more step towards practical `type theory in type theory'~\citep{Chapman-type-theory-should-eat-itself} (not just theoretically interesting), although our encoding is `shallow'}

\todo[inline]{Typed metaprogramming~\citep{Xie-Typed-Template-Haskell, Jang-Moebius, Kiselyov-MetaOCaml, Davies-modal-staged-computation}}

\paragraph{Universe polymorphism}

\todo[inline]{A practical application and motivation~\citep{Kovacs-universe-hierarchies} (not just theoretically interesting); generic level quantification; no subject rejection; universe-polymorphic definitions not polymorphic enough (e.g., |Σ|-types); more expressive universes}

\todo[inline]{\citet{Chapman-levitation} propose a more radical redesign of type theory where datatype definitions are first-class, but the theory is still at an early stage of development and lacks an implementation; our proposal is more practical and serves as a platform for the development of mature datatype-generic libraries, which can be ported to new platforms when ready}

\section{Conclusion}

\todo[inline]{From the angle of datatype-generic programming, the generic constructions should work on native datatypes and functions for maximum interoperability with language facilities and other libraries, and the gap between generic and native entities can be filled straightforwardly with (powerful enough) metaprogramming.
From the angle of metaprogramming, one way to offer better correctness guarantees about the meta-level constructions is to introduce types, and (dependently typed) datatype-generic programming already provides a working solution for typing a good range of the constructions.
Each of the two programming disciplines works nicely as the other's natural extension.}

\todo[inline]{The native world as the common playground of multiple generic libraries}

\todo[inline]{Suggestions for the future evolution of Agda or the design of new languages with elaborator reflection}

\todo[inline]{Our experience with untyped metaprogramming was painful, especially in contrast to the experience with datatype-generic programming (a form of typed metaprogramming, as we argued above)}

\todo[inline]{Provide a practically relevant application whose foundation the theorists can investigate and formalise}

%%
%% The acknowledgments section is defined using the "acks" environment
%% (and NOT an unnumbered section). This ensures the proper
%% identification of the section in the article metadata, and the
%% consistent spelling of the heading.
\begin{acks}
The work is supported by the \grantsponsor{MOST}{Ministry of Science and Technology of Taiwan}{https://www.most.gov.tw/} under grant \grantnum{MOST}{MOST 109-2222-E-001-002-MY3}.
\end{acks}

%%
%% The next two lines define the bibliography style to be used, and
%% the bibliography file.
\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}

%%
%% If your work has an appendix, this is the place to put it.
%\appendix
%
%\section{Research Methods}

\end{document}
