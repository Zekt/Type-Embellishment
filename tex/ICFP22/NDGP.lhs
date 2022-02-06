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

\usepackage[hyperpageref]{backref} % this may be removed

\usepackage[euler]{textgreek}

\usepackage[capitalise]{cleveref}

\usepackage[color=yellow,textsize=scriptsize]{todonotes}
\setlength{\marginparwidth}{1.25cm}

\newcommand{\LT}[1]{\todo[author=LT,inline,color=green!40]{{#1}}}
\newcommand{\Josh}[1]{\todo[author=Josh,inline]{{#1}}}
\newcommand{\Viktor}[1]{\todo[author=Viktor,inline,color=orange]{{#1}}}

\newenvironment{halfcol}{\begin{minipage}{.45\textwidth}\setlength{\mathindent}{0em}}{\end{minipage}}

\newcommand{\arXiv}[1]{\href{http://arxiv.org/abs/#1}{arXiv:\nolinkurl{#1}}}

\let\Bbbk\relax
%include agda.fmt

\setlength{\mathindent}{.5\parindent}
%\renewcommand{\Varid}{\texttt}
%\renewcommand{\Conid}{\texttt}
\newcommand{\iden}{\mathit}

%format syntax = "\Keyword{syntax}"
%format pattern = "\Keyword{pattern}"

%format == = "\mathop="
%format _ = "\char95"
%format : = "\mathop:"
%format → = "\mathop\to"
%format [ = "[\kern-2pt"
%format Σ[ = Σ [
%format σ[ = σ [
%format π[ = π [
%format ] = "\kern-2pt]"
%format [[ = "|\kern-1.5pt[\kern-2pt"
%format ]] = "\kern-2pt]\kern-1.5pt|"
%format ⦃ = "\{\kern-2.75pt\{\kern-2pt"
%format ⦄ = "\kern-2pt\}\kern-2.75pt\}"
%format ⟦ = "⟦\kern-1.5pt"
%format ⟧ = "\kern-1.5pt⟧"
%format × = "\mathop\times"
%format ⊎ = "\mathop\uplus"
%format ≡ = "\mathop\equiv"
%format ∘ = "\mathop\circ"
%format ⊔ = "\mathop\sqcup"
%format ⊑ = "\mathop\sqsubseteq"
%format ^ = "\kern-1.5pt\text{\char94}\kern-1.5pt"
%format ++ = "{+}\kern-3pt{+}"
%format _++_ = _ ++ _

%format Setω = Set "_{\text\textomega}"
%format Acc< = Acc "_<"
%format Acc<D = Acc "_<\Conid{D}"
%format foldAcc< = fold Acc<
%format foldAcc<Alg = foldAcc< Alg
%format μ = "\text\textmugreek"
%format CurriedL = Curried "_{\Conid L}"

%format ᵗ = "_{\Conid T}"
%format ⟦_⟧ᵗ = ⟦_⟧ ᵗ
%format ⟧ᵗ = ⟧ ᵗ
%format Curriedᵗ = Curried ᵗ
%format curryᵗ = curry ᵗ
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

%format ᵈ = "_{\Conid D}"
%format ⟦_⟧ᵈ = ⟦_⟧ ᵈ
%format ⟧ᵈ = ⟧ ᵈ
%format fmapᵈ = fmap ᵈ

%format ⁱ = "_{\Conid I}"

%format A = "\iden A"
%format C = "\iden C"
%format D = "\iden D"
%format E = "\iden E"
%format F = "\iden F"
%format Ds = "\iden{Ds}"
%format I = "\iden I"
%format N = "\iden N"
%format P = "\iden P"
%format PAcc = "\iden P_{" Acc "}"
%format R = "\iden R"
%format T = "\iden T"
%format U = "\iden U"
%format X = "\iden X"
%format Y = "\iden Y"
%format a = "\iden a"
%format as = "\iden{as}"
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
%format is = "\iden{is}"
%format j = "\iden j"
%format ℓ' = "\iden{" ℓ "^\prime}"
%format ℓ'' = "\iden{" ℓ "^{\prime\prime}}"
%format ℓᵈ = "\iden{" ℓ "_D}"
%format ℓⁱ = "\iden{" ℓ "_I}"
%format ℓᵖ = "\iden{" ℓ "_P}"
%format ℓˣ = "\iden{" ℓ "_X}"
%format ℓʸ = "\iden{" ℓ "_Y}"
%format ℓs = "\iden{" ℓ "\kern-1pt s}"
%format lt = "\iden{lt}"
%format m = "\iden m"
%format n = "\iden n"
%format ns = "\iden{ns}"
%format p = "\iden p"
%format ps = "\iden{ps}"
%format rb = "\iden{rb}"
%format t = "\iden t"
%format u = "\iden u"
%format x = "\iden x"
%format xs = "\iden{xs}"
%format xs' = "\iden{xs^\prime}"
%format y = "\iden y"

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
\orcid{0000-0002-7656-6225}
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
\todo[inline]{Datatype-generic programming is typed metaprogramming over datatypes.}
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

\Josh{Problems with the current state of dependently typed DGP (the kind of DGP discussed in this paper; no qualification thereafter)}

\Josh{What we really want from generic libraries, using lists and vectors as familiar examples: we want to generate functions for native datatypes as if they are hand-written so that they are efficient to compute (no back-and-forth representation conversions), easy to reason about (again without the conversions and no excessive abstraction), and can fully benefit from whatever language facilities there are (e.g., Agda's interactive features and compiler optimisations); moreover, we want to generate not only, for example, fold operators but also their theorems such as fold fusion; particularly important in a dependently typed setting is the ability to generate new \emph{datatypes}, and then their functions and properties (e.g., algebraic ornamentation and the associated isomorphism)}

\Josh{There have been many attempts at removing overheads by compiler optimisation, but this is not enough for dependently typed programming, where programs may appear in later types and be reasoned about (and haven’t been processed by the compiler at all).
And compiler optimisations need to be fine-tuned to produce what we want; why not just generate what we want in the first place?}

\Josh{Staging? No! Enter elaborator reflection.}

\Josh{Some actual demo}

\todo[inline]{
Contributions:

$\bullet$ Encoding of universe-polymorphic and parametrised inductive families (precise calculation of universe levels)

$\bullet$ Better interoperability with native datatypes and functions (generating new native datatypes and functions, and connecting with existing ones for which generic constructions are specialised)

$\bullet$ A new use case of elaborator reflection where traditional datatype-generic programs are simply normalised to yield native programs (and do not need more radical adaptations like staging)

$\bullet$ Simpler and less error-prone `object-level' binder-manipulating techniques with (Agda's) elaborator reflection (bypassing the manipulation of de Bruijn indices; a tutorial for Agda's reflection mechanism)}

\section{A Recap of Datatype-Generic Programming}
\label{sec:recap}

\Josh{3 pages}

\Josh{A recap of the standard approach (except for some minor details), also serving as an outline}

\Josh{Say somewhere `datatype' means `inductive families' in this paper}

\Josh{Typesetting conventions (in a footnote)}

\LT{Cite \cite{Dybjer1994,Dybjer1999} somewhere for the definition of inductive families.}
\LT{Use \emph{(non)-inductive part/premise} instead of recursive part/premise as suggested by~\citet{Dybjer1999}}
We start from a recap of standard datatype-generic programming (DGP) within a dependently typed setting, but use a three-layered encoding of datatypes that more closely follows the structure of a native datatype definition, which has a list of constructors made up of a series of fields, some of which can be potentially higher-order recursive occurrences of the datatype being defined.%
\footnote{This choice of layered structure has also been adopted elsewhere, for example by \citet{de-Vries-true-SoP}.}
As a small example that covers all the essential components of datatype definitions (in particular higher-order recursive occurrence), consider this datatype |Acc<| of accessibility proofs:%
\footnote{Although the meaning of |Acc<| is not important here, a quick explanation is that a proof |acc as : Acc< n| that |n|~is accessible captures the fact that any descending chain from~|n| with respect to~|_<_| is finite: if we deconstruct the proof by applying |as| to some~|m| such that |m < n|, we will get a proof of |Acc< m|, which we can keep deconstructing, but can only do so a finite number of times because |Acc<| is an inductive datatype.}
\begin{code}
data Acc< : ℕ → Set where
  acc : {n : ℕ} (as : (m : ℕ) (lt : m < n) → Acc< m) → Acc< n
\end{code}
The first layer is the list of constructors, which for |Acc<| consists of only |acc|;
the type of |acc| has two fields |n|~and |as|, which constitute the second layer;
the type of the field |as| is described in the third layer as it ends with the recursive occurrence |Acc< m|, in front of which there are function arguments |m|~and~|lt| (making the recursive occurrence higher-order).
Corresponding to the three layers, we use three datatypes of \emph{descriptions} ---all parametrised by an index type~|I|--- to encode datatype definitions,
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
Different from ordinary lists, in the case of |σ A D| a new variable of type~|A| is brought into the context of~|D| (for example, |n|~appears in the type of |as|); this is done by making~|D| a function with an argument of type~|A|, using the host language's function space to extend the context --- we will continue to use this technique heavily in \cref{sec:parameters}.\todo{forward reference about detecting abuses}%
\footnote{The expressive power of the host language's function space has been better utilised in the DGP literature (for example by \citet[Section~2.1]{McBride-ornaments}), but we will refrain from abusing the function space in the descriptions for tasks beyond context extension, and it will be easy to detect abuses at the meta-level.}
Moreover, the~|ι| at the end of a |ConD I| should specify the index targeted by the constructor (e.g., the final~|n| in the type of |acc|).
Inhabitants of |RecD I| use the same structure to describe dependent function types ending with a recursive occurrence.

To make descriptions slightly easier to write and read, we can introduce a couple of syntax declarations for the binders:
\begin{code}
syntax π  A (λ a → D) = π[ a ∶ A ] D
syntax σ  A (λ a → D) = σ[ a ∶ A ] D
\end{code}
For example, |Acc<D| can be rewritten as |(σ[ n ∶ ℕ ] ρ (π[ m ∶ ℕ ] π[ lt ∶ m < n ] ι m) (ι n)) ∷ []|.

In the standard recipe, a description |D : ConDs I| is converted to a type family |μ D : I → Set| by the operator~|μ| which takes the least fixed point of the base functor |⟦ D ⟧ᶜˢ : (I → Set) → (I → Set)|:
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
pattern acc {n} as = con (inl (n , as , refl))
\end{code}
where the arguments |n|~and |as| of |acc| are collected in a tuple, which is injected into a sum type by |inl|, and finally wrapped up with |con| as an inhabitant of |μ Acc<D n|.
The equality proof |refl| at the end of the tuple needs a bit more explanation: in the type of |con|, the index~|i| is universally quantified, which seems to suggest that we could construct inhabitants of |μ D i| for any~|i|, but the equality proof forces~|i| to be~|n|, the index targeted by |acc|.
The sum and product structures are defined respectively on the first two layers of descriptions:
\begin{code}
⟦_⟧ᶜˢ : ConDs I → (I → Set) → (I → Set)
⟦ []      ⟧ᶜˢ  X i = ⊥
⟦ D ∷ Ds  ⟧ᶜˢ  X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i

⟦_⟧ᶜ : ConD I → (I → Set) → (I → Set)
⟦ ι j     ⟧ᶜ   X i = i ≡ j
⟦ σ A  D  ⟧ᶜ   X i = Σ[ a ∶ A ] ⟦ D a ⟧ᶜ X i
⟦ ρ D  E  ⟧ᶜ   X i = ⟦ D ⟧ʳ X × ⟦ E ⟧ᶜ X i
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
foldAcc< p (acc as) = p (λ m lt → foldAcc< p (as m lt))
\end{code}
However, the point of using described datatypes such as |μ Acc<D| is that we do not have to write |foldAcc<| ourselves but can simply derive it as an instantiation of a generic grogram parametrised by a description.
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
fold D f (con ds) = f (fmapᶜˢ D (fold D f) ds)
\end{code}
where |fmapᶜˢ D| is the functorial map for |⟦ D ⟧ᶜˢ| (which we will define shortly).
For example, the (parametrised) algebra for |foldAcc<| is
\begin{code}
foldAcc<Alg :  {P : ℕ → Set} → (∀ {n} → (∀ m → m < n → P m) → P n) →
               Alg Acc<D P
foldAcc<Alg p (inl (_ , ps , refl)) = p ps
\end{code}
(which will be an instantiation of a generic program in \cref{sec:fold-and-induction-operators} and will not need to be written manually), and we obtain |foldAcc<| by applying the |fold| operator to the algebra:
\begin{code}
foldAcc< :  {P : ℕ → Set} → (∀ {n} → (∀ m → m < n → P m) → P n) →
            ∀ {n} → Acc< n → P n
foldAcc< p = fold Acc<D (foldAcc<Alg p)
\end{code}
It is instructive to take a closer look at the functorial map because it is a typical generic program, which is parametrised by a description and analyses the description layer by layer:
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

Being able to treat folds generically means that we are able to write generic programs whose types have the form |∀ {i} → μ D i → X i|, but this is not enough when, for example, we want to prove generic theorems by induction on |d : μ D i|, in which case the types take the more complex form |∀ {i} (d : μ D i) → P d| (where |P : ∀ {i} → μ D i → Set|).
Our library thus provides another set of definitions for treating induction generically.
The treatment of induction is largely standard and analogous to the treatment of folds, however, so we omit the technical details of generic induction from the presentation.

\section{Datatype Parameters and Universe Polymorphism}
\label{sec:parameters}

The datatype descriptions presented in the previous section missed a couple of important features --- it was probably tempting to generalise |Acc<| to a version parametrised by a type~|A| and a binary relation~|R| on~|A|, and moreover, by the levels of the universes in which |A|~and~|R| reside:
\begin{code}
data Acc {ℓ ℓ' : Level} {A : Set ℓ} (R : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  acc : {x : A} → ((y : A) → R y x → Acc R y) → Acc R x
\end{code}
We ought to extend our datatype descriptions to express this kind of parametric and universe-polymorphic datatypes as they are prevalent in Agda codebases.
Conceptually this is straightforward: parameters are just variables in the context which can be referred to by the index type, datatype level, and constructor types, and we know an easy way to extend the context --- just use the host language's function space.
So a parametrised and universe-polymorphic datatype could be described by a parameter type~|P|, a parametrised index type |I : (p : P) → Set (ℓⁱ p)| (where |ℓⁱ : P → Level|), a parametrised datatype level |ℓᵈ : P → Level|, and a parametrised list of constructor descriptions |(p : P) → ConDs (I p)| (where |ConDs| needs to be enriched with levels, which we will do in \cref{sec:universe-polymorphic-descriptions}).
For example, we could describe |Acc| with
\begin{code}
P  = Σ[ ℓ ∶ Level ] Σ[ ℓ' ∶ Level ] Σ[ A ∶ Set ℓ ] (A → A → Set ℓ')
I  = λ (_ , _ , A , _) → A {-"\qquad"-} ℓⁱ = λ (ℓ , _) → ℓ {-"\qquad"-} ℓᵈ = λ (ℓ , ℓ' , _) → ℓ ⊔ ℓ'
\end{code}
and a parametrised description that looks like |Acc<D|.

\subsection{Level Parameters}
\label{sec:level-parameters}

Unfortunately, we have already bumped into the limitation of Agda's current design of universe polymorphism, where only finite levels of type |Level| can be dealt with uniformly (via quantification over |Level|).
Depending on whether a described datatype is universe-polymorphic or not, its parameter type may reside in a universe with a finite or infinite level: a non-universe-polymorphic parameter type, for example |Σ[ A ∶ Set ] (A → A → Set)|, resides in |Set|, which has a finite level, whereas the parameter type~|P| defined above for |Acc| ---call it |PAcc| for ease of reference--- cannot have type |Set ℓᵖ| for any |ℓᵖ : Level| because the type of one of its components is |Set ℓ| where |ℓ|~can be arbitrarily large, so the type/kind of~|PAcc| has to be |Setω|, the first universe with an infinite level.
The mismatch between the range of levels we need to handle and the limited power of level quantification creates a load of problems, one of which is that the usual universe-polymorphic |Σ|-type former is not enough for defining~|PAcc| (and we will see one more at the end of \cref{sec:telescopes}).

To avoid some of the problems, we make a simplifying assumption, which holds for common universe-polymorphic datatypes: we assume that there is a list of level parameters separate from other parameters, and universe-polymorphic constructs refer to these level parameters only.
More formally, to describe a datatype, we start with a number |n : ℕ| of level parameters, from which we can compute a type |Level ^ n| of tuples of |n|~levels as defined by
\begin{code}
_^_ : Set → ℕ → Set
A ^    zero    = ⊤
A ^ (  suc n)  = A × (A ^ n)
\end{code}
Parameterised by |ℓs : Level ^ n|, the rest of the description can be written more succinctly as |λ ℓs → (ℓᵈ , ℓᵖ , ℓⁱ , P , I , D)| where |ℓᵈ|~is the datatype level, |P : Set ℓᵖ| the parameter type, |I : P → Set ℓⁱ| the parametrised index type, and |D : (p : P) → ConDs (I p)| the parametrised list of constructors.
Note that, given~|ℓs|, the type~|P| (which is |Σ[ A ∶ Set ℓ ] (A → A → Set ℓ')| in the case of |Acc|) always has a finite level now.
We will pack all these data in two record types in \cref{sec:DataD}, after we make some more necessary refinements.

\subsection{Telescopes}
\label{sec:telescopes}

At some point we will need to convert a description to a datatype definition, and it would be unsatisfactory in practice if the parameter and index types in the datatype definition were not in the conventional curried form.
When currying, the encoding of multiple types in one nested |Σ|-type is ambiguous --- how do we know whether a |Σ|-type is supposed to be interpreted as two types, with the latter depending on the former, or just one type?
A natural solution is to use telescopes~\citep{de-Bruijn-telescopes} to represent lists of parameter or index types:
\begin{code}
mutual

  data Tel : Level → Setω where
    []     : Tel lzero
    _∷_    : (A : Set  ℓ) (T  : A → Tel ℓ') → Tel (ℓ ⊔ ℓ')
    _++_   : (T : Tel  ℓ) (U  : ⟦ T ⟧ᵗ → Tel ℓ') → Tel (ℓ ⊔ ℓ')

  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ []       ⟧ᵗ = ⊤
  ⟦ A ∷   T  ⟧ᵗ = Σ[ a ∶ A ] ⟦ T a ⟧ᵗ
  ⟦ T ++  U  ⟧ᵗ = Σ[ t ∶ ⟦ T ⟧ᵗ ] ⟦ U t ⟧ᵗ
\end{code}
Again we use the host language's function space to bring variables of the types in the front of a telescope into the context of the rest of the telescope.
Besides the usual cons constructor `|∷|', we also include telescope-appending as a constructor `|++|' (which requires induction-recursion to define), making our telescopes tree-shaped; the reason will be clear when we reach \cref{sec:examples}.
The index~|ℓ| in the type |Tel ℓ| of a telescope~|T| is the maximum level appearing in~|T|.
This level is important as it is the universe level of the type |⟦ T ⟧ᵗ|, which is a nested |Σ|-type inhabited by tuples whose components have the types in~|T|.
%More subtly, the indexing also precludes overly universe-polymorphic telescopes like |Level ∷ (λ ℓ → Set ℓ ∷ (λ _ → []))|, since in a cons telescope (and similarly in an appended telescope), the maximum level~|ℓ'| in the tail has to be determined independently from the |A|-typed value in the context.

A couple of syntax declarations will make telescopes slightly easier to write and read:
\begin{code}
syntax _∷_   A  (λ x  → T  ) = {-"\kern1.25pt"-}[  x                ∶ A  ]   T
syntax _++_  T  (λ t  → U  ) = [[                  {-"\kern1pt"-}t  ∶ T  ]]  U
\end{code}
For example, the parameters of |Acc| can be represented as |[ A ∶ Set ℓ ] [ R ∶ (A → A → Tel ℓ') ] []| instead of |Set ℓ ∷ (λ A → (A → A → Set ℓ') ∷ (λ R → []))|.

From a telescope~|T| it is straightforward to compute a curried function type |Curriedᵗ T X| which has arguments with the types in~|T|, and ends with a given type |X : ⟦ T ⟧ᵗ → Set ℓ'| that can refer to all the arguments (collectively represented as a tuple of type |⟦ T ⟧ᵗ|):
\begin{code}
Curriedᵗ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ []          X = X tt
Curriedᵗ (A  ∷   T)  X = (a : A) → Curriedᵗ (T a) (curry X a)
Curriedᵗ (T  ++  U)  X = Curriedᵗ T (λ t → Curriedᵗ (U t) (λ u → X (t , u)))
\end{code}
It is also straightforward to convert between this curried function type and its uncurried counterpart with the functions
\begin{code}
curryᵗ    : ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ T X
uncurryᵗ  : Curriedᵗ T X → ((t : ⟦ T ⟧ᵗ) → X t)
\end{code}
whose definitions are omitted.
With these, we will be able to compute curried forms of parameters and indices when they appear in types (e.g., the type of the fold operator of |Acc|).
Incidentally, if we attempt a similar construction for |Level ^ n| (which can be viewed as a kind of specialised telescope) to produce curried forms of level parameters as well,
\begin{code}
CurriedL : (n : ℕ) {f : Level ^ n → Level} → ((ℓs : Level ^ n) → Set (f ℓs)) → Set ?
CurriedL    zero    X = X tt
CurriedL (  suc n)  X = (ℓ : Level) → CurriedL n (λ ℓs → X (ℓ , ℓs))
\end{code}
we will not be able to fill in the hole `?' since it should be a finite level when |n|~is zero (meaning that there is no level quantification), or~|ω| when |n|~is non-zero, going beyond the current capabilities of Agda's universe polymorphism.
To deal with level parameters, we will resort to metaprogramming techniques in \cref{sec:reflection}.

\subsection{Universe-Polymorphic Descriptions}
\label{sec:universe-polymorphic-descriptions}

It remains to adapt the description datatypes |ConDs|, |ConD|, and |RecD| from \cref{sec:recap} for universe polymorphism.
A first instinct might be copying what has been done for |Tel| (as constructor descriptions can be viewed as a slightly more complex kind of telescopes), enriching the |Set|-arguments to |Set ℓ| and perhaps indexing the datatypes with the maximum level, but this is not enough.
Consider how we should enrich the type of a base functor |⟦ D ⟧ᶜˢ|:
One place where we use the base functor is the type of an algebra |{i : I} → ⟦ D ⟧ᶜˢ X i → X i| where |X : I → Set ℓ|~is the result type, which can have any level depending on what the algebra computes, so |ℓ|~should be universally quantified in the type of |⟦ D ⟧ᶜˢ|.
But then, what should the level of the type |⟦ D ⟧ᶜˢ X i| be?
This level ---call it~|ℓ'|--- needs to be computed from |ℓ|~and the structure of~|D|, and the computation is non-trivial --- for example, if |D|~is |[]|, then |⟦ D ⟧ᶜˢ X i = ⊥|, in which case |ℓ'|~is simply |lzero|; if |D|~is non-empty, then |ℓ|~may or may not appear in~|ℓ'|, depending on whether there is a constructor with a |ρ|-field or not.
More generally, the need for non-trivial level computation naturally arises if we take universe polymorphism seriously, for example when we compute a new datatype from an old one, and need to specify the new levels in terms of the old ones --- \cref{sec:algebraic-ornamentation,sec:simple-containers} will give some such examples.

To allow level computation to be performed as freely as possible, we choose to index the description datatypes with as much useful information as possible: the index in the type of a description is a list which not only contains the levels of the fields but also encodes the description constructors used.
Starting from the simplest |RecD| datatype, we index it with |RecB = List Level|, recording the levels of the |π|-fields:
\begin{code}
data RecD (I : Set ℓⁱ) : RecB → Setω where
  ι  : (i : I) → RecD I []
  π  : (A : Set ℓ) (D : A → RecD I rb) → RecD I (ℓ ∷ rb)
\end{code}
For |ConD|, the index type is |ConB = List (Level ⊎ RecB)|, whose element sum type is used to record whether a field is |σ|~or~|ρ|:
\begin{code}
data ConD (I : Set ℓⁱ) : ConB → Setω where
  ι  : (i : I) → ConD I []
  σ  : (A : Set ℓ) (D : A → ConD I cb) → ConD I (inl ℓ ∷ cb)
  ρ  : (D : RecD I rb) (E : ConD I cb) → ConD I (inr rb ∷ cb)
\end{code}
Finally, |ConDs| is indexed with |ConBs = List ConB|, collecting information from all the constructors into one list:
\begin{code}
data ConDs (I : Set ℓⁱ) : ConBs → Setω where
  []   : ConDs I []
  _∷_  : (D : ConD I cb) (Ds : ConDs I cbs) → ConDs I (cb ∷ cbs)
\end{code}

With some helper functions, which constitute a small domain-specific language for level computation, we can now specify the output level of |⟦_⟧ᶜˢ|:
\begin{code}
⟦_⟧ᶜˢ :  {I : Set ℓⁱ} → ConDs I cbs → (I → Set ℓ) →
         (I → Set (  maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔
                     maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs))
⟦ []      ⟧ᶜˢ X i = ⊥
⟦ D ∷ Ds  ⟧ᶜˢ X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i
\end{code}
In prose, the output level is the maximum among the maximum level of the |π|-fields, the maximum level of the |σ|-fields, |ℓ| if the description has a |ρ|-field, and |ℓⁱ| if the description has a constructor.
For our library, the approach works surprisingly well (even though the level expressions may look somewhat scary sometimes): we are able to write fully universe-polymorphic types while keeping almost all of the programs as they were --- for example, the universe-polymorphic program of |⟦_⟧ᶜˢ| is exactly the same as the non-universe-polymorphic one in \cref{sec:recap}.
To see how the universe-polymorphic version of |⟦_⟧ᶜˢ| is type-checked, we need to show a couple of definitions:
\begin{code}
maxMap : (A → Level) → List A → Level
maxMap f []        = lzero
maxMap f (a ∷ as)  = f a ⊔ maxMap f as

hasCon? : Level → ConBs → Level
hasCon? ℓ = maxMap (λ _ → ℓ)
\end{code}
It is easy to see that the output level in the |[]|~case is |lzero|, which is indeed the level of~|⊥|.
In the |D ∷ Ds| case where |D : ConD I cb| and |Ds : ConDs I cbs|, the output level expands to
\begin{code}
max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb ⊔ ℓⁱ ⊔
maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs
\end{code}
where the first line is the level of |⟦ D ⟧ᶜ X i| and the second line is inductively the level of |⟦ Ds ⟧ᶜˢ X i|, and indeed the level of the sum type is their maximum.
It may appear that we skipped several steps applying the associativity and commutativity of~`⊔', but in fact these properties (along with some others) are built into Agda's definitional equality on |Level|, so the definition of |⟦_⟧ᶜˢ| type-checks without any manual proofs about levels.

\subsection{Packing Up}
\label{sec:DataD}

We are now ready to pack what we have developed in this section into two new layers of datatype descriptions, mostly corresponding to the representation given in \cref{sec:level-parameters}.
The outermost layer deals with universe-polymorphic level parameters,
\begin{code}
record DataD : Setω where
  field
    #levels  : ℕ
    applyL   : Level ^ #levels → PDataD
\end{code}
and the next layer deals with ordinary parameters and indices:
\begin{code}
record PDataD : Setω where
  field
    alevel      : Level
    {plevel  }  : Level
    {ilevel  }  : Level
    {struct  }  : ConBs
    level-inequality : maxMap max-π struct ⊔ maxMap max-σ struct ⊑ alevel ⊔ ilevel
    Param       : Tel plevel
    Index       : ⟦ Param ⟧ᵗ → Tel ilevel
    applyP      : (ps : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index ps ⟧ᵗ struct
\end{code}
For convenience, we lift the definitions of base functor to the |DataD| layer:
\begin{code}
⟦_⟧ᵈ :  (D : DataD) → ∀ {ℓs ps} →
        let I == ⟦ D .applyL ℓs .Index ps ⟧ᵗ in (I → Set ℓ) → (I → Set _)
⟦ D ⟧ᵈ {ℓs} {ps} = ⟦ D .applyL ℓs .applyP ps ⟧ᶜˢ

fmapᵈ :  (D : DataD) → ∀ {ℓs ps} →
         let I == ⟦ D .applyL ℓs .Index ps ⟧ᵗ in {X : I → Set ℓˣ} {Y : I → Set ℓʸ} →
         (∀ {i} → X i → Y i) → ∀ {i} → ⟦ D ⟧ᵈ X i → ⟦ D ⟧ᵈ Y i
fmapᵈ D {ℓs} {ps} = fmapᶜˢ (D .applyL ℓs .applyP ps)
\end{code}
For example, the |Acc| datatype can now be described by
\begin{code}
AccD : DataD
AccD = record
  {  #levels  = 2
  ;  applyL   = λ (ℓ , ℓ' , _) → record
     {  alevel  = ℓ'
     ;  level-inequality = refl
     ;  Param   = [ A ∶ Set ℓ ] [ R ∶ (A → A → Set ℓ') ] []
     ;  Index   = λ (A , _) → [ _ ∶ A ] []
     ;  applyP  = λ (A , R , _) → (σ[ x ∶ A ] ρ (π[ y ∶ A ] π[ _ ∶ R y x ] ι (y , tt)) (ι (x , tt))) ∷ [] }{-"\kern-1.5pt"-}}
\end{code}

What remain to be explained are the fields |alevel| and |level-inequality|, which make sure that a corresponding datatype definition would pass Agda's universe checker.
Here we are using the more conservative and simpler datatype level--checking rule employed when Agda's \verb"--without-K" option~\citep{Cockx-pattern-matching-without-K} is turned on: the level of a datatype should at least be the maximum level of its index types, which is |ilevel| in our descriptions.
If there are more components in the datatype level, they are specified in |alevel|, and the final datatype level is |alevel ⊔ ilevel|.
The datatype level is not uniquely determined by the content of the datatype ---for example, we could define alternative versions of natural numbers at any level--- but must be no less than the level of any |π|- or |σ|-field of the constructors; this is enforced by |level-inequality|, where the relation |ℓ ⊑ ℓ'| is defined by |ℓ ⊔ ℓ' ≡ ℓ'|.
With |level-inequality|, we could even define a universe-polymorphic version of the |μ|~operator from \cref{sec:recap}, but that is not the road we are going to take.

\section{Connecting Generic and Native Entities}
\label{sec:connections}

Instead of a generic |μ|~operator~(\cref{sec:recap}), we will rely on Agda's reflection mechanism~(\cref{sec:reflection}) to manufacture a native datatype from a description of type |DataD|~(\cref{sec:DataD}).
The native datatype will be in a curried form, but it is easier for generic programs to handle an uncurried form, which can be computed from the |DataD| by
\begin{code}
DataT : DataD → Setω
DataT D = ∀ ℓs →  let  Dᵖ == D .applyL ℓs
                  in   ∀ ps (is : Dᵖ .Index ps) → Set (Dᵖ .alevel ⊔ Dᵖ .ilevel)
\end{code}
This uncurried form always represents level parameters, ordinary parameters, and indices as three arguments |ℓs|, |ps|, and |is| regardless of how many parameters and indices there actually are, presenting a uniform view to generic programs.
The conversion from a curried form to an uncurried form is purely cosmetic and can be done with a wrapper function, for example,
\begin{code}
AccT : DataT AccD
AccT _ (A , R , _) = Acc R
\end{code}
We also need a constructor function |toN| corresponding to the |con| constructor of~|μ|, and moreover, we need to perform pattern matching, which can be simulated by an inverse |fromN| of |toN|.
These are what we need to know about the native datatype, which are summarised in this record type
\begin{code}
record DataC (D : DataD) (N : DataT D) : Setω where
  field
    toN        : ⟦ D ⟧ᵈ (N ℓs ps) is → N ℓs ps is
    fromN      : N ℓs ps is → ⟦ D ⟧ᵈ (N ℓs ps) is
    fromN-toN  : (ns : ⟦ D ⟧ᵈ (N ℓs ps) is) → fromN (toN ns) ≡ ns
    toN-fromN  : (n : N ℓs ps is) → toN (fromN n) ≡ n
\end{code}
The content of a |DataC D N| performs invertible conversion between the branches of the sum structure in~|D| with the constructors of~|N|.
For example,
\begin{code}
AccC : DataC AccD AccT
AccC = record  {  toN        = λ { (inl (x , ps , refl))  → acc ps }
               ;  fromN      = λ { (acc ps)               → inl (_ , ps , refl) }
               ;  fromN-toN  = λ { (inl (x , ps , refl))  → refl }
               ;  toN-fromN  = λ { (acc ps)               → refl } }
\end{code}
What we have developed is essentially an architecture where generic and native entities can be kept in sync (reminiscent of `bidirectional transformations'~\citep{Abou-Saleh-BX-intro}): a datatype has a |DataD| description on the generic side and a definition on the native side, and these two entities are connected by a |DataC|; a small twist is that the native definition is in a curried form, which is converted to a more regular uncurried form using a wrapper to interface with the architecture.
This architecture is symmetric: in addition to manufacturing a native datatype from a description, we can also compute a description of a native datatype; in either case, a connection is formed between the generic and native entities at the end.

Following the same architecture, we are also going to connect algebras with the corresponding native fold functions.
More precisely, the algebras are, in general, parametrised algebras like |foldAcc<Alg| from \cref{sec:recap}, and we start from a generic representation for them.
Analogously to |DataD|, the universe-polymorphic level parameters of a parametrised algebra are separated from the other parameters, whose types are represented as a telescope to allow currying, and all the parameter information is packed with the algebra into a record type |FoldP| of `fold programs':
\begin{code}
record FoldP : Setω where
  field
    {Desc}    :  DataD
    {Native}  :  DataT Desc
    Conv      :  DataC Desc Native
    #levels   :  ℕ
    level     :  Level ^ #levels → Level ^ (Desc .#levels)
    {plevel}  :  Level ^ #levels → Level
    Param     :  ∀ ℓs → Tel (plevel ℓs)
    param     :  Level ^ #levels → Level
    Carrier   :  ∀ ℓs ps → ⟦ Desc .applyL (level ℓs) .Index (param ps) ⟧ᵗ → Set (clevel ℓs)
    algebra   :  ∀ {ℓs} ps {is} →
                 ⟦ Desc .applyL (level ℓs) .applyP (param ps) ⟧ᶜˢ (Carrier ℓs ps) is →
                 Carrier ℓs ps is
\end{code}
A |FoldP| includes a field |Conv : DataC| connecting the datatype description |Desc| on which the |algebra| operates to a native datatype, which will be operated on by the corresponding native fold function.
The functions |level| and |param| are used to compute the parameters for the native datatype argument from the parameters of the fold function (see |FoldT| below).
For example, the following |FoldP| represents the universe-polymorphic fold operator for |Acc| on the generic side:
\begin{code}
foldAccP : FoldP
foldAccP = record
  {  Conv     = AccC
  ;  #levels  = 3
  ;  level    = snd
  ;  Param    = λ (ℓ'' , ℓ , ℓ' , _) →  [ A ∶ Set ℓ ] [ R ∶ (A → A → Set ℓ') ] [ P ∶ (A → Set ℓ'') ]
                                        [ p ∶ (∀ {x} → (∀ y → R y x → P y) → P x) ] []
  ;  param    = λ    (A , R , P , p , _) → A , R , tt
  ;  Carrier  = λ _  (A , R , P , p , _) (a , _) → P a
  ;  algebra  = λ {  (A , R , P , p , _) (inl (x , ps , refl)) → p ps {-"\;"-}} }
\end{code}
Again we can compute an uncurried type of the native fold function from a |FoldP|,
\begin{code}
FoldT : FoldP → Setω
FoldT F =  let  open FoldP F
           in   ∀ {ℓs} ps {is} → Native (level ℓs) (param ps) is → Carrier ℓs ps is
\end{code}
through which we can define a connection between a |FoldP| and a corresponding native function as the defining equation of the fold:
\begin{code}
record FoldC (F : FoldP) (f : FoldT P) : Setω where
  field
    equation :  let  open FoldP F
                in   (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is) →
                     f ps (Conv .toN ns) ≡ algebra ps (fmapᵈ Desc (f ps) ns)
\end{code}

Now let us try to transform |foldAccP| to a function |foldAcc| manually, and develop some generic facilities along the way.
First we need a type for |foldAcc|, which we can write a function to compute:
\begin{code}
FoldNT : (F : FoldP) (ℓs : Level ^ (F .#levels)) → Set _
FoldNT F ℓs =  let  open FoldP F
               in   Curriedᵗ (Param ℓs) λ ps →
                    Curriedᵗ (Desc .applyL (level ℓs) .Index (param ps)) λ is →
                    Native (level ℓs) (param ps) is → Carrier ℓs ps is
\end{code}
Because of the limitation of Agda's universe polymorphism (\cref{sec:level-parameters,sec:telescopes}), we have to treat the level parameters specially and cannot just curry them like what we have done with the ordinary parameters and indices.
After normalising |∀ {ℓs} → FoldNT foldAccP ℓs|, currying the level parameters, and renaming the arguments, we get the type
\begin{code}
foldAcc :  ∀ {ℓ'' ℓ ℓ'} (A : Set ℓ) (R : A → A → Set ℓ') (P : A → Set ℓ'')
           (p : ∀ {x} → (∀ y → R y x → P y) → P x) → ∀ {x} → Acc R x → P x
\end{code}
which we can wrap in
\begin{code}
foldAccT : FoldT foldAccP
foldAccT _ (A , R , P , p , _) = foldAcc A R P p
\end{code}
The definition of |foldAcc| should satisfy the |equation| of |FoldC foldAccP foldAccT|, but this equation does not work directly as a definition because |toN| is not a constructor.
An intermediate definition can be obtained by changing |toN| on the left-hand side to |fromN| on the right-hand side; this definition can be generically expressed by
\begin{code}
fold-base : (F : FoldP) → ∀ {ℓs} → FoldNT F ℓs → FoldNT F ℓs
fold-base F {ℓs} rec = let open FoldP F in curryᵗ λ ps → curryᵗ λ is →
  algebra ps ∘ fmapᵈ Desc (λ {is} → uncurryᵗ (uncurryᵗ rec ps) is) ∘ Conv .fromN
\end{code}
with which we can write
\begin{code}
foldAcc A R P p a = fold-base foldAccP foldAcc A R P p a
\end{code}
This definition, albeit a non-terminating one, implies the |FoldC.equation| because of the inverse property |DataC.fromN-toN|.
To turn this into a terminating definition, we pattern-match~|a| with all the possible constructors, of which there is only one in this case:
\begin{code}
foldAcc A R P p (acc as) = fold-base foldAccP (foldAcc A R P p) (acc as)
\end{code}
Finally we normalise the right-hand side,
\begin{code}
foldAcc A R P p (acc as) = p (λ y lt → foldAcc A R P p (as y lt))
\end{code}
and this final definition can be directly shown to satisfy the connecting equation:
\begin{code}
foldAccC : FoldC foldAccP foldAccT
foldAccC = record { equation = λ { (inl (x , as , refl)) → refl } }
\end{code}

Everything we did manually above was highly mechanical and deserves to be automated; this we do next in \cref{sec:reflection} using Agda's reflection mechanism, after which we will see some examples of datatype-generic programming with |DataC| and |FoldC| connections in \cref{sec:examples}.

\section{Establishing Connections via Reflection}
\label{sec:reflection}

\subsection{Introduction to Reflection in Agda}
\Viktor{
$\bullet$ TC monad, |macro| and |unquoteDecl|, problems of scope checking to be discussed in Section 7.

$\bullet$ Important primitive operations (should we discuss |quote| and |quoteTerm|?).

$\bullet$ Datatype and function descriptions.

$\bullet$ Our to-be-proposed design of |defineData| and |unquoteDecl|
}

\subsection{Datatype}
\Viktor{
$\bullet$ Observe correspondence between reflected and generic descriptions.

$\bullet$ Problems of universe polymorphism (one of which is strengthening).
}
\Viktor{Discuss weakening, strengthening and usage of extendContext}
\Viktor{Enforce types on untyped operations using quoteTC/unquoteTC}
\subsection{Recursion and Induction}
\Viktor{Translate FoldP/IndP to function definition}

\subsection{}

\section{Examples}
\label{sec:examples}

\subsection{Fold and Induction Operators}
\label{sec:fold-and-induction-operators}

\Josh{In contrast to an untyped approach, the datatype-generic version also proves that the arguments to the fold operator do constitute an algebra.}

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
\label{sec:algebraic-ornamentation}

\subsection{Predicates on Simple Containers}
\label{sec:simple-containers}

\Josh{There are not too many generic programs that work without assumptions on the range of datatypes they operate on.}

\Josh{Allow assumptions about data type descriptions to derive more functionalities (boring if we can only automate Eq, Show, Read etc)}

\Josh{There are not too many generic programs that work without assumptions on the range of datatypes they operate on.}

\section{Practical Issues}

\subsection{Portability}
\LT{Address the statement that our development is not specific to Agda.
So, what features do we need to implement?}
\LT{Axiom K is used for ornaments but this axiom is not generally desirable especially for homotopy type theory.
This seemingly conflicting requirement in fact originates in the false belief that only one identity type is allowed in a type theory.
Indeed, it is possible to have more than one identity type with different strength.
For example, the two-level type theory proposed by \citet{Capriotti2017} consists of a strict equality (satisfying the axiom K) and a weak equality compatible with the homotopy-theoretic interpretation.
Agda has an experimental option \texttt{--two-level} in the cubical mode which introduces additional universes \texttt{SSet}.
This extra sort of universes will make our library portable to proof assistants based on homotopy type theory.
(A bit of experiments should be performed to testify.)
}
\LT{Elaborator reflection}

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
Efficiency problem~\citep{Magalhaes-optimising-generics} due to conversion between generic and native representations (see below).
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

\todo[inline]{Missing the feature that converts fold functions to algebras, although there seems to be some overlap between this feature and the functionalities of the termination checker; update the reflection API?}

\section{Conclusion}

\todo[inline]{From the angle of datatype-generic programming, the generic constructions should work on native datatypes and functions for maximum interoperability with language facilities and other libraries, and the gap between generic and native entities can be filled straightforwardly with (powerful enough) metaprogramming.
From the angle of metaprogramming, one way to offer better correctness guarantees about the meta-level constructions is to introduce types, and (dependently typed) datatype-generic programming already provides a working solution for typing a good range of the constructions.
Each of the two programming disciplines works nicely as the other's natural extension.}

\todo[inline]{The native world as the common playground of multiple generic libraries}

\todo[inline]{Success of the App Store: dependent types need richer type structures and allow assumptions about datatype descriptions to derive more functionalities (boring if we can only automate Eq, Show, Read etc), so DGP has much more potential in dependently typed settings; also, keep generic programs natural so that libraries can be developed more easily — no staging!}

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
\todo[inline]{Bow-Yaw Wang (inherently generic representation)}
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
