\documentclass[acmsmall,review,fleqn]{acmart}

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
\setcitestyle{nosort}

\settopmatter{printacmref=false}

\usepackage[british]{babel}
\usepackage[hyperpageref]{backref} % this may be removed

\usepackage{mathtools}
\usepackage[euler]{textgreek}

\usepackage[capitalise,noabbrev]{cleveref}
\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\usepackage[color=yellow,textsize=scriptsize]{todonotes}
\setlength{\marginparwidth}{1.25cm}

\newcommand{\LT}[1]{\todo[author=LT,inline,color=green!40,caption={}]{{#1}}}
\newcommand{\Josh}[1]{\todo[author=Josh,inline,caption={}]{{#1}}}
\newcommand{\Viktor}[1]{\todo[author=Viktor,inline,color=orange,caption={}]{{#1}}}

\usepackage{caption}
\captionsetup{aboveskip=1.5ex minus .5ex,belowskip=-1.5ex minus .5ex}
\newcommand{\codefigure}{\small\setlength{\mathindent}{0em}\setlength{\abovedisplayskip}{0ex}\setlength{\belowdisplayskip}{0ex}\noindent}

\newcommand{\arXiv}[1]{\href{http://arxiv.org/abs/#1}{arXiv:\nolinkurl{#1}}}

\let\Bbbk\relax
%include agda.fmt

\setlength{\mathindent}{.5\parindent}
\newcommand{\cons}[1]{\mathbf{#1}}
\newcommand{\iden}{\mathit}

\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as

\usepackage{xcolor}
\definecolor{addition}{RGB}{204,255,216}
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.2ex depth 0.1ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

\usepackage[inline]{enumitem} % for environment enumerate*

%format (HL(t)) = "\highlight{addition}{" t "}"

%format syntax = "\Keyword{syntax}"
%format pattern = "\Keyword{pattern}"
%format unquoteDecl = "\Keyword{unquoteDecl}"
%format constructor = "\Keyword{constructor}"
%format unquote = "\Keyword{unquote}"
%format quote = "\Keyword{quote}"
%format quoteTerm = "\Keyword{quoteTerm}"
%format macro = "\Keyword{macro}"
%format postulate = "\Keyword{postulate}"
%format do = "\Keyword{do}"

%format == = "\mathop="
%format _ = "\char95"
%format : = "\mathop:"
%format → = "\mathop\to"
%format -> = "\mathop{\kern-.5pt\to\kern-.5pt}" 
%format ... = ".\kern.5pt.\kern.5pt.\kern.5pt"
%format [ = "[\kern-2pt"
%format Σ[ = Σ [
%format σ[ = σ [
%format π[ = π [
%format Γ = "\mathop\Gamma"
%format Δ = "\mathop\Delta"
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
%format ˣ = "_{\iden X}"
%format ʸ = "_{\iden Y}"

%format acc = "\cons{acc}"
%format con = "\cons{con}"
%format inl = "\cons{inl}"
%format inr = "\cons{inr}"
%format refl = "\cons{refl}"
%format ι = "\textbf{\textiota}"
%format σ = "\textbf{\textsigma}"
%format ρ = "\textbf{\textrho}"
%format π = "\textbf{\textpi}"
%format zero = "\cons{zero}"
%format suc = "\cons{suc}"
%format agda-sort = "\cons{agda\textsf{-}sort}"
%format set = "\cons{set}"
%format pi = "\cons{pi}"
%format lit = "\cons{lit}"
%format lam = "\cons{lam}"
%format pat-lam = "\cons{pat\textsf{-}lam}"
%format var = "\cons{var}"
%format def = "\cons{def}"
%format meta = "\cons{meta}"
%format unknown = "\cons{unknown}"
%format proj = "\cons{proj}"
%format absurd = "\cons{absurd}"
%format dot = "\cons{dot}"
%format prop = "\cons{prop}"
%format propLit = "\cons{propLit}"
%format inf = "\cons{inf}"
%format abs = "\cons{abs}"
%format arg = "\cons{arg}"
%format arg-info = "\cons{arg\textsf{-}info}"
%format visible = "\cons{visible}"
%format hidden = "\cons{hidden}"
%format instance′ = "\cons{instance′}"
%format nat = "\cons{nat}"
%format clause = "\cons{clause}"
%format absurd-clause = "\cons{absurd\textsf{-}clause}"
%format function = "\cons{function}"
%format data-type = "\cons{data\textsf{-}type}"
%format tt = "\cons{tt}"

%format A = "\iden A"
%format B = "\iden B"
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
%format c = "\iden{c}"
%format calgs = "\iden{calgs}"
%format calgsˣ = calgs ˣ
%format calgsʸ = calgs ʸ
%format cb = "\iden{cb}"
%format cbs = "\iden{cbs}"
%format cls = "\iden{cls}"
%format cs = "\iden{cs}"
%format d = "\iden d"
%format ds = "\iden{ds}"
%format eq = "\iden{eq}"
%format f = "\iden f"
%format fC = "\iden{fC}"
%format fs = "\iden{fs}"
%format h = "\iden h"
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
%format l = "\iden{l}"
%format lhs = "\iden{lhs}"
%format lt = "\iden{lt}"
%format m = "\iden m"
%format n = "\iden n"
%format ns = "\iden{ns}"
%format p = "\iden p"
%format ps = "\iden{ps}"
%format #ps = "\iden{\#ps}"
%format rb = "\iden{rb}"
%format rec = "\iden{rec}"
%format rhs = "\iden{rhs}"
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
\title{Datatype-Generic Programming Meets Elaborator Reflection}

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
\label{sec:introduction}

\todo[inline]{2 pages}

\Josh{Problems with the current state of dependently typed DGP (the kind of DGP discussed in this paper; no qualification hereafter)}

\Josh{What we really want from generic libraries, using lists and vectors as familiar examples: we want to generate functions for native datatypes as if they are hand-written so that they are efficient to compute (no back-and-forth representation conversions), easy to reason about (again without the conversions and no excessive abstraction), and can fully benefit from whatever language facilities there are (e.g., Agda's interactive features and compiler optimisations); moreover, we want to generate not only, for example, fold operators but also their theorems such as fold fusion; particularly important in a dependently typed setting is the ability to generate new \emph{datatypes}, and then their functions and properties (e.g., algebraic ornamentation and the associated isomorphism)}

\Josh{Old attempts at optimising DGP and why they don't work: There have been many attempts at removing overheads by compiler optimisation, but this is not enough for dependently typed programming, where programs may appear in later types and be reasoned about (and haven’t been processed by the compiler at all).
And compiler optimisations need to be fine-tuned to produce what we want; why not just generate what we want in the first place?}

\Josh{Staging? No! Enter elaborator reflection.}
\LT{
The use of elaborator reflection is essential to us: type-checking and normalisation, for example, are not available in other metaprogramming paradigms and they are hard to implement in full as this would require essentially rebuilding an elaborator.
Unlike other approaches using staging~\cite{Yallop-staged-generic-programming,Pickering-staged-SoP} where generic programs are entangled with staging to eliminate the generic representation, the elaborator reflection allows us to normalise a given open term directly.
}

\Josh{No radically new datatype-generic programming techniques, just adaptations for practical Agda programming (parameters, universe polymorphism, and visibility and curried forms; compare with \citet{Dybjer1994}); pointing out an ignored direction worth following}

\Josh{Some actual demo}

\todo[inline]{
Contributions:

$\bullet$ Better interoperability with native datatypes and functions (generating new native datatypes and functions, and connecting with existing ones for which generic constructions are specialised)

$\bullet$ Encoding of universe-polymorphic and parametrised inductive families (precise calculation of universe levels)

$\bullet$ A new use case of elaborator reflection where traditional datatype-generic programs are simply normalised to yield native programs (and do not need more radical adaptations like staging)

$\bullet$ Simpler and less error-prone `object-level' binder-manipulating techniques with (Agda's) elaborator reflection (bypassing the manipulation of de Bruijn indices; a tutorial for Agda's reflection mechanism)}

\todo[inline]{Practically-oriented, inspiring future theories}

\section{A Recap of Datatype-Generic Programming}
\label{sec:recap}

We start from a recap of standard datatype-generic programming in a dependently typed setting.
In \cref{sec:descriptions} we fix on a first-class representation of datatype definitions (restricted to inductive families~\citep{Dybjer1994} in this paper).
Then we review (|F|-)algebras in \cref{sec:algebras}, the kind of generic program that our presentation will focus on (but not the only kind we use).
The representations in this section are close to but not the final version, which we will develop in \cref{sec:parameters,sec:connections}.

\subsection{Datatype Descriptions}
\label{sec:descriptions}

\begin{figure}
\codefigure
\begin{minipage}[t]{.525\textwidth}
\begin{code}
data ConDs (I : Set) : Set₁ where
  []   :                     ConDs I
  _∷_  : ConD I → ConDs I →  ConDs I

data ConD (I : Set) : Set₁ where
  ι  : I                           → ConD I
  σ  : (A : Set)  → (A →  ConD I)  → ConD I
  ρ  : RecD I     →       ConD I   → ConD I

data RecD (I : Set) : Set₁ where
  ι  : I                           → RecD I
  π  : (A : Set)  → (A →  RecD I)  → RecD I
\end{code}
\end{minipage}%
\begin{minipage}[t]{.475\textwidth}
\begin{code}
⟦_⟧ᶜˢ : ConDs I → (I → Set) → (I → Set)
⟦ []       ⟧ᶜˢ  X i  = ⊥
⟦ D ∷ Ds   ⟧ᶜˢ  X i  = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i

⟦_⟧ᶜ : ConD I → (I → Set) → (I → Set)
⟦ ι j      ⟧ᶜ   X i  = i ≡ j
⟦ σ  A  D  ⟧ᶜ   X i  = Σ[ a ∶ A ] ⟦ D a ⟧ᶜ X i
⟦ ρ  D  E  ⟧ᶜ   X i  = ⟦ D ⟧ʳ X × ⟦ E ⟧ᶜ X i

⟦_⟧ʳ : RecD I → (I → Set) → Set
⟦ ι i      ⟧ʳ   X    = X i
⟦ π A D    ⟧ʳ   X    = (a : A) → ⟦ D a ⟧ʳ X
\end{code}
\end{minipage}
\caption{A basic version of datatype descriptions and their base functor semantics}
\label{fig:basic-descriptions}
\end{figure}

There have been quite a few variants of datatype encoding~\citep{Morris-thesis,Chapman-levitation,McBride-ornaments,Dagand-functional-ornaments,Ko-OrnJFP}; here we use a three-layered version that more closely follows the structure of an Agda datatype definition.
%\footnote{This choice of layered structure has also been adopted elsewhere, for example by \citet{de-Vries-true-SoP}.}
%which has (i)~a list of constructors made up of (ii)~a series of fields, some of which can be (iii)~potentially higher-order recursive occurrences of the datatype being defined.
As a small running example that covers all the essential components, consider this datatype of accessibility proofs:%
%\footnote{Although the meaning of |Acc<| is not important here, a quick explanation is that a proof |acc as : Acc< n| that |n|~is accessible captures the fact that any descending chain from~|n| with respect to~|_<_| is finite: if we deconstruct the proof by applying~|as| to some~|m| such that |m < n|, we will get a proof of |Acc< m|, which we can keep deconstructing, but can only do so a finite number of times because |Acc<| is an inductive datatype.}
\begin{code}
data Acc< : ℕ → Set where
  acc : (n : ℕ) (as : (m : ℕ) (lt : m < n) → Acc< m) → Acc< n
\end{code}
The first layer is the list of constructors, which for |Acc<| consists of only |acc|;
the type of |acc| has two fields |n|~and |as|, which constitute the second layer;
the type of the field~|as| is described in the third layer as it ends with the recursive occurrence |Acc< m|, in front of which there are function arguments |m|~and~|lt|.
Corresponding to the three layers, we use three datatypes of `descriptions' |ConDs|, |ConD|, and |RecD| in \cref{fig:basic-descriptions} ---all parametrised by an index type~|I|--- to encode datatype definitions.
For example, |Acc<| is described by
\begin{code}
Acc<D : ConDs ℕ
Acc<D = (σ ℕ (λ n → ρ (π ℕ (λ m → π (m < n) (λ lt → ι m))) (ι n))) ∷ []
\end{code}
Inhabitants of |ConDs I| are just lists of constructor (type) descriptions of type |ConD I|.
Inhabitants of |ConD I| are also list-like: the elements can either be the type of a non-recursive field, marked by~|σ|, or describe a recursive occurrence, marked by~|ρ|, and the `lists' end with~|ι|.
Different from ordinary lists, in the case of |σ A D| a new variable of type~|A| is brought into the context of~|D| (for example, in the type of |acc|, the field~|n| appears in the type of~|as|); this is done by making~|D| a function from~|A|, using the host language's function space to extend the context --- we will continue to use this technique heavily in \cref{sec:parameters}.%
\footnote{The computation power of the host language's function space has been better utilised in the datatype-generic programming literature (for example by \citet[Section~2.1]{McBride-ornaments}), but we will refrain from abusing the function space in the descriptions we write for tasks beyond context extension, keeping our descriptions in correspondence with native datatypes.
In general, if there are abuses, they will be detected at the meta-level~(\cref{sec:reflection}).}
The~|ι| at the end of a |ConD I| should specify the index targeted by the constructor (for example, the final~|n| in the type of |acc|).
Inhabitants of |RecD I| use the same structure to describe dependent function types ending with a recursive occurrence.

A couple of syntax declarations will make descriptions slightly easier to write and read:
\begin{code}
syntax π A (λ a → D) = π[ a ∶  A ] D{-"\,"-};{-"\quad"-} syntax σ A (λ a →  D) = σ[ a ∶  A ] D
\end{code}
For example, |Acc<D| can be rewritten as |(σ[ n ∶ ℕ ] ρ (π[ m ∶ ℕ ] π[ lt ∶ m < n ] ι m) (ι n)) ∷ []|.

In the standard recipe, a description |D : ConDs I| is converted to a type family |μ D : I → Set| by taking the least fixed point of the base functor |⟦ D ⟧ᶜˢ : (I → Set) → (I → Set)|:
\begin{code}
data μ (D : ConDs I) : I → Set where
  con : ∀ {i} → ⟦ D ⟧ᶜˢ (μ D) i → μ D i
\end{code}
For example, we can redefine |Acc<| as |μ Acc<D : ℕ → Set|, whose inhabitants are now constructed by the generic constructor |con|.
Specified by the definition of the base functor |⟦ D ⟧ᶜˢ| in \cref{fig:basic-descriptions},%
\footnote{|⊥|~is the empty type with no constructors.
|A ⊎ B| is the sum of the types |A|~and~|B| with constructors |inl : A → A ⊎ B| and |inr : B → A ⊎ B|.
|Σ[ a ∶ A ] B| is a dependent pair type, where |Σ[ a ∶ A ]| binds the variable~|a|, which can appear in~|B|; the pair constructor |_,_| associates to the right.
Free variables in types (such as~|I| in the types of |⟦_⟧ᶜˢ|, |⟦_⟧ᶜ|, and |⟦_⟧ʳ|) are implicitly universally quantified.}
the argument of |con| encodes the choice of a constructor and the arguments of the chosen constructor in a sum-of-products structure; for example, in Agda it is customary to use a pattern synonym~\citep{Pickering-pattern-synonyms} to define |acc| in terms of |con|,
\begin{code}
pattern acc n as = con (inl (n , as , refl))
\end{code}
where the arguments |n|~and~|as| of |acc| are collected in a tuple (product structure), tagged by |inl| (left injection into a sum type), and finally wrapped up with |con| as an inhabitant of |μ Acc<D n|.
In general, when there are multiple constructors, the injection parts will look like |inl ...|, |inr (inl ...)|, |inr (inr (inl ...))|, etc, specifying the constructor choice in Peano-style.
The equality proof |refl| at the end of the tuple needs a bit more explanation: in the type of |con|, the index~|i| is universally quantified, which seems to suggest that we could construct inhabitants of |μ D i| for any~|i|, but the equality proof forces~|i| to be~|n|, the index targeted by |acc|.

\subsection{Algebras as Generic Programs}
\label{sec:algebras}

\begin{figure}
\codefigure
\begin{code}
fmapᶜˢ  : (D : ConDs I)  → (∀ {i} → X i → Y i) → ∀ {i} → ⟦ D ⟧ᶜˢ  X i → ⟦ D ⟧ᶜˢ  Y i
fmapᶜˢ   (D ∷ Ds)      f  (inl  xs)      = inl  (fmapᶜ   D   f xs)
fmapᶜˢ   (D ∷ Ds)      f  (inr  xs)      = inr  (fmapᶜˢ  Ds  f xs)

fmapᶜ   : (D : ConD I)   → (∀ {i} → X i → Y i) → ∀ {i} → ⟦ D ⟧ᶜ   X i → ⟦ D ⟧ᶜ   Y i
fmapᶜ    (ι i      )   f  eq             = eq
fmapᶜ    (σ  A  D  )   f  (a ,   xs   )  = a , fmapᶜ (D a) f xs
fmapᶜ    (ρ  D  E  )   f  (xs ,  xs'  )  = fmapʳ D f xs , fmapᶜ E f xs'

fmapʳ   : (D : RecD I)   → (∀ {i} → X i → Y i) → ⟦ D ⟧ʳ X → ⟦ D ⟧ʳ Y
fmapʳ    (ι i    )     f  x              = f x
fmapʳ    (π A D  )     f  xs             = λ a → fmapʳ (D a) f (xs a)
\end{code}
\caption{Datatype-generic functorial maps of base functors}
\label{fig:fmap}
\end{figure}

Now we can write programs on |Acc<|, for example its fold operator:%
%\footnote{This operator proves the strong induction principle on accessible natural numbers.}
\begin{code}
foldAcc< :  {P : ℕ → Set} → (∀ n → (∀ m → m < n → P m) → P n) →
            ∀ {n} → Acc< n → P n
foldAcc< p (acc n as) = p n (λ m lt → foldAcc< p (as m lt))
\end{code}
However, the point of using described datatypes such as |μ Acc<D| is that we do not have to write |foldAcc<| ourselves but can simply derive it as an instantiation of a generic grogram.
The class of generic programs we will focus on in this paper is `($F$-)algebras'~\citep{Bird-AoP} (where the functor~$F$ is always some base functor |⟦ D ⟧ᶜˢ| in this paper), whose type is defined by
\begin{code}
Alg : ConDs I → (I → Set) → Set
Alg D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i
\end{code}
Algebras are useful because they are the interesting part of a fold function:
By a `fold function' we mean a function defined recursively on an argument of some datatype by (i)~pattern-matching the argument with all possible constructors, (ii)~applying the function recursively to all the recursive fields, and (iii)~somehow computing the final result from the recursively computed sub-results and the non-recursive fields.
For example, |foldAcc<| is a fold function, and so are a lot of common functions such as list |length|.\todo{a few more examples from \cref{sec:introduction}}
The first two steps are the same for all fold functions on the same datatype, whereas the third step is customisable and represented by an algebra, whose argument of type |⟦ D ⟧ᶜˢ X i| represents exactly the input of step~(iii).
We can define a generic |fold| operator that expresses the computation pattern of fold functions and can be specialised with an algebra,%
\footnote{The unsafe \textsc{terminating} pragma will not be a problem because we will not rely on this generic |fold| operator in this paper.}
\begin{code}
{-# TERMINATING #-}
fold : (D : ConDs I) → Alg D X → ∀ {i} → μ D i → X i
fold D f (con ds) = f (fmapᶜˢ D (fold D f) ds)
\end{code}
where |fmapᶜˢ| is the functorial map for |⟦ D ⟧ᶜˢ| (defined in \cref{fig:fmap}),%
\footnote{For most of the generic programs in this paper we will provide only a sketch, because they are not too different from those in the literature.
But as a more detailed example, the functorial map~(\cref{fig:fmap}) is a typical generic program:
The functorial map should apply a given function~|f| to all the recursive fields in a sum-of-products structure while leaving everything else intact, and it does so by analysing the input description layer by layer --- |fmapᶜˢ| keeps the choices of |inl| or |inr|, |fmapᶜ| keeps the |σ|-fields and |ι|-equalities, and finally |fmapʳ| applies~|f| to the recursive fields (of type~|X i| for some~|i|) pointwise.}
used here to apply |fold D f| to the recursive fields in~|ds|.
Libraries may provide generic programs in the form of algebras parametrised by descriptions, and the user gets a fold function for their datatype by applying |fold| to an algebra specialised to the description of the datatype.
For example, by specialising a generic program in \cref{sec:fold-operators}, we get an algebra (with some parameters of its own)
\begin{code}
foldAcc<Alg : {P : ℕ -> Set} -> (∀ n -> (∀ m -> m < n -> P m) -> P n) -> Alg Acc<D P
foldAcc<Alg p (inl (n , ps , refl)) = p n ps
\end{code}
which we then use to specialise |fold| to get |foldAcc<|:
\begin{code}
foldAcc< :  {P : ℕ → Set} → (∀ n → (∀ m → m < n → P m) → P n) →
            ∀ {n} → Acc< n → P n
foldAcc< p = fold Acc<D (foldAcc<Alg p)
\end{code}
%Instead of |fold|, however, we will provide an alternative way to get from algebras to fold functions through elaborator reflection~(\cref{sec:reflection}).

Being able to treat folds generically means that we can write generic programs whose types have the form |∀ {i} → μ D i → X i|, but this is not enough when, for example, we want to prove generic theorems by induction on |d : μ D i|, in which case the types take the more complex form |∀ {i} (d : μ D i) → P d| (where |P : ∀ {i} → μ D i → Set|).
Therefore we have another set of definitions for generic induction, corresponding to the scheme of elimination rules of inductive families~\citep[Section~3.3]{Dybjer1994}.
The technical details of generic induction are omitted from the presentation, however, since the treatment is largely standard (closely following, for example, \citet{McBride-ornaments}), and our metaprograms (\cref{sec:reflection}) work for fold and induction in the same way.

\section{Datatype Parameters and Universe Polymorphism}
\label{sec:parameters}

The datatype descriptions presented in \cref{sec:recap} missed a couple of important features --- it was probably tempting to generalise |Acc<| to a version parametrised by a type~|A| and a binary relation~|R| on~|A|, and moreover, by the levels of the universes in which |A|~and~|R| reside:%
\footnote{Agda's finite universe levels have a type |Level : Set|.
We can use the primitives |lzero : Level| and |lsuc : Level → Level| to construct finite levels in the same way as we construct natural numbers, but we cannot pattern-match levels with |lzero| and |lsuc|.
There is also an operator |_⊔_ : Level → Level → Level| that computes the maximum of two levels.}
\begin{code}
data Acc {ℓ ℓ' : Level} {A : Set ℓ} (R : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  acc : (x : A) → ((y : A) → R y x → Acc R y) → Acc R x
\end{code}
We ought to extend our datatype descriptions to express this kind of parametric and universe-polymorphic datatypes given their prevalence in Agda codebases.
Conceptually this is straightforward: parameters are just variables in the context which can be referred to by the index type, datatype level, and constructor types, and we know an easy way to extend the context --- just use the host language's function space.
So a parametrised and universe-polymorphic datatype could be described by a parameter type~|P|, a parametrised index type |I : (p : P) → Set (ℓⁱ p)| (where |ℓⁱ : P → Level|), a parametrised datatype level |ℓᵈ : P → Level|, and a parametrised list of constructor descriptions |(p : P) → ConDs (I p)| (where |ConDs| needs to be enriched with levels, which we will do in \cref{sec:universe-polymorphic-descriptions}).
For example, we could describe |Acc| with
\begin{code}
P  = Σ[ ℓ ∶ Level ] Σ[ ℓ' ∶ Level ] Σ[ A ∶ Set ℓ ] (A → A → Set ℓ')
I  = λ (_ , _ , A , _) → A {-"\qquad"-} ℓⁱ = λ (ℓ , _) → ℓ {-"\qquad"-} ℓᵈ = λ (ℓ , ℓ' , _) → ℓ ⊔ ℓ'
\end{code}
and a parametrised description that looks like |Acc<D|.
The actual description of |Acc| will be given in \cref{sec:DataD}, but before that, there are some practical issues about level quantification~(\cref{sec:level-parameters}) and representation of parameters and indices~(\cref{sec:telescopes}) to deal with.

\subsection{Level Parameters}
\label{sec:level-parameters}

Unfortunately, we have in fact already bumped into the limitation of Agda's current design of universe polymorphism, where only finite levels can be dealt with uniformly via quantification over |Level|.
Depending on whether a described datatype is universe-polymorphic or not, its parameter type may reside in a universe with a finite or infinite level: a non-universe-polymorphic parameter type, for example |Σ[ A ∶ Set ] (A → A → Set)|, resides in |Set₁|, which has a finite level, whereas the parameter type~|P| defined above for |Acc| ---call it |PAcc| for short--- cannot have type |Set ℓᵖ| for any |ℓᵖ : Level| because the type of~|A| is |Set ℓ| where |ℓ|~can be arbitrarily large, so the type/kind of~|PAcc| has to be |Setω|, the first universe with an infinite level.
Generic programs taking descriptions with parameters as input have to quantify the level of~|P|, but currently Agda does not allow such quantification.
This is one of the many problems created by the mismatch between the range of levels we need to handle and the limited power of level quantification;%
\todo{Is there a better reason?}
another is that the usual universe-polymorphic |Σ|-type former ---with which we can only construct |Σ|-types with finite levels--- is actually not enough for defining~|PAcc|;
and one more will be mentioned in \cref{sec:telescopes}.

To avoid some of the problems (including the two mentioned above), we make a simplifying assumption, which holds for common universe-polymorphic datatypes: we assume that there is a list of level parameters separate from other ordinary parameters, and only the level parameters are used to achieve universe polymorphism.
More formally, to describe a datatype, we start with a number |n : ℕ| of level parameters, from which we can compute a type |Level ^ n| of tuples of |n|~levels (as defined by |A ^ zero == ⊤| and |A ^ (suc n) == A × (A ^ n)|).%
\footnote{|⊤| is the unit type with one constructor~|tt|.}
Parameterised by |ℓs : Level ^ n|, the rest of the description can be written more succinctly as |λ ℓs → (ℓᵈ , ℓᵖ , ℓⁱ , P , I , D)| where |ℓᵈ|~is the datatype level, |P : Set ℓᵖ| the ordinary parameter type, |I : P → Set ℓⁱ| the parametrised index type, and |D : (p : P) → ConDs (I p)| the parametrised list of constructors.
Note that the datatype level~|ℓᵈ| depends only on the level parameters~|ℓs|, not the ordinary parameter of type~|P|; moreover, given~|ℓs|, the type~|P| (which is |Σ[ A ∶ Set ℓ ] (A → A → Set ℓ')| in the case of |Acc|) always has a finite level now, avoiding the two problems in the previous paragraph.
%We will pack all these data in two record types in \cref{sec:DataD}, after we make some more necessary refinements.

\subsection{Telescopes}
\label{sec:telescopes}

\begin{figure}
\codefigure
\begin{minipage}[b]{.65\textwidth}
\begin{code}
mutual

  data Tel : Level → Setω where
    []     : Tel lzero
    _∷_    : (A : Set  ℓ) (T  : A       → Tel ℓ') → Tel (ℓ ⊔ ℓ')
    _++_   : (T : Tel  ℓ) (U  : ⟦ T ⟧ᵗ  → Tel ℓ') → Tel (ℓ ⊔ ℓ')
\end{code}
\end{minipage}%
\begin{minipage}[b]{.35\textwidth}
\begin{code}
  ⟦_⟧ᵗ : Tel ℓ → Set ℓ
  ⟦ []       ⟧ᵗ = ⊤
  ⟦ A ∷   T  ⟧ᵗ = Σ[ a ∶ A       ] ⟦ T a ⟧ᵗ
  ⟦ T ++  U  ⟧ᵗ = Σ[ t ∶ ⟦ T ⟧ᵗ  ] ⟦ U t ⟧ᵗ
\end{code}
\end{minipage}
\caption{(Tree-shaped) telescopes and their semantics as nested |Σ|-types}
\label{fig:telescopes}
\end{figure}

At some point we will need to convert a description to a datatype definition, and it would be unsatisfactory in practice if the parameter and index types in the datatype definition were not in the conventional curried form.
When currying, the encoding of multiple types in one nested |Σ|-type is ambiguous --- how do we know whether a |Σ|-type is supposed to be interpreted as two types, with the latter depending on the former, or just one type?
A natural solution is to use telescopes~\citep{de-Bruijn-telescopes} to represent lists of parameter or index types, as shown in \cref{fig:telescopes}.
Again we use the host language's function space to bring variables of the types in the front of a telescope into the context of the rest of the telescope.
Besides the usual cons constructor `|∷|', we also include a constructor `|++|' for appending telescopes (which requires index induction-recursion~\citep{Dybjer-indexed-induction-recursion} to define), making our telescopes tree-shaped; the reason will be clear when we reach \cref{sec:examples}.
The index~|ℓ| in the type |Tel ℓ| of a telescope~|T| is the maximum level appearing in~|T|.
This level is important since it is the universe level of the type |⟦ T ⟧ᵗ|, which is a nested |Σ|-type inhabited by tuples whose components have the types in~|T|.
%More subtly, the indexing also precludes overly universe-polymorphic telescopes like |Level ∷ (λ ℓ → Set ℓ ∷ (λ _ → []))|, since in a cons telescope (and similarly in an appended telescope), the maximum level~|ℓ'| in the tail has to be determined independently from the |A|-typed value in the context.

A couple of syntax declarations will make telescopes slightly easier to write and read:
\begin{code}
syntax _∷_ A (λ x → T) = [ x ∶ A ] T{-"\,"-};{-"\quad"-} syntax _++_ T (λ t → U) = [[ t ∶ T ]] U
\end{code}
For example, the parameters of |Acc| can be represented as |[ A ∶ Set ℓ ] [ R ∶ (A → A → Tel ℓ') ] []| instead of |Set ℓ ∷ (λ A → (A → A → Set ℓ') ∷ (λ R → []))|.

From a telescope~|T| it is straightforward to compute a curried function type |Curriedᵗ T X| which has arguments with the types in~|T|, and ends with a given type |X : ⟦ T ⟧ᵗ → Set ℓ'| that can refer to all the arguments (collectively represented as a tuple of type |⟦ T ⟧ᵗ|):
\begin{code}
Curriedᵗ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ []          X = X tt
Curriedᵗ (A  ∷   T)  X = (a : A)          → Curriedᵗ (T a) (λ t  → X (a  , t  ))
Curriedᵗ (T  ++  U)  X = Curriedᵗ T (λ t  → Curriedᵗ (U t) (λ u  → X (t  , u  )))
\end{code}
It is also straightforward to convert between this curried function type and its uncurried counterpart with the functions\todo{condense?}
\begin{code}
curryᵗ    : ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ T X
uncurryᵗ  : Curriedᵗ T X → ((t : ⟦ T ⟧ᵗ) → X t)
\end{code}
whose definitions are omitted.
With these, we will be able to compute curried forms of parameters and indices when they appear in types (for example, the type of the fold operator of |Acc|).

Incidentally, if we attempt a similar construction for |Level ^ n| (which can be viewed as a kind of specialised telescope) to produce curried forms of level parameters as well,
\begin{code}
CurriedL : (n : ℕ) {f : Level ^ n → Level} → ((ℓs : Level ^ n) → Set (f ℓs)) → Set {! !}
CurriedL    zero    X = X tt
CurriedL (  suc n)  X = (ℓ : Level) → CurriedL n (λ ℓs → X (ℓ , ℓs))
\end{code}
we will not be able to fill in the hole `|{! !}|' since it should be a finite level when |n|~is zero (meaning that there is no level quantification), or~|ω| when |n|~is non-zero, going beyond the current capabilities of Agda's universe polymorphism.
To deal with level parameters, we will resort to metaprogramming techniques in \cref{sec:reflection}.

\subsection{Universe-Polymorphic Descriptions}
\label{sec:universe-polymorphic-descriptions}

\begin{figure}
\codefigure
\begin{minipage}[t]{.41\textwidth}
\begin{code}
record DataD : Setω where
  field
    #levels  : ℕ
    applyL   : Level ^ #levels → PDataD

record PDataD : Setω where
  field
    alevel {plevel} {ilevel} : Level
    {struct} : ConBs
    level-ineq :  maxMap max-π struct
               ⊔  maxMap max-σ struct
               ⊑  alevel ⊔ ilevel
    Param   :  Tel plevel
    Index   :  ⟦ Param ⟧ᵗ → Tel ilevel
    applyP  :  (ps : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index ps ⟧ᵗ struct
\end{code}
\end{minipage}%
\begin{minipage}[t]{.6\textwidth}
\begin{code}
data ConDs (I : Set (HL ℓⁱ)) : (HL ConBs) → Set{-"_{\highlight{addition}{\text\textomega}}"-} where
  []   :                                      ConDs I (HL [])
  _∷_  : ConD I (HL cb) → ConDs I (HL cbs) →  ConDs I (HL((cb ∷ cbs)))

data ConD (I : Set (HL ℓⁱ)) : (HL ConB) → Set{-"_{\highlight{addition}{\text\textomega}}"-} where
  ι  : I                                          →  ConD I (HL [])
  σ  : (A : Set (HL ℓ))  → (A →  ConD I (HL cb))  →  ConD I (HL(({-"\awa{\cons{inr}}{\cons{inl}}\;\awa{\iden{rb}}{\ell}\;"-} ∷ cb)))
  ρ  : RecD I (HL rb)    →       ConD I (HL cb)   →  ConD I (HL((inr rb ∷ cb)))

data RecD (I : Set (HL ℓⁱ)) : (HL RecB) → Set{-"_{\highlight{addition}{\text\textomega}}"-} where
  ι  : I                                          →  RecD I (HL [])
  π  : (A : Set (HL ℓ))  → (A →  RecD I (HL rb))  →  RecD I (HL((ℓ ∷ rb)))
\end{code}
\end{minipage}
\caption{Parametric and universe-polymorphic datatype descriptions (all five layers), where |RecB == List Level|, |ConB == List (Level ⊎ RecB)|, and |ConBs == List ConB|; modifications to \cref{fig:basic-descriptions} are highlighted.}
\label{fig:full-descriptions}
\end{figure}

It remains to adapt the description datatypes |ConDs|, |ConD|, and |RecD| from \cref{sec:recap} for universe polymorphism.
A first instinct might be copying what has been done for |Tel| (as constructor descriptions can be viewed as a slightly more complex kind of telescopes), enriching the |Set|-arguments to |Set ℓ| and perhaps indexing the datatypes with the maximum level, but this is not enough:
the range of definitions depending on |Tel| (such as |⟦_⟧ᵗ| and |Curriedᵗ|) is limited and requires only the computation of the maximum level, so indexing suffices; on the other hand, generic libraries built on the description datatypes may construct whatever they want from descriptions, and the need for non-trivial level computation will naturally arise if those constructions are universe-polymorphic.
For example, in \cref{sec:algebraic-ornamentation,sec:simple-containers} we will compute new universe-polymorphic datatypes from old ones, and will need to specify the new levels in terms of the old ones (and even reason about them).
For a concrete example we can look at now, consider how the type of a base functor |⟦ D ⟧ᶜˢ| should be enriched:
One place where we use the base functor is the type of an algebra |{i : I} → ⟦ D ⟧ᶜˢ X i → X i| where |X : I → Set ℓ|~is the result type, which can have any level depending on what the algebra computes, so |ℓ|~should be universally quantified in the type of |⟦ D ⟧ᶜˢ|.
But then, what should the level of the type |⟦ D ⟧ᶜˢ X i| be?
This level ---call it~|ℓ'|--- needs to be computed from |ℓ|~and the structure of~|D|, and the computation is non-trivial --- for example, if |D|~is |[]|, then |⟦ D ⟧ᶜˢ X i == ⊥|, in which case |ℓ'|~is simply |lzero|; if |D|~is non-empty, then |ℓ|~may or may not appear in~|ℓ'|, depending on whether there is a constructor with a |ρ|-field or not.

To allow level computation to be performed as freely as possible, we choose to index the description datatypes with as much useful information as possible, as shown in \cref{fig:full-descriptions}.
The index in the type of a description is a list which not only contains the levels of the fields but also encodes the description constructors used.
Starting from the simplest |RecD| datatype, we index it with |RecB == List Level|, recording the levels of the |π|-fields.
For |ConD|, the index type is |ConB == List (Level ⊎ RecB)|, whose element sum type is used to record whether a field is |σ|~or~|ρ|.
Finally, |ConDs| is indexed with |ConBs == List ConB|, collecting information from all the constructors into one list.
With some helper functions, which constitute a small domain-specific language for datatype level computation, we can now specify the output level of |⟦_⟧ᶜˢ|:
\begin{code}
⟦_⟧ᶜˢ :  {I : Set (HL ℓⁱ)} → ConDs I (HL cbs) → (I → Set (HL ℓ)) →
         (I → Set (  (HL(maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔))
                     (HL(maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs))))
⟦ []      ⟧ᶜˢ X i = ⊥
⟦ D ∷ Ds  ⟧ᶜˢ X i = ⟦ D ⟧ᶜ X i ⊎ ⟦ Ds ⟧ᶜˢ X i
\end{code}
In prose, the output level is the maximum among the maximum level of the |π|-fields, the maximum level of the |σ|-fields, |ℓ| if the description has a |ρ|-field, and |ℓⁱ| if the description has a constructor.

For our constructions, the approach works surprisingly well (even though the level expressions may look somewhat scary sometimes): we are able to write fully universe-polymorphic types while keeping almost all of the programs as they were --- for example, the universe-polymorphic program of |⟦_⟧ᶜˢ| is exactly the same as the non-universe-polymorphic one in \cref{sec:recap}.
To see how the universe-polymorphic version of |⟦_⟧ᶜˢ| is type-checked, we need to show a couple of definitions:
\begin{code}
maxMap : (A → Level) → List A → Level {-"\hspace{3em}"-}  hasCon? : Level → ConBs → Level
maxMap f []        = lzero                                hasCon? ℓ = maxMap (λ _ → ℓ)
maxMap f (a ∷ as)  = f a ⊔ maxMap f as
\end{code}
It is easy to see that the output level in the |⟦ [] ⟧ᶜˢ| case is |lzero|, which is indeed the level of~|⊥|.
In the |⟦ D ∷ Ds ⟧ᶜˢ| case where |D : ConD I cb| and |Ds : ConDs I cbs|, the output level expands to
\begin{code}
max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb ⊔ ℓⁱ ⊔
maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ maxMap (hasRec? ℓ) cbs ⊔ hasCon? ℓⁱ cbs
\end{code}
where the first line is the level of |⟦ D ⟧ᶜ X i| and the second line is inductively the level of |⟦ Ds ⟧ᶜˢ X i|, and indeed the level of the sum type is their maximum.
It may appear that we skipped several steps applying the associativity and commutativity of~`⊔', but in fact these properties (along with some others) are built into Agda's definitional equality on |Level|, so the definition of |⟦_⟧ᶜˢ| type-checks without any manual proofs about levels.

\subsection{Packing Up}
\label{sec:DataD}

We are now ready to pack what we have developed in this section into two new layers of datatype descriptions in \cref{fig:full-descriptions}, mostly corresponding to the representation given in \cref{sec:level-parameters}.
The outermost layer |DataD| contains the number of level parameters and brings those level parameters into the context for the next layer |PDataD| (for `parametrised datatype descriptions' or `pre-datatype descriptions'), which contains the ordinary parameter types in the |Param| telescope (with maximum level |plevel|), the index types in the parametrised |Index| telescope (with maximum level |ilevel|), and the parametrised list of constructor descriptions (whose structure is recorded in |struct|).
Before explaining the rest of the |PDataD| fields, it may be helpful to see an example first: the |Acc| datatype can now be described by
\begin{code}
AccD : DataD
AccD = record { #levels = 2;{-"~~"-} applyL = λ (ℓ , ℓ' , _) → record
  {  alevel  = ℓ';{-"~~"-} level-ineq = refl
  ;  Param   = [ A ∶ Set ℓ ] [ R ∶ (A → A → Set ℓ') ] []
  ;  Index   = λ (A , R , _) → [ _ ∶ A ] []
  ;  applyP  = λ (A , R , _) → (σ[ x ∶ A ] ρ (π[ y ∶ A ] π[ _ ∶ R y x ] ι (y , tt)) (ι (x , tt))) ∷ [] } }
\end{code}
When accessing the fields in the nested |DataD| and |PDataD| structures, the postfix projection syntax works better, as shown in the following definitions of base functor lifted to the |DataD| layer (which we will use later):
\begin{code}
⟦_⟧ᵈ :  (D : DataD) → ∀ {ℓs ps} →
        let I == ⟦ D .applyL ℓs .Index ps ⟧ᵗ in (I → Set ℓ) → (I → Set _)
⟦ D ⟧ᵈ {ℓs} {ps} = ⟦ D .applyL ℓs .applyP ps ⟧ᶜˢ

fmapᵈ :  (D : DataD) → ∀ {ℓs ps} →
         let I == ⟦ D .applyL ℓs .Index ps ⟧ᵗ in {X : I → Set ℓˣ} {Y : I → Set ℓʸ} →
         (∀ {i} → X i → Y i) → ∀ {i} → ⟦ D ⟧ᵈ X i → ⟦ D ⟧ᵈ Y i
fmapᵈ D {ℓs} {ps} = fmapᶜˢ (D .applyL ℓs .applyP ps)
\end{code}

What remain to be explained are the |PDataD| fields |alevel| and |level-ineq|, which make sure that a corresponding datatype definition would pass Agda's universe checker.
Here we are using the simpler datatype level--checking rule employed when Agda's \verb"--without-K" option~\citep{Cockx-pattern-matching-without-K} is turned on: the level of a datatype should at least be the maximum level of its index types, which is |ilevel| in our descriptions.
If there are more components in the datatype level, they are specified in |alevel|, and the final datatype level is |alevel ⊔ ilevel|.
The datatype level is not uniquely determined by the content of the datatype ---for example, we could define alternative versions of natural numbers at any level--- but must be no less than the level of any |π|- or |σ|-field of the constructors; this is enforced by |level-ineq|, where the relation |ℓ ⊑ ℓ'| is defined by |ℓ ⊔ ℓ' ≡ ℓ'|.
With |level-ineq|, we could even define a universe-polymorphic version of the |μ|~operator from \cref{sec:recap}, but that is not the road we are going to take.

\section{Connecting Generic and Native Entities}
\label{sec:connections}

Instead of a generic |μ|~operator~(\cref{sec:recap}), we will rely on Agda's elaborator reflection~(\cref{sec:reflection}) to manufacture a native datatype~|N| from a description |D : DataD|~(\cref{sec:DataD}).
Subsequently we may need to compute from~|D| a new description that refers to~|N| and its constructors.
For example, in \cref{sec:simple-containers} we will define a datatype-generic predicate |All| stating that a given predicate~|P| holds for all the elements in a container-like structure; for lists, |All| specialises to
\begin{code}
data ListAll {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  []   :                                        ListAll P []
  _∷_  : ∀ {a} → P a → ∀ {as} → ListAll P as →  ListAll P (a ∷ as)
\end{code}
whose description can be computed from the description of |List|.
Note that the index type of |ListAll| refers to |List| ---a native datatype--- and the indices targeted by the |ListAll| constructors refer to the native |List| constructors.
These native entities need to be provided as additional input to the generic construction of |All| to allow the latter to specialise to the description of |ListAll|.
More generally, if we provide enough structure about native datatypes so that what we can do with them are more or less the same as what we can do with those datatypes manufactured with~|μ|, then we should be able to adapt generic programs that assume the presence of~|μ| to work on these native datatypes instead.
Such structure will be defined in \cref{sec:DataC}, and analogously for fold functions in \cref{sec:FoldC}.

\subsection{Datatype Connections}
\label{sec:DataC}

\begin{figure}
\codefigure
\begin{code}
DataT : DataD → Setω
DataT D = ∀ ℓs ps → let Dᵖ == D .applyL ℓs in (is : Dᵖ .Index ps) → Set (Dᵖ .alevel ⊔ Dᵖ .ilevel)

record DataC (D : DataD) (N : DataT D) : Setω where field
  toN        : ⟦ D ⟧ᵈ (N ℓs ps) is  → N ℓs ps is
  fromN      : N ℓs ps is           → ⟦ D ⟧ᵈ (N ℓs ps) is
  fromN-toN  : (ns  : ⟦ D ⟧ᵈ (N ℓs ps) is)   → fromN (toN ns)  ≡ ns
  toN-fromN  : (n   : N ℓs ps is)            → toN (fromN n)   ≡ n
\end{code}
\caption{Datatype connections}
\label{fig:DataC}
\end{figure}

When |μ|~was present, generic programs only needed to take a description |D : DataD| as input, and the corresponding native datatype would simply be |μ D|.
Without~|μ|, a corresponding native datatype~|N| needs to be passed as an additional argument, and the first issue is the type of~|N|: the native datatype is usually in a curried form, but it is easier for generic programs to handle an uncurried form, which can be computed by |DataT D| as defined in \cref{fig:DataC}.
Regardless of how many parameters and indices there actually are, this uncurried form always represents level parameters, ordinary parameters, and indices as three arguments |ℓs|, |ps|, and |is|, presenting a uniform view to generic programs.
The conversion from a curried form to the uncurried form is purely cosmetic and can be done with a wrapper function, for example,
\begin{code}
AccT : DataT AccD
AccT _ (A , R , _) (as , _) = Acc R as
\end{code}
Note that |AccT| allows the form of the native datatype to be customised: we can change the order and visibility of the arguments (for example, the visibility of~|A| is set to implicit in |Acc|) as long as we change |AccT| accordingly.
Also, corresponding to the |con| constructor of~|μ|, we need a function |toN| to construct inhabitants of~|N|, and moreover, we need to perform pattern matching, which can be simulated by an inverse |fromN| of |toN|.
These are packed into the record type |DataC| of `datatype connections' in \cref{fig:DataC}, replacing |μ|'s functionalities.
(Strictly speaking, the inverse property |fromN-toN| here is only propositional whereas for |con| it is definitional, but this does not pose a problem for our examples in \cref{sec:examples}.)
%|DataC| is an example of generic definitions that benefit from the |DataT| wrapper --- the types of the fields would have been much messier if |N|~were in a curried form.
An inhabitant of |DataC D N| performs invertible conversion between the branches of the sum structure in~|D| with the constructors of~|N|, and the conversion is highly mechanical --- for example,
\begin{code}
AccC : DataC AccD AccT
AccC = record  {  toN        = λ { (inl (x , as , refl))  → acc x as             }
               ;  fromN      = λ { (acc x as)             → inl (x , as , refl)  }
               ;  fromN-toN  = λ { (inl (x , as , refl))  → refl                 }
               ;  toN-fromN  = λ { (acc x as)             → refl                 } }
\end{code}
Note that the order and visibility of constructor arguments can be customised as well.


The introduction of |DataC| supports a symmetric architecture where generic and native entities may grow separately but can be kept in sync: we may compute a new description from an old one and then manufacture a native datatype from the new description, or write a native datatype and then derive its description; in either case, a connection is established between the generic and native entities at the end.
This architecture generalises the standard one involving~|μ|, where |D|~has a connection only with |μ D|, whereas in our architecture, connections can be established between any pair of description and datatype as long as they correspond.
In particular, the forms of native datatypes and constructors (curried versus uncurried forms, order and visibility of arguments, etc) are not tightly coupled with descriptions (especially datatype-generically computed ones, which usually have prescribed forms) and can be customised by the programmer, which is vital in practice.

\subsection{Fold Connections}
\label{sec:FoldC}

\begin{figure}
\codefigure
\begin{minipage}[t]{.5\textwidth}
\begin{code}
record FoldP : Setω where field
  {Desc}    : DataD
  {Native}  : DataT Desc
  Con       : DataC Desc Native
  #levels   : ℕ
  level     :
    Level ^ #levels → Level ^ (Desc .#levels)
  applyL    :
    ∀ ℓs → PFoldP (Desc .applyL (level ℓs))
\end{code}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\begin{code}
record PFoldP (D : PDataD) : Setω where field
  {plevel} {clevel} : Level
  Param    :  Tel plevel
  param    :  ⟦ Param ⟧ᵗ → ⟦ D .Param ⟧ᵗ
  Carrier  :
    ∀ ps → ⟦ D .Index (param ps) ⟧ᵗ → Set clevel
  applyP   :
    ∀ ps → Alg (D .applyP (param ps)) (Carrier ps)

Alg : ConDs I cbs → (I → Set ℓ) → Set _
Alg D X = ∀ {i} → ⟦ D ⟧ᶜˢ X i → X i
\end{code}
\end{minipage}
\caption{Fold programs (parametrised algebras)}
\label{fig:FoldP}
\end{figure}

Following the same architecture, we are also going to connect algebras with native fold functions.
In general, algebras can be parametrised like |foldAcc<Alg| from \cref{sec:recap}, and first we should give them a proper representation: analogous to |DataD| and |PDataD|~(\cref{fig:full-descriptions}), we use two layers |FoldP| (for `fold programs') and |PFoldP| ---defined in \cref{fig:FoldP}--- to store respectively the level parameters and the ordinary parameters.
There are some additional fields that require explanation:
|FoldP| is designed to contain sufficient information for manufacturing a corresponding native fold function.
The fold function needs a type, which refers to the native datatype the fold function operates on, so |FoldP| includes a field |Con : DataC| connecting the datatype description |Desc| that the algebra operates on to a |Native| datatype, enabling us to compute the type of the fold function using |FoldT| in \cref{fig:FoldC}.%
\footnote{Agda's |open| statement can be used to bring the fields of an inhabitant of a record type into scope --- for example, the name |Native| in the definition of |FoldT| stands for |F .Native| because of |open FoldP F|.
Moreover, an |open| statement can be used in a |let|-expression to limit its effect to the body of the |let|-expression.}
In the definition of |FoldT|, we also see that the fields |level| and |param| are used to compute the parameters for the native datatype argument from the parameters of the fold function.
So, given |F : FoldP|, it can be connected to some |f : FoldT F|, but what should the connection be?
Since |f|~is supposed to replace an instantiation of the generic |fold| operator, what we need to know about~|f| is that it satisfies a suitably instantiated version of the defining equation of |fold|.
This |equation| constitutes the only field of the record type |FoldC| in \cref{fig:FoldC}.

\begin{figure}
\codefigure
\begin{code}
FoldT : FoldP → Setω
FoldT F =  ∀ ℓs ps {is} → let open FoldP F; open PFoldP (F .applyL ℓs) in
           Native (level ℓs) (param ps) is → Carrier ps is

record FoldC (F : FoldP) (f : FoldT F) : Setω where field
  equation :  ∀ {ℓs ps is} → let open FoldP F; open PFoldP (F .applyL ℓs) in
              (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is) →
              f ℓs ps (Con .toN ns) ≡ applyP ps (fmapᵈ Desc (f ℓs ps) ns)
\end{code}
\caption{Fold connections}
\label{fig:FoldC}
\end{figure}

In this paper we are only interested in manufacturing native fold functions from |FoldP| (and establishing |FoldC| at the end), leaving the opposite direction as future work.
As a concrete example, let us manufacture the universe-polymorphic fold operator for |Acc| from
\begin{code}
foldAccP : FoldP
foldAccP = record { Con = AccC;{-"~~"-} #levels = 3
  ;  level    = λ (ℓ'' , ℓ , ℓ' , _) → (ℓ , ℓ' , tt)
  ;  applyL   = λ (ℓ'' , ℓ , ℓ' , _) → record
     {  Param    =  [ A ∶ Set ℓ ] [ R ∶ (A → A → Set ℓ') ] [ P ∶ (A → Set ℓ'') ]
                    [ p ∶ (∀ x → (∀ y → R y x → P y) → P x) ] []
     ;  param    =  λ    (A , R , P , p , _) → A , R , tt
     ;  Carrier  =  λ    (A , R , P , p , _) (x , _) → P x
     ;  applyP   =  λ {  (A , R , P , p , _) (inl (x , ps , refl)) → p x ps } } }
\end{code}
(which is an instantiation of a generic program in \cref{sec:fold-operators}).
Along the way we will develop some generic facilities for mechanising the manufacturing process.
First we need a curried type for the fold function, which can be computed by a variant of |FoldT| that uses |Curriedᵗ|~(\cref{sec:telescopes}):
\begin{code}
FoldNT : (F : FoldP) (ℓs : Level ^ (F .#levels)) → Set _
FoldNT F ℓs = let open FoldP F; open PFoldP (F .applyL ℓs) in
  Curriedᵗ Param λ ps → Curriedᵗ (Desc .applyL (level ℓs) .Index (param ps)) λ is →
  Native (level ℓs) (param ps) is → Carrier ps is
\end{code}
As explained in \cref{sec:level-parameters,sec:telescopes}, we have to treat the level parameters specially and cannot just curry them like what we have done with the ordinary parameters and indices.
After normalising |∀ {ℓs} → FoldNT foldAccP ℓs| and currying the level parameters, we get the type
\begin{code}
foldAcc :  ∀ {ℓ'' ℓ ℓ'} (A : Set ℓ) (R : A → A → Set ℓ') (P : A → Set ℓ'')
           (p : ∀ x → (∀ y → R y x → P y) → P x) → ∀ x → Acc R x → P x
\end{code}
The definition of |foldAcc| should satisfy the |equation| of |FoldC foldAccP foldAccT|, but this equation does not work directly as a definition because |toN| is not a constructor.
We can, however, change |toN| on the left-hand side to |fromN| on the right-hand side to get a definition, which we write as
\begin{code}
foldAcc A R P p x a = fold-base foldAccP foldAcc A R P p x a
\end{code}
where |fold-base| generically expresses the computation pattern of fold functions in the usual non-recursive form that abstracts the recursive call as an extra argument~|rec|:
\begin{code}
fold-base : (F : FoldP) → ∀ {ℓs} → FoldNT F ℓs → FoldNT F ℓs
fold-base F {ℓs} rec = let open FoldP F; open PFoldP (F .applyL ℓs) in
  curryᵗ λ ps → curryᵗ λ is →
  applyP ps ∘ fmapᵈ Desc (λ {is} → uncurryᵗ (uncurryᵗ rec ps) is) ∘ Con .fromN
\end{code}
This definition of |foldAcc|, albeit one deemed non-terminating by Agda, implies the |FoldC.equation| because of the inverse property |DataC.fromN-toN|.
To turn this into a valid definition, we pattern-match the variable~|a| with all the possible constructors, although there is only one in this case:%
\begin{equation}\label{eq:fold-base-before}
|foldAcc A R P p x (acc as) = fold-base foldAccP foldAcc A R P p x (acc as)|
\end{equation}
Now normalise the right-hand side,
\begin{equation}\label{eq:fold-base-after}
|foldAcc A R P p x (acc as) = p x (λ y lt → foldAcc A R P p y (as y lt))|
\end{equation}

and this final definition can be directly shown to satisfy the connecting equation
\begin{code}
foldAccC : FoldC foldAccP foldAccT
foldAccC = record { equation = λ { (inl (x , as , refl)) → refl } }
\end{code}
where |foldAccT _ (A , R , P , p , _) {x , _} == foldAcc A R P p x| is a wrapper function.
(The inverse property |DataC.fromN-toN| does not appear in the proof, but we need it at the meta-level to argue generically that the proof always works.)

%Everything we did manually above was highly mechanical and deserves to be automated; this we do next in \cref{sec:reflection} using Agda's reflection mechanism, after which we will see some examples of datatype-generic programming with |DataC| and |FoldC| connections in \cref{sec:examples}.

%\todo[inline]{Although we do not present the details of generic induction, the definitions (|IndP|, |IndT|, etc) are largely the same as what we have formulated for folds above.
%When we get to examples that require induction in \cref{sec:examples}, which will only be sketched informally, it should suffice to think of those programs as a more complex kind of parametrised algebra with induction hypotheses.}

\section{Establishing Connections Using Elaborator Reflection}
\label{sec:reflection}


\Viktor{The built-in type |Term| (\cref{fig:full reflected syntax}) represents all reflected terms, with each constructor corresponding to a class of terms.
It's crucial that reflected terms are unityped by |Term|, meaning they are subject to arbitrary manipulation without type enforcement.
This untypeable nature gives us freedom to perform operations not possible under the object language's type system, therefore allowing translation from programs defined with generic description, which is more expressive than the object language, to their native counterparts.
However it's a double-edged sword that also puts programmers in great danger of dealing with structures that are not safeguarded by types, such as intermediate terms of strengthening and weakening.
This may leads to bugs in metaprograms uncaught by types.
Fortunately, we can exploit elaborator reflection to focus on interesting manipulations on terms, while leaving more typical and otherwise error-prone operations to the elaborator.
We will discuss in \cref{sec:translation} how we interact with the |TC| monad to do so.}

\Viktor{There are several differences between the elaborator reflection mechanisms of Agda and Idris, we will discuss them and their implications on our work in \cref{sec:discussion}.}

\LT{Staged computation has been proposed to solve the notorious efficiency problem~\cite{Yallop-staged-generic-programming,Pickering-staged-SoP} due to the conversions between generic representations.
This approach, however, requires the additional staging annotation \emph{inside} generic programs, making generic programs even harder to write.
It will be ideal to keep generic programs from metaprogramming.}



In this section, we will show that how elaborator reflection and generic programs work together to achieve following tasks:
First, metaprograms are used to translate representations described in \Cref{sec:parameters} used by generic programs such as |Tel : Level → Set|, which are \emph{higher-order} and \emph{typed}, and those by the reflection framework which are \emph{first-order} and \emph{uni-typed}.
Then, connections in \Cref{sec:DataC,sec:FoldC} are generated by walking through two different types of representations at the same time. 
Finally, generic programs such as~\eqref{eq:fold-base-before} are \emph{normalised during elaboration} systematically to derive definitions comparable, if not identical, to hand-written ones like~\eqref{eq:fold-base-after}. 

We should, however, briefly sketch the metaprogramming framework (\Cref{sec:elab}) and then explain how that is used in subsequent sections (\Cref{sec:translation,sec:connection-generation,sec:specialising}).


\subsection{Elaborator Reflection in Agda}
\label{sec:elab}
Agda's reflection API includes a set of primitives based on the elaborator monad, called |TC|, which operates on the reflected language formed by a few types,
including |Tm| (\Cref{fig:reflected-term}), |Pattern| (\Cref{fig:reflected pattern}), |Clause| (\Cref{fig:clause}), |Definition| (\Cref{fig:definition}), and |Literal| (\Cref{fig:other-type}), corresponding to each syntactic category. 
For the sake of illustration, only a small subset of reflected terms is presented rather than the actual type |Term| of reflected terms (\Cref{fig:full reflected syntax}).
The elaborator monad |TC| encloses states needed for elaboration including, the current context, the scope |Name| of names, the set |Meta| of metavariables, etc.\ which are not exposed directly.
Any term generated by a |macro| will be checked again to ensure the generated term is well-typed.

The reflected language plays a double role as the reflection of the surface language and the core language in the sense that reflected terms can be elaborated by |TC| computations.
The double role is very helpful as the reflected term |unknown| corresponding to the underscore `|_|' in Agda will be treated as a metavariable by the elaborator.
For example, the |TC| computation |checkType : Tm → Type → TC Tm| checks a reflected term against a reflected type and returns a (partially) elaborated reflected term with metavariables resolved if possible. 
If |unknown| is checked against the unit type |⊤|, then |checkType| returns the only constructor |tt| of |⊤| in the reflected form; if |unknown| is checked against |unknown| then |checkType| returns |meta x []| for some metavariable |x| generated during elaboration.

The reflected language in Agda is based on the de Bruijn representation and therefore \emph{not} hygiene.
Manipulating indices directly is notoriously error-prone, but in many cases there is no need to manipulate indices at all.
Elaboration reflection is able to `unquote' a reflected term by the TC computation |unquoteTC : ∀ {A} → Term → TC A|, so a reflected variable can be used as if it is object-level variable. 
Combining with the |TC| computation |extendContext : ∀ {A} → Type → TC A → TC A| which extends the current context, we are able to generate a variable used locally in another TC computation.
For example, the following |TC| computation 
\begin{code}
extendContextT : (B : Set ℓ) → (Type → B → TC A) → TC A
extendContextT B f = do
  `B ← quoteTC B
  extendContext `B do
    x ← unquoteTC {A = B} (var 0 [])
    f `B x
\end{code}


\LT{
  Outline the core of reflection:
  \begin{enumerate}
    \item reflected syntax with informal symbols: variables, constructors, pi-types, sets, etc.,
    \item telescope, function clauses,
    \item |quoteTerm| and |quote|,
    \item the double role as a checked and unchecked expmession,
    \item type-checking state, TC monad,
    \item function definition, datatype definition
    \item a few primitives including |getDefinition|, |getContext|,
    \item (?) |quoteTC| and |unquoteTC|
    \item introduce |macro| and |Tactic| with a small example
  \end{enumerate}
}



\begin{enumerate*}
	\item The fully-applied constructor |set t| represents universe types |Set ℓ| while |t| represents |ℓ|;
	\item |pi t u| represents dependent function types |T → U|, in which |T| and |U| are represented by |t| and |u|;
	\item |lit l| represents literals, i.e. numbers, characters and strings;
	\item |lam t| represents lambda terms |λ x → T| where |T| is represented by |t| and |x| is omitted since occurrences of |x| in |T| are translated to de Bruijn indices;
	\item |var i xs| represents variables, de Bruijn indexed by natural numbers |i|, applied to arguments that are represented by |xs|;
	\item |con c xs| and |def f xs| represents constructor and function applications respectively, where |c| and |f| are the constructor/function names, and |xs| represents the arguments they are applied to;
	\item |unknown| represents terms that are not provided.
	      For example, when there are parts of a type we conclude Agda could derive for us, we can fill them as |unknown| and feed the type to the |checkType| primitive, expecting the result would be devoid of |unknown|s.
\end{enumerate*}

\Viktor{Agda also supports top-level primitives |quote|, |quoteTerm| and |unquote|.
|quote| generates the name (of type |Name|) of the quoted term at call site upon elaborating, similarly |quoteTerm| generates the reflected representation (of type |Tm|).
|unquote| is the underlying primitive for macros, it takes a function |m : Tm → TC A|, creates a fresh metavariable |hole| and its quoted representation |qhole|, then execute |m qhole|.
Notably, when a macro is invoked, its |Tm| and |Name| arguments are quoted before being passed to it, while other arguments are passed as-is.}

\Viktor{Another usage of metaprograms is to define top-level definitions.
In Agda, elaboration happens after scope-checking, Agda wouldn't know a name is valid when scope-checking if it's only introduced by elaborator reflection.
I.e. they must be top-level definitions.
The keyword |unquoteDecl| introduces names of definitions into scope before they can be defined by metaprograms.
In a declaration |unquoteDecl f = T|, |f| is treated as a name of a to-be-defined function, where |T| is a metaprogram of type |TC ⊤| that should define |f|.
Function declaration and definition had been the only usages of |unquoteDecl|.
We have proposed a change in design such that |unquoteDecl D constructor c d e = T| would introduce |D| as a datatype name and |c|, |d|, |e| as constructor names into scope, which should be defined by |T|.
}

\begin{figure}
\codefigure
\begin{minipage}[t]{.5\textwidth}%
\begin{code}
data Tm : Set where
  set   : (t  : Tm)                  →  Tm
  pi    : (t u : Type)               →  Tm
  lit   : (l  : Literal)             →  Tm
  lam   : (t  : Tm)                  →  Tm
  var   : (i  : ℕ)     (xs   : Tms)  →  Tm
  con   : (c  : Name)  (xs   : Tms)  →  Tm
  def   : (f  : Name)  (xs   : Tms)  →  Tm
  meta  : (x  : Meta)  (xs   : Tms)  →  Tm
  unknown :                             Tm
\end{code}
\caption{Reflected expressions (simplified)}
\label{fig:reflected-term}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}%
\begin{code}
data Pattern where
  con     : (c : Name) (ps : Patterns)  → Pattern
  proj    : (f : Name)                  → Pattern
  var     : (i : ℕ)                     → Pattern
  absurd  : (i : ℕ)                     → Pattern
  lit     : (l : Literal)               → Pattern
  dot     : (t : Tm)                    → Pattern
\end{code}
\caption{Reflected patterns}
\label{fig:reflected pattern}
\end{minipage}
\end{figure}

\begin{figure}[h]
\codefigure
\begin{minipage}[t]{.5\textwidth}
\begin{code}
postulate
  Name  : Set
  Meta  : Set

data Literal where
  nat    : (n : ℕ) → Literal
  ...

\end{code}
\caption{Other built-in types for reflection}\label{fig:other-type}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\begin{code}
Type       =  Tm
Teles      =  List Type
Tms        =  List Tm
Names      =  List Name
Patterns   =  List Pattern
\end{code}
\caption{Type abbreviations}
\label{fig:type abbrs}
\end{minipage}
\end{figure}


\subsection{Translation between Typed Higher-Order and Untyped First-Order Representations}
\label{sec:translation}
\LT{Discuss the difference between the typed higher-order and untyped first-order representations of telescopes}
\LT{Introduce |extendContext|, |unquoteTC|, and a more safe version |extendContextT|}
\Viktor{Enforce types on untyped operations using |quoteTC|/|unquoteTC|; discuss the usage of |extendContext|}

\begin{figure}[h]
\codefigure
\begin{code}
data Clause : Set where
  clause         :  (Δ : Teles)  (lhs : Patterns)  (rhs : Tm)  → Clause
  absurd-clause  :  (Δ : Teles)  (lhs : Patterns)              → Clause
\end{code}
\caption{Clauses}\label{fig:clause}
\end{figure}

\begin{figure}[h]
\codefigure
\begin{code}
data Definition : Set where
  function    :             (cls  : Clauses)  → Definition
  data-type   : (#ps  : ℕ)  (cs   : Names)    → Definition
  ...
\end{code}
\caption{A snippet of reflected declarations}
\label{fig:definition}
\end{figure}
\subsection{Generating the Connections and Wrappers with |Level|}\label{sec:connection-generation}
\LT{Address the universe problem here: currying for |Level|}

\subsection{Instantiating Generic Functions without Bureaucracy}\label{sec:specialising}
\Viktor{Use |FoldP| to generate function definitions}
\LT{Introduce |normalise| and |checkType|; explain the difference between unchecked and checked clauses; no subject reduction for abstract syntax, so we have to normalise checked clauses with |fold-base| on the right hand side~\cite{Alimarine2004}}

\Viktor{definition declaration via macro |unquoteDecl|}

\section{Examples}
\label{sec:examples}

\todo[inline]{Some missed opportunities, not new stuff: generic constructions that the dependently typed programmer could have benefited from}

\subsection{Fold Operators}
\label{sec:fold-operators}

As a more familiar example, let us write a datatype-generic program
\begin{code}
fold-operator : DataC D N → FoldP
\end{code}
that gives rise to fold operators on native datatypes such as |foldAcc|.
Given |C : DataC D N|, the parameters in |fold-operator C| are essentially a |D|-algebra where sums are separated and products are curried, so what we need to do is just cosmetic work: at type level, compute the parameter types, which are the curried types of the constructors of~|D| where all the recursive occurrences are replaced with a given carrier, and at program level, uncurry and assemble the parameters into a |D|-algebra.

Part~(i) is computed by
\begin{code}
FoldOpTel :  (D : ConDs I cbs) → (I → Set ℓ) →
             Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
FoldOpTel []        X = []
FoldOpTel (D ∷ Ds)  X = [ _ ∶ FoldOpT D X ] FoldOpTel Ds X
\end{code}
which converts each constructor description to a type by |FoldOpT| and collects the types in a telescope.
The actual conversion by |FoldOpT| produces the required curried type:
\begin{code}
FoldOpT : (D : ConD I cb) → (I → Set ℓ) → Set (max-π cb ⊔ max-σ cb ⊔ ℓ)
FoldOpT (ι i     ) X = X i
FoldOpT (σ A  D  ) X = (a : A)   → FoldOpT (D a) X
FoldOpT (ρ D  E  ) X = ⟦ D ⟧ʳ X  → FoldOpT E X
\end{code}
For example, given a predicate |P : A → Set ℓ| as the carrier, the description of |acc| is converted to
\begin{code}
   FoldOpT (σ[ x ∶ A ] ρ (π[ y ∶ A ] π[ _ ∶ R y x ] ι y) (ι x)) P
=  (x : A) → ((y : A) → R y x → P y) → P x
\end{code}

For part~(ii), we are given a list of functions of the types in a telescope computed by |FoldOpTel|, from which we should construct an algebra; this is done by performing a case analysis on the argument of the algebra ---which is a sum structure--- to determine which function to apply:
\begin{code}
fold-op : (D : ConDs I cbs) → ⟦ FoldOpTel D X ⟧ᵗ → Alg D X
fold-op (D ∷ Ds) (f , fs) (inl  xs) = fold-opᶜ  D   f   xs
fold-op (D ∷ Ds) (f , fs) (inr  xs) = fold-op   Ds  fs  xs
\end{code}
The task of the next layer |fold-opᶜ| is also constructing a |D|-algebra, but here |D|~is a single constructor description (|ConD|) rather than a list of constructor descriptions (|ConDs|).
For convenience, define
\begin{code}
Algᶜ : ConD I cb → (I → Set ℓ) → Set _
Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i
\end{code}
so that the type of |fold-opᶜ| can be written in a form corresponding to the type of |fold-op|:
\begin{code}
fold-opᶜ : (D : ConD I cb) → FoldOpT D X → Algᶜ D X
fold-opᶜ (ι  i     ) x  refl           = x
fold-opᶜ (σ  A  D  ) f  (a   , xs   )  = fold-opᶜ (  D a)  (f  a   ) xs
fold-opᶜ (ρ  D  E  ) f  (xs  , xs'  )  = fold-opᶜ    E     (f  xs  ) xs'
\end{code}
The definition of |fold-opᶜ| is essentially uncurrying, gradually applying a given function to the argument of the algebra --- which is a tuple.

Finally we pack everything into the definition of |fold-operator|:
\begin{code}
fold-operator : DataC D N → FoldP
fold-operator {D} C = record
  {  Conv     =  C
  ;  #levels  =  suc (D .#levels)
  ;  level    =  snd
  ;  Param    =  λ (ℓ , ℓs) → let Dᵖ = D .applyL ℓs in
                   [[ ps ∶ Dᵖ .Param ]] [ X ∶ Curriedᵗ (Dᵖ .Index ps) (λ _ → Set ℓ) ]
                   FoldOpTel (Dᵖ .applyP ps) (uncurryᵗ X)
  ;  param    =  fst
  ;  Carrier  =  λ _  (ps , X , calgs) → uncurryᵗ X
  ;  algebra  =  λ    (ps , X , calgs) → fold-op (D .applyL _ .applyP ps) calgs }
\end{code}
The level parameters of |fold-operator C| include those of~|D| and one more for the carrier~|X| appearing in the |Param| telescope, which also includes the ordinary parameters of~|D| and the parameters computed by |FoldOpTel|.
The type of~|X| is specified to be in a curried form, which is then uncurried for |FoldOpTel| and the |Carrier| field --- a common pattern where curried entities seen by the user are converted to uncurried forms for processing by generic programs.
The |Param| telescope is the first place where we see the use of telescope appending, with which the parameters are divided into three `groups' |ps|, |X|, and |calgs|, making it convenient to distribute them to relevant parts of the generic definition.
The benefit is even clearer in the next example and also in \cref{sec:algebraic-ornamentation}.

It would not be too interesting if we could only manufacture functions but not prove some of their properties.
For fold operators, one of the most useful theorems is the fusion theorem~\citep{Bird-AoP}, which states that a function~|h| composed with a fold can be fused into the fold if |h|~is a homomorphism between the algebras of the two folds.%
\todo{List version in \cref{sec:introduction}}
The theorem can be represented as a generic program
\begin{code}
fold-fusion : (C : DataC D N) (fC : FoldC (fold-operator C) f) → IndP
\end{code}
which we apply to a datatype connection~|C| and a fold connection |fC| ---which essentially says that a function~|f| is a fold operator--- to get a specialised version of the theorem.

\subsection{Algebraic Ornamentation}
\label{sec:algebraic-ornamentation}

\todo[inline]{Side effect of level indexing: works as a first-order, albeit partial, representation of datatypes}

\Josh{The representation looks more messy, but they will actually lead to cleaner native datatypes.}

\subsection{Predicates on Simple Containers}
\label{sec:simple-containers}

\Josh{There are not too many generic programs that work without assumptions on the range of datatypes they operate on.}

\Josh{Allow assumptions about data type descriptions to derive more functionalities (boring if we can only automate Eq, Show, Read etc)}

\Josh{There are not too many generic programs that work without assumptions on the range of datatypes they operate on.}

\section{Practical Issues}

\subsection{Portability}
\LT{Address the statement that our development is not specific to Agda.
So, what features do we need to implement?
(Elaborator reflection)}
%\LT{Axiom K is used for ornaments but this axiom is not generally desirable especially for homotopy type theory.
%This seemingly conflicting requirement in fact originates in the false belief that only one identity type is allowed in a type theory.
%Indeed, it is possible to have more than one identity type with different strength.
%For example, the two-level type theory proposed by \citet{Capriotti2017} consists of a strict equality (satisfying the axiom K) and a weak equality compatible with the homotopy-theoretic interpretation.
%Agda has an experimental option \texttt{--two-level} in the cubical mode which introduces additional universes \texttt{SSet}.
%This extra sort of universes will make our library portable to proof assistants based on homotopy type theory.
%(A bit of experiments should be performed to testify.)

\subsection{Naming, Visibility, and Order of Arguments}

\begin{figure}
\codefigure
\begin{minipage}[t]{.45\textwidth}\setlength{\mathindent}{0em}
\begin{code}
mutual
  data (HL (Sort : Set)) where
    set      : (t : Term)  →  Sort
    lit      : (n : ℕ)     →  Sort
    prop     : (t : Term)  →  Sort
    propLit  : (n : ℕ)     →  Sort
    inf      : (n : ℕ)     →  Sort
    unknown  :                Sort

  data (HL (Abs (A : Set)  : Set)) where
    abs : (s : String)   (x : A) → Abs A

  data (HL (Arg (A : Set)  : Set)) where
    arg : (i : ArgInfo)  (x : A) → Arg A

  data (HL (ArgInfo     : Set)) where
    arg-info : (v : Visibility) (m : Modality) → ArgInfo
  ...
\end{code}
\end{minipage}%
\begin{minipage}[t]{.55\textwidth}\setlength{\mathindent}{0em}
\begin{code}
{-" "-}
data Term : Set where
  (HL agda-sort)  : (s : Sort)                                      → Term
  pi              : (a : (HL Arg) Type) (b : (HL Abs) Type  )       → Term
  lit             : (l : Literal)                                   → Term
  lam             : ((HL(v : Visibility)))   (t : (HL Abs) Term)    → Term
  (HL pat-lam)    : (cls : Clauses)          (xs : Args Term)       → Term
  var             : (i : ℕ)                  (xs : (HL Args) Term)  → Term
  con             : (c : Name)               (xs : (HL Args) Term)  → Term
  def             : (f : Name)               (xs : (HL Args) Term)  → Term
  meta            : (x : Meta)               (xs : (HL Args) Term)  → Term
  unknown         : Term
\end{code}
\end{minipage}

\begin{minipage}[t]{.6\textwidth}\setlength{\mathindent}{0em}
\begin{code}
\end{code}
\end{minipage}%
  
\caption{A snippet of reflected expressions (actual)}
\label{fig:full reflected syntax}
\end{figure}

\begin{code}
Args : Set ℓ → Set ℓ
Args A = List (Arg A)
\end{code}

\begin{code}
Telescope = List (String × Type)
\end{code}

\todo[inline]{Chosen by generic programs, dependency analysis, refactoring tools, heuristics, machine learning; interaction with generalised variables; the wrapper trick retains all these possibilities}

\subsection{Normalisation and Printing}

\todo[inline]{`type preservation', optimisation, name scope and qualification}

\subsection{Interactive User Interface}

\subsection{Automatic Resolution of Arguments to Generic Programs}

\todo[inline]{Type classes, instance arguments}

\section{Discussion}
\label{sec:discussion}

\paragraph{Interoperability}

\Josh{Instead of a most generic representation~\citep{Magalhaes-GGP}, just use the native datatypes, and instantiate all generic constructions to native entities.}

\todo[inline]{The native world as the common playground of multiple generic libraries; delta-based bidirectional transformations~\citep[Section~3.3]{Abou-Saleh-BX-intro} and bx network~\citep{Stevens-multiary-BX}; the need for syncing may be unavoidable since representation matters in practice}

\todo[inline]{Missing the feature that converts fold functions to algebras, although there seems to be some overlap between this feature and the functionalities of the termination checker; update the reflection API?}

\paragraph{Code generation vs first-class datatypes}

\Josh{\citet{Benke-generic-universes,Altenkirch-GP-within-DTP,Gibbons-DGP}.
The Haskell programmer produces recursive function definitions~\citep{de-Vries-true-SoP}.
We adopt the approach where generic function representations are non-recursive and then weaved into recursive definitions.
The language supports a single generic representation akin to the generic |μ| and |fold| operators, which avoid code duplication/explosion but (potentially?) sacrificing efficiency~\citep{Allais-n-ary-functions}.
No development since levitation~\citep{Chapman-levitation}, in particular no implementation.
Our work provides a foundation for the development of generic libraries \emph{now}.
Feel free to port the libraries to a new foundation when it's ready.}

\paragraph{Datatype-generic libraries for dependently typed programming}

\Josh{Our work enables the practical development and applications of datatype-generic libraries.
Duplicated code in Standard Library.
Ornaments have been used to lift functions, but its original purpose ---organisation of datatypes--- should not be forgotten (\citet{McBride-ornaments}; porting some constructions from \citet{Ko-OAOAOO}; more experimental developments~\citep{Ko-OrnJFP, Dagand-functional-ornaments}; theory and developments about function transportation in simply typed settings~\cite{Williams-principle-ornamentation, Williams-ornaments-in-practice}; realistic dependently typed application and automated synthesis of ornaments~\citep{McDonell-Ghostbuster,Ringer-ornaments-Coq}).
Make \citet{McBride-pivotal, Allais-binding-syntax-universe-JFP} native.}

\todo[inline]{Success of the App Store: dependent types need richer type structures and allow assumptions about datatype descriptions to derive more functionalities (boring if we can only automate Eq, Show, Read etc), so DGP has much more potential in dependently typed settings; also, keep generic programs natural so that libraries can be developed more easily — no staging (which is not in the current dependently typed languages anyway)!}

\paragraph{Universe polymorphism}

\LT{A practical application and motivation~\citep{Kovacs-universe-hierarchies} (not just theoretically interesting); generic level quantification; no subject reduction; universe-polymorphic definitions not polymorphic enough (e.g., |Σ|-types); more expressive universes}

\paragraph{Typed metaprogramming}

\LT{Emphasise object-level binder-manipulating techniques~\citep{Chen-Mtac-Agda}.}

\paragraph{Foundation of typed metaprogramming}

\LT{One more step towards practical `type theory in type theory'~\citep{Chapman-type-theory-should-eat-itself} (not just theoretically interesting), although our encoding is `shallow'.
Our experience with untyped metaprogramming was painful, especially in contrast to the experience with datatype-generic programming --- a form of typed metaprogramming.
Respond to \varcitet{Christiansen-elaborator-reflection}{'s} comments about datatype-generic programming (untyped vs typed metaprogramming): in contrast to an untyped approach, |fold-operator| also serves as a proof that the arguments of a fold operator do constitute an algebra.
Other work on typed metaprogramming~\citep{Xie-Typed-Template-Haskell, Jang-Moebius, Kiselyov-MetaOCaml, Davies-modal-staged-computation} may benefit from considering practical applications.}

\todo[inline]{\citet{Chapman-levitation} propose a more radical redesign of type theory where datatype definitions are first-class, but the theory is still at an early stage of development and lacks an implementation; our proposal is more practical and serves as a platform for the development of mature datatype-generic libraries, which can be ported to new platforms when ready}

\paragraph{Optimisation of datatype-generic programs}

\Viktor{\citet{Pickering-staged-SoP, Yallop-staged-generic-programming, Jones-partial-evaluation, de-Vries-masters-thesis, Alimarine2004}; partial evaluation is more programmer-friendly than staging, and elaborator reflection provides, to some extent, the ability to do partial evaluation.
Staging may be better for controlling what appears in the final code, but there's no implementation for dependently typed languages.
Efficiency problem due to conversion between generic and native representations (see below) since the Haskell era~\citep{Magalhaes-optimising-generics}.}

\paragraph{Conclusion}

\todo[inline]{From the angle of datatype-generic programming, the generic constructions should work on native datatypes and functions for maximum interoperability with language facilities and other libraries, and the gap between generic and native entities can be filled straightforwardly with (powerful enough) metaprogramming.
From the angle of metaprogramming, one way to offer better correctness guarantees about the meta-level constructions is to introduce types, and (dependently typed) datatype-generic programming already provides a working solution for typing a good range of the constructions.
Each of the two programming disciplines works nicely as the other's natural extension.}

\todo[inline]{Suggestions for the future evolution of Agda or the design of new languages with elaborator reflection}

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
