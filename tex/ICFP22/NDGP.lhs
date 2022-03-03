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
%\usepackage[hyperpageref]{backref}

\usepackage{mathtools}
\usepackage[euler]{textgreek}

\usepackage[capitalise,noabbrev]{cleveref}
\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}
\newcommand{\NoPeriod}[1]{\,}

\usepackage[color=yellow,textsize=scriptsize,disable]{todonotes}
\setlength{\marginparwidth}{1.25cm}

\newcommand{\LT}[1]{\todo[author=LT,inline,color=green!40,caption={}]{{#1}}}
\newcommand{\Josh}[1]{\todo[author=Josh,inline,caption={}]{{#1}}}
\newcommand{\Viktor}[1]{\todo[author=Viktor,inline,color=orange,caption={}]{{#1}}}

\usepackage[inline]{enumitem} % for environment enumerate*

\captionsetup{aboveskip=1.5ex minus .5ex,belowskip=-1.5ex minus .5ex}
\newcommand{\codefigure}{\footnotesize\setlength{\mathindent}{0em}\setlength{\abovedisplayskip}{0ex}\setlength{\belowdisplayskip}{0ex}\noindent}

\newcommand{\arXiv}[1]{\href{http://arxiv.org/abs/#1}{arXiv:\nolinkurl{#1}}}

\let\Bbbk\relax
%include agda.fmt

\newcommand{\cons}[1]{\mathbf{#1}}
\newcommand{\iden}{\mathit}

\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as

\usepackage{xcolor}
\definecolor{addition}{RGB}{204,255,216}
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.2ex depth 0.1ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

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
%format cΔ[ = cΔ [
%format Γ = "\mathop\Gamma"
%format Δ = "\mathop\Delta"
%format ] = "\kern-2pt]"
%format [[ = "|\kern-1.5pt[\kern-2pt"
%format ]] = "\kern-2pt]\kern-1.5pt|"
%format ⦃ = "\{\kern-.9pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-1.5pt"
%format ⦄ = "\kern-1.5pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-.9pt\}"
%format ⟦ = "⟦\kern-1.5pt"
%format ⟧ = "\kern-1.5pt⟧"
%format × = "\mathop\times"
%format ⊎ = "\mathop\uplus"
%format ≡ = "\mathop\equiv"
%format (EQ(t)) = "\mathop{\equiv_{\," t "}}"
%format ∘ = "\mathop\circ"
%format ⊔ = "\mathop\sqcup"
%format ⊑ = "\mathop\sqsubseteq"
%format ^ = "\kern-1.5pt\text{\char94}\kern-1.5pt"
%format ++ = "{+}\kern-3pt{+}"
%format _++_ = _ ++ _
%format Tel._++_ = Tel. _++_
%format ∺ = ∷ "\kern-3.75pt\raisebox{1.95pt}{\rule{3.25pt}{.5pt}}"
%format >>= = "\mathop{{>}\kern-3pt{>}\kern-3pt{=}}"
%format =<< = "\mathop{{=}\kern-3pt{<}\kern-3pt{<}}"

%format Setω = Set "_{\text\textomega}"
%format Acc< = Acc "_<"
%format Acc<D = Acc "_<\Conid{D}"
%format foldAcc< = fold Acc<
%format foldAcc<Alg = foldAcc< Alg
%format μ = "\text\textmugreek"
%format CurriedL = Curried "_{\Conid L}"
%format genFoldC' = genFoldC "^\prime"

%format ᵗ = "_{\Conid T}"
%format ⟦_⟧ᵗ = ⟦_⟧ ᵗ
%format ⟧ᵗ = ⟧ ᵗ
%format Curriedᵗ = Curried ᵗ
%format curryᵗ = curry ᵗ
%format uncurryᵗ = uncurry ᵗ
%format ⊆ᵗ? = "\mathop{\subseteq^t}?"
%format _⊆ᵗ?_ = _ ⊆ᵗ? _

%%format ` = "{}^\backprime"
%%format `Set = ` Set
%%format `[] = ` []
%%format `∷ = "\mathop{" ` "{" ∷ "}}"
%format `A = ` A
%format `B = ` B
%format `D = ` D
%format `T = ` T
%format `type = ` "\iden{type}"

%format ᵇ = "_{\Conid B}"
%format SCᵇ = SC ᵇ

%format ʳ = "_{\Conid R}"
%format ⟦_⟧ʳ = ⟦_⟧ ʳ
%format ⟧ʳ = ⟧ ʳ
%format fmapʳ = fmap ʳ
%format algDʳ = algD ʳ

%format ᶜ = "_{\Conid C}"
%format ⟦_⟧ᶜ = ⟦_⟧ ᶜ
%format ⟧ᶜ = ⟧ ᶜ
%format fmapᶜ = fmap ᶜ
%format Algᶜ = Alg ᶜ
%format FoldOpTᶜ = FoldOpT ᶜ
%format fold-opᶜ = fold-op ᶜ
%format algDᶜ = algD ᶜ
%format SCᶜ = SC ᶜ

%format ᶜˢ = "_{\Conid{Cs}}"
%format ⟦_⟧ᶜˢ = ⟦_⟧ ᶜˢ
%format ⟧ᶜˢ = ⟧ ᶜˢ
%format fmapᶜˢ = fmap ᶜˢ
%format Algᶜˢ = Alg ᶜˢ
%format FoldOpTelᶜˢ = FoldOpTel ᶜˢ
%format fold-opᶜˢ = fold-op ᶜˢ
%format FoldOpTelᶜˢ = FoldOpTel ᶜˢ
%format SCᶜˢ = SC ᶜˢ

%format ᵖ = "_{\Conid P}"
%format Dᵖ = D "\kern.5pt" ᵖ
%format SCᵖ = SC ᵖ

%format ᵈ = "_{\Conid D}"
%format ⟦_⟧ᵈ = ⟦_⟧ ᵈ
%format ⟧ᵈ = ⟧ ᵈ
%format fmapᵈ = fmap ᵈ

%format ⁱ = "_{\Conid I}"
%format ˣ = "_{\iden X}"
%format ʸ = "_{\iden Y}"

%format acc = "\cons{acc}"
%format app = "\cons{app}"
%format base = "\cons{base}"
%format con = "\cons{con}"
%format inl = "\cons{inl}"
%format inr = "\cons{inr}"
%format refl = "\cons{refl}"
%format ι = "\textbf{\textiota}"
%format σ = "\textbf{\textsigma}"
%format ρ = "\textbf{\textrho}"
%format π = "\textbf{\textpi}"
%format cΔ = "\textbf{\textDelta}"
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
%format char = "\cons{char}"
%format float = "\cons{float}"
%format word64 = "\cons{word64}"
%format name = "\cons{name}"
%format string = "\cons{string}"
%format clause = "\cons{clause}"
%format absurd-clause = "\cons{absurd\textsf{-}clause}"
%format function = "\cons{function}"
%format data-type = "\cons{data\textsf{-}type}"
%format data-cons = "\cons{data\textsf{-}cons}"
%format tt = "\cons{tt}"
%format false = "\cons{false}"
%format true = "\cons{true}"
%format here = "\cons{here}"
%format there = "\cons{there}"
%format node₀ = "\cons{node_0}"
%format node₂ = "\cons{node_2}"
%format node₃ = "\cons{node_3}"

%format A = "\iden A"
%format A₁ = A ₁
%format B = "\iden B"
%format C = "\iden C"
%format D = "\iden D"
%format Δ = "\iden\Delta"
%format E = "\iden E"
%format F = "\iden F"
%format Ds = "\iden{Ds}"
%format vΓ = "\iden\Gamma"
%format Γ = "\iden\Gamma"
%format I = "\iden I"
%format N = "\iden N"
%format P = "\iden P"
%format PAcc = "\iden P_{" Acc "}"
%format R = "\iden R"
%format T = "\iden T"
%format U = "\iden U"
%format V = "\iden V"
%format X = "\iden X"
%format Y = "\iden Y"
%format a = "\iden a"
%format as = "\iden{as}"
%format alg = "\iden{alg}"
%format args = "\iden{args}"
%format b = "\iden b"
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
%format e = "\iden e"
%format e' = "\iden{e^\prime}"
%format f = "\iden f"
%format f' = "\iden{f^\prime}"
%format fC = "\iden{fC}"
%format fs = "\iden{fs}"
%format Γps = "\iden{\Gamma ps}"
%format h = "\iden h"
%format he = "\iden{he}"
%format hf = "\iden{hf}"
%format hole = "\iden{hole}"
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
%format c₁ = "\iden{c}_1"
%format cₙ = "\iden{c}_n"
%format l = "\iden{l}"
%format lhs = "\iden{lhs}"
%format lt = "\iden{lt}"
%format m = "\iden m"
%format n = "\iden n"
%format ns = "\iden{ns}"
%format p = "\iden p"
%format pars = "\iden{pars}"
%format ps = "\iden{ps}"
%format #ps = "\iden{\#ps}"
%format r = "\iden r"
%format rb = "\iden{rb}"
%format rec = "\iden{rec}"
%format rhs = "\iden{rhs}"
%format s = "\iden s"
%format ss = "\iden{ss}"
%format vσ = "\iden\sigma"
%format t = "\iden t"
%format τ = "\iden\tau"
%format u = "\iden u"
%format v = "\iden v"
%format x = "\iden x"
%format .x = "." x
%format xs = "\iden{xs}"
%format xs' = "\iden{xs^\prime}"
%format y = "\iden y"

%%
%% end of the preamble, start of the body of the document source.
\begin{document}

\setlength{\mathindent}{.5\parindent}

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
Datatype-generic programming is natural and useful in dependently typed languages such as Agda.
However, datatype-generic libraries in Agda are not reused as much as they should be, because traditionally they work only on datatypes decoded from a library's own version of datatype descriptions; this means that different generic libraries cannot be used together, and they do not work on native datatypes, which are preferred by the practical Agda programmer for better language support and access to other libraries.
This paper presents a framework using Agda's elaborator reflection to instantiate datatype-generic programs as, and for, a useful range of native datatypes and functions ---including universe-polymorphic ones--- in programmer-friendly and customisable forms.
Thanks to the power of elaborator reflection, generic programs do not need to be drastically rewritten compared to their traditional forms, making it easy to adapt existing generic libraries and develop new ones.
We expect that datatype-generic libraries built with our framework ---being interoperable with native entities--- will finally be suitable for the toolbox of the practical Agda programmer.
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

%\todo{Replace \emph{representations} by \emph{encodings}}

\section{Introduction}
\label{sec:introduction}

Parametrised by datatype structure, datatype-generic programs~\citep{Gibbons-DGP} are ideal library components since they can be instantiated for a usually wide range of datatypes, including user-defined ones as long as their structures are recognisable by the datatype-generic programs.
Particularly in dependently typed programming~\citep{Stump-Agda-book,Brady-Idris-book, Kokke-PLFA}, datatype-genericity has long been known to be naturally achievable~\citep{Benke-generic-universes,Altenkirch-GP-within-DTP}, and is even more useful for organising indexed datatypes with intrinsic constraints and their operations.
However, there is hardly any datatype-genericity in, for example, the Agda standard library, which instead contains duplicated code for similar datatypes and functions.
The existing dependently typed datatype-generic libraries~\citep{McBride-ornaments,McBride-pivotal,Dagand-functional-ornaments,Diehl-InfIR,Ko-OrnJFP,Allais-binding-syntax-universe-JFP} ---mostly in Agda, which will be our default language--- are not reused as much as they should be either.
What is going wrong?

The major problem, we argue, is the lack of interoperability.
The prevalent approach to datatype-generic programming in Agda (recapped in \cref{sec:recap}) is to construct a family of datatype descriptions and then decode the descriptions to actual datatypes via some least fixed-point operator~|μ|.
Generic programs take descriptions as parameters and work only on datatypes decoded from descriptions.
Although this approach is theoretically rooted in the idea of universe à~la Tarski~\citep{ML-TT73,ML-TT84} and serves as a simulation of a more recent theory of datatypes~\citep{Chapman-levitation} (discussed in \cref{sec:discussion}), it is not what we want:
Generic libraries usually use their own version of datatype descriptions and are incompatible with each other, so only one library can be chosen at a time, which is unreasonable.
Moreover, decoded datatypes are essentially segregated from native datatypes, and there is no point for the Agda programmer to abandon most of the language support and libraries developed for native datatypes in exchange for one generic library.

So what do we want from datatype-generic libraries?
We want to write our own native datatypes and then instantiate generic programs for them.
And in a dependently typed setting, we should be able to instantiate theorems (and, in general, constructions) about native datatypes and functions too.
For a standard example, from the |List| datatype, we want to derive not only its fold operator
\begin{code}
foldr : {A : Set ℓ} {B : Set ℓ'} → (A → B → B) → B → List A → B
foldr f e []        = e
foldr f e (a ∷ as)  = f a (foldr f e as)
\end{code}
but also theorems about |foldr|, such as the following `fold fusion' theorem (which allows us to optimise the composition of a |foldr| and a function~|h| as a single |foldr|):
\begin{code}
foldr-fusion :  {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} (h : B → C)
                {e : B} {f : A → B → B} {e' : C} {f' : A → C → C} →
                (he : h e ≡ e') (hf : ∀ a b c → h b ≡ c → h (f a b) ≡ f' a c)
                (as : List A) → h (foldr f e as) ≡ foldr f' e' as
foldr-fusion h he hf []        = he
foldr-fusion h he hf (a ∷ as)  = hf a _ _ (foldr-fusion h he hf as)
\end{code}
Also important (especially in a dependently typed setting) is the ability to derive new datatypes --- the standard example is the derivation of the vector datatype from list |length|,
\begin{code}
data Vec (A : Set ℓ) : ℕ → Set ℓ where                              length : {A : Set ℓ} → List A → ℕ
  []   :                        Vec A    zero                       length []        = zero
  _∷_  : A → ∀ {n} → Vec A n →  Vec A (  suc n) {-"\hspace{2em}"-}  length (a ∷ as)  = suc (length as)
\end{code}
and subsequently we want to derive constructions about vectors too.
What we want is conceptually simple but immediately useful in practice: automated generation of native entities that had to written manually ---including all the entities shown above--- from datatype-generic programs.

%\todo[inline]{What we really want from generic libraries, using lists and vectors as familiar examples: we want to generate functions for native datatypes as if they are hand-written so that they are efficient to compute (no back-and-forth representation conversions), easy to reason about (again without the conversions and no excessive abstraction), and can fully benefit from whatever language facilities there are (e.g., Agda's interactive features and compiler optimisations); moreover, we want to generate not only, for example, fold operators but also their theorems such as fold fusion; particularly important in a dependently typed setting is the ability to generate new \emph{datatypes}, and then their functions and properties (e.g., algebraic ornamentation and the associated isomorphism); some actual demo}

Luckily, datatype-generic programming has a long history of development in Haskell~\citep{Loh-thesis,Magalhaes-thesis}, where we can find much inspiration for our development in Agda.
Generic programs in Haskell have always been instantiated for native datatypes, so the interoperability problem in Agda does not exist there.
However, generic program instantiation in Haskell traditionally proceeds by inserting conversions back and forth between native and generic representations, causing a serious efficiency problem.
The conversions are even more problematic in Agda because their presence would make it unnecessarily complicated to reason about instantiated functions.
The Haskell community addressed the conversion problem using compiler optimisation~\citep{Magalhaes-inlining} and, more recently, staging~\citep{Pickering-staged-SoP}.
Unfortunately, compiler optimisation does not work for us because instantiated functions are reasoned about even before they are compiled, and they need to be as clean as hand-written code right after instantiation; this need could be met by staging, which is not available in dependently typed languages though.

%\Josh{Old attempts at optimising DGP and why they don't work: There have been many attempts at removing overheads by compiler optimisation, but this is not enough for dependently typed programming, where programs may appear in later types and be reasoned about (and haven’t been processed by the compiler at all).
%And compiler optimisations need to be fine-tuned to produce what we want; why not just generate what we want in the first place?}

Luckily again, in Agda there is something that can take the place of staging for generic program instantiation: elaborator reflection (inspired by Idris~\citep{Christiansen-elaborator-reflection}), through which the Agda metaprogrammer has access to operations for elaborating the surface language to the core.
It turns out that datatype-generic programming and elaborator reflection are a perfect match in Agda.
For example, to express dependency in types, datatype descriptions are usually higher-order and can be somewhat difficult to manipulate, but our transformation from descriptions to native datatypes is surprisingly natural thanks to the `local variable creation' technique~\citep{Nanevski2005,Schurmann2005}, which is easily implemented using a few reflection primitives.
Moreover, there is no need to drastically alter the form of generic programs (such as adding staging annotations) because they can be straightforwardly instantiated with (open-term) normalisation, also a reflection primitive.

%\LT{Staged computation has been proposed to solve the notorious efficiency problem~\cite{Yallop-staged-generic-programming,Pickering-staged-SoP} due to the conversions between generic representations.
%This approach, however, makes generic programs entangled with the staging information, making generic programs even harder to write.
%It will be ideal to keep generic programs from metaprogramming.}
%
%\LT{The use of elaborator reflection is essential to us: type-checking and normalisation, for example, are not available in other metaprogramming paradigms and they are hard to implement in full as this would require essentially rebuilding an elaborator.
%Unlike other approaches using staging~\cite{Yallop-staged-generic-programming,Pickering-staged-SoP} where generic programs are entangled with staging to eliminate the generic representation, the elaborator reflection allows us to normalise a given open term directly.}

We have developed a framework in Agda where datatype-generic programs can be instantiated as, and for, a useful range of native datatypes and functions through elaborator reflection.
We do not need radically new datatype-generic programming techniques, but do need to adapt our datatype descriptions ---restricted to inductive families~\citep{Dybjer1994} in this paper--- to support commonly used Agda features, in particular universe polymorphism~(\cref{sec:parameters}).
Our generic programs instantiate to native entities that are close to hand-written forms, and work on existing native entities ---whose forms can be flexibly customised--- through `connections' to their generic counterparts~(\cref{sec:connections}).
The instantiation macros are a new and natural use case of elaborator reflection~(\cref{sec:reflection}); more generally, we give a Cook's tour of Agda's elaborator reflection (which is less documented), and promote the local name creation technique for handling higher-order syntax.
As a demo, we adapt some existing generic constructions to our framework~(\cref{sec:examples}).
We expect that this work will facilitate the development of practical datatype-generic libraries in Agda, and provide motivations for theoretical investigations~(\cref{sec:discussion}).
Our Agda code is available at \url{https://github.com/Zekt/Type-Embellishment}.

%\Josh{No radically new datatype-generic programming techniques, just adaptations for practical Agda programming (parameters, universe polymorphism, and visibility and curried forms; compare with \citet{Dybjer1994}); pointing out an ignored direction worth following}

%\todo[inline]{
%Contributions:
%
%$\bullet$ Better interoperability with native datatypes and functions (generating new native datatypes and functions, and connecting with existing ones for which generic constructions are specialised)
%
%$\bullet$ Encoding of universe-polymorphic and parametrised inductive families (precise calculation of universe levels)
%
%$\bullet$ A new use case of elaborator reflection where traditional datatype-generic programs are simply normalised to yield native programs (and do not need more radical adaptations like staging)
%
%$\bullet$ Simpler and less error-prone `object-level' binder-manipulating techniques with (Agda's) elaborator reflection (bypassing the manipulation of de Bruijn indices; a tutorial for Agda's reflection mechanism)}

%\todo[inline]{Practically-oriented, inspiring future theories}

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
\begin{minipage}[t]{.5\textwidth}
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
\begin{minipage}[t]{.4\textwidth}
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

There have been quite a few variants of datatype encoding~\citep{Altenkirch-SSDGP,Chapman-levitation,McBride-ornaments,Dagand-functional-ornaments,Ko-OrnJFP}; here we use a three-layered version that closely follows the structure of an Agda datatype definition (comparable to \varcitet{de-Vries-true-SoP}{'s} encoding).
%\footnote{This choice of layered structure has also been adopted elsewhere, for example by \citet{de-Vries-true-SoP}.}
%which has (i)~a list of constructors made up of (ii)~a series of fields, some of which can be (iii)~potentially higher-order recursive occurrences of the datatype being defined.
As a small running example, consider this accessibility datatype:%
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
In general, if there are abuses, they will be detected at the meta-level~(\cref{sec:translation}).}
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
For example, |foldAcc<| is a fold function, and so are a lot of common functions such as list |length|.
The first two steps are the same for all fold functions on the same datatype, whereas the third step is customisable and represented by an algebra, whose argument of type |⟦ D ⟧ᶜˢ X i| represents exactly the input of step~(iii).
We can define a generic |fold| operator that expresses the computation pattern of fold functions and can be specialised with an algebra,
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
(The unsafe \textsc{terminating} pragma is not be a problem because our work does not use |fold|.)
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
This is one of the many problems created by the mismatch between the range of levels we need to handle and the limited power of level quantification;
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
\begin{minipage}[b]{.6\textwidth}
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
  ⟦ A ∷   T  ⟧ᵗ = Σ[ a  ∶ A       ] ⟦ T a ⟧ᵗ
  ⟦ T ++  U  ⟧ᵗ = Σ[ t  ∶ ⟦ T ⟧ᵗ  ] ⟦ U t ⟧ᵗ
\end{code}
\end{minipage}
\caption{(Tree-shaped) telescopes and their semantics as nested |Σ|-types}
\label{fig:telescopes}
\end{figure}

At some point we will need to convert a description to a datatype definition, and it would be unsatisfactory in practice if the parameter and index types in the datatype definition were not in the conventional curried form.
When currying, the encoding of multiple types in one nested |Σ|-type is ambiguous --- how do we know whether a |Σ|-type is supposed to be interpreted as two types, with the latter depending on the former, or just one type?
A natural solution is to use telescopes~\citep{de-Bruijn-telescopes} to represent lists of parameter or index types, as shown in \cref{fig:telescopes}.
Again we use the host language's function space to bring variables of the types in the front of a telescope into the context of the rest of the telescope.
Besides the usual cons constructor `|∷|', we also include a constructor `|++|' for appending telescopes (which requires indexed induction-recursion~\citep{Dybjer-indexed-induction-recursion} to define), making our telescopes tree-shaped; the reason will be clear when we reach \cref{sec:examples}.
The index~|ℓ| in the type |Tel ℓ| of a telescope~|T| is the maximum level appearing in~|T|.
This level is important since it is the universe level of the type |⟦ T ⟧ᵗ|, which is a nested |Σ|-type inhabited by tuples whose components have the types in~|T|.
%More subtly, the indexing also precludes overly universe-polymorphic telescopes like |Level ∷ (λ ℓ → Set ℓ ∷ (λ _ → []))|, since in a cons telescope (and similarly in an appended telescope), the maximum level~|ℓ'| in the tail has to be determined independently from the |A|-typed value in the context.

A couple of syntax declarations will make telescopes slightly easier to write and read:
\begin{code}
syntax _∷_ A (λ x → T) = [ x ∶ A ] T{-"\,"-};{-"\quad"-} syntax _++_ T (λ t → U) = [[ t ∶ T ]] U
\end{code}
For example, the parameters of |Acc| can be represented as |[ A ∶ Set ℓ ] [ R ∶ (A → A → Tel ℓ') ] []| instead of |Set ℓ ∷ (λ A → (A → A → Set ℓ') ∷ (λ R → []))|.

From a telescope~|T| it is straightforward to compute a curried function type |Curriedᵗ T X| which has arguments with the types in~|T|, and ends with a given type |X : ⟦ T ⟧ᵗ → Set ℓ'| that can refer to all the arguments (collectively represented as a tuple of type |⟦ T ⟧ᵗ|):
\pagebreak
\begin{code}
Curriedᵗ : (T : Tel ℓ) → (⟦ T ⟧ᵗ → Set ℓ') → Set (ℓ ⊔ ℓ')
Curriedᵗ []          X = X tt
Curriedᵗ (A  ∷   T)  X = (a : A)          → Curriedᵗ (T a) (λ t  → X (a  , t  ))
Curriedᵗ (T  ++  U)  X = Curriedᵗ T (λ t  → Curriedᵗ (U t) (λ u  → X (t  , u  )))
\end{code}
It is also straightforward to convert between this curried function type and its uncurried counterpart with the functions |curryᵗ : ((t : ⟦ T ⟧ᵗ) → X t) → Curriedᵗ T X| and |uncurryᵗ| in the opposite direction (whose definitions are omitted).
With these, we will be able to compute curried forms of parameters and indices when they appear in types (such as the type of the fold operator of |Acc|).

Incidentally, if we attempt a similar construction for |Level ^ n| (which can be viewed as a kind of specialised telescope) to produce curried forms of level parameters as well,
\begin{code}
CurriedL : (n : ℕ) {f : Level ^ n → Level} → ((ℓs : Level ^ n) → Set (f ℓs)) → Set {! !}
CurriedL    zero    X = X tt
CurriedL (  suc n)  X = (ℓ : Level) → CurriedL n (λ ℓs → X (ℓ , ℓs))
\end{code}
we will not be able to fill in the hole `|{! !}|' since it should be a finite level when |n|~is zero (meaning that there is no level quantification), or~|ω| when |n|~is non-zero, going beyond the current capabilities of Agda's universe polymorphism.
We will rely on elaborator reflection to deal with level parameters in \cref{sec:reflection}.

\subsection{Universe-Polymorphic Descriptions}
\label{sec:universe-polymorphic-descriptions}

\begin{figure}
\codefigure
\begin{minipage}[t]{.41\textwidth}
\begin{code}
record DataD : Setω where field
  #levels  : ℕ
  applyL   : Level ^ #levels → PDataD

record PDataD : Setω where field
  alevel {plevel} {ilevel} : Level
  {struct}    : ConBs
  level-ineq  :  maxMap max-π  struct ⊔
                 maxMap max-σ  struct
                   ⊑ alevel ⊔ ilevel
  Param   :  Tel plevel
  Index   :  ⟦ Param ⟧ᵗ → Tel ilevel
  applyP  :  (ps : ⟦ Param ⟧ᵗ) → ConDs ⟦ Index ps ⟧ᵗ struct
\end{code}
\end{minipage}%
\begin{minipage}[t]{.59\textwidth}
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
For example, in \cref{sec:simple-containers} we will define a datatype-generic predicate |All P| stating that a given predicate~|P| holds for all the elements in a container-like structure; for lists, |All| specialises to
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
\begin{minipage}[t]{.35\textwidth}
\begin{code}
DataT : DataD → Setω
DataT D = ∀ ℓs ps →
  let  Dᵖ == D .applyL ℓs
  in   (is : Dᵖ .Index ps) →
       Set (Dᵖ .alevel ⊔ Dᵖ .ilevel)
\end{code}
\end{minipage}%
\begin{minipage}[t]{.55\textwidth}
\begin{code}
record DataC (D : DataD) (N : DataT D) : Setω where field
  toN        : ⟦ D ⟧ᵈ (N ℓs ps) is  → N ℓs ps is
  fromN      : N ℓs ps is           → ⟦ D ⟧ᵈ (N ℓs ps) is
  fromN-toN  : (ns  : ⟦ D ⟧ᵈ (N ℓs ps) is)   → fromN (toN ns)  ≡ ns
  toN-fromN  : (n   : N ℓs ps is)            → toN (fromN n)   ≡ n
\end{code}
\end{minipage}
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

The introduction of |DataC| supports a symmetric architecture where generic and native entities may grow separately but can be kept in sync (reminiscent of `delta-based bidirectional transformations'~\citep[Section~3.3]{Abou-Saleh-BX-intro}): we may compute a new description from an old one and then manufacture a native datatype from the new description, or write a native datatype and then derive its description; in either case, a connection is established between the generic and native entities at the end.
This architecture generalises the standard one involving~|μ|, where |D|~has a connection only with |μ D|, whereas in our architecture, connections can be established between any pair of description and datatype as long as they correspond.
In particular, the forms of native datatypes and constructors (curried versus uncurried forms, order and visibility of arguments, etc) are not tightly coupled with descriptions (especially datatype-generically computed ones, which usually have prescribed forms) and can be customised by the programmer, which is vital in practice.

\subsection{Fold Connections}
\label{sec:FoldC}

\begin{figure}
\codefigure
\begin{minipage}[t]{.48\textwidth}
\begin{code}
record FoldP : Setω where field
  {Desc}    : DataD
  {Native}  : DataT Desc
  Con       : DataC Desc Native
  #levels  : ℕ
  level    : Level ^ #levels → Level ^ (Desc .#levels)
  applyL   : ∀ ℓs → PFoldP (Desc .applyL (level ℓs))
\end{code}
\end{minipage}%
\begin{minipage}[t]{.52\textwidth}
\begin{code}
record PFoldP (D : PDataD) : Setω where field
  {plevel} {clevel} : Level
  Param    : Tel plevel
  param    : ⟦ Param ⟧ᵗ → ⟦ D .Param ⟧ᵗ
  Carrier  : ∀ ps → ⟦ D .Index (param ps) ⟧ᵗ → Set clevel
  applyP   : ∀ ps → Alg (D .applyP (param ps)) (Carrier ps)

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
The fold function needs a type, which refers to the native datatype on which the fold function operates, so |FoldP| includes a field |Con : DataC| connecting the datatype description |Desc| on which the algebra operates to a |Native| datatype, enabling us to compute the type of the fold function using |FoldT| in \cref{fig:FoldC}.%
\footnote{Agda's |open| statement can be used to bring the fields of an inhabitant of a record type into scope --- for example, the name |Native| in the definition of |FoldT| stands for |F .Native| because of |open FoldP F|.
Moreover, an |open| statement can be used in a |let|-expression to limit its effect to the body of the |let|-expression.}
In the definition of |FoldT|, we also see that the fields |level| and |param| are used to compute the parameters for the native datatype argument from the parameters of the fold function.
So, given |F : FoldP|, it can be connected to some |f : FoldT F|, but what should the connection be?
Since |f|~is supposed to replace an instantiation of the generic |fold| operator, what we need to know about~|f| is that it satisfies a suitably instantiated version of the defining equation of |fold|.
This |equation| constitutes the only field of the record type |FoldC| in \cref{fig:FoldC}.

Incidentally, although we do not present the details of generic induction, the definitions are largely the same as what we have formulated for folds above, including |IndP|, |IndT|, |IndC|, etc.
When we get to examples that require induction in \cref{sec:examples}, it should suffice to think of those generic programs as a more complex kind of parametrised algebras.

\begin{figure}
\codefigure
\begin{minipage}[t]{.41\textwidth}
\begin{code}
FoldT : FoldP → Setω
FoldT F = ∀ ℓs ps {is} →
  let  open FoldP F; open PFoldP (F .applyL ℓs)
  in   Native (level ℓs) (param ps) is →
       Carrier ps is
\end{code}
\end{minipage}%
\begin{minipage}[t]{.59\textwidth}
\begin{code}
record FoldC (F : FoldP) (f : FoldT F) : Setω where field
  equation :
    ∀ {ℓs ps is} → let open FoldP F; open PFoldP (F .applyL ℓs) in
    (ns : ⟦ Desc ⟧ᵈ (Native (level ℓs) (param ps)) is) →
    f ℓs ps (Con .toN ns) ≡ applyP ps (fmapᵈ Desc (f ℓs ps) ns)
\end{code}
\end{minipage}
\caption{Fold connections}
\label{fig:FoldC}
\end{figure}

In this paper we are only interested in manufacturing native fold functions from |FoldP| and establishing |FoldC| at the end, leaving the opposite direction as future work.
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
fold-base F {ℓs} rec =
  let open FoldP F; open PFoldP (F .applyL ℓs) in curryᵗ λ ps → curryᵗ λ is →
  applyP ps ∘ fmapᵈ Desc (λ {is} → uncurryᵗ (uncurryᵗ rec ps) is) ∘ Con .fromN
\end{code}
This definition of |foldAcc|, albeit one deemed non-terminating by Agda, implies the |FoldC.equation| because of the inverse property |DataC.fromN-toN|.
To turn this into a valid definition, we pattern-match the variable~|a| with all the possible constructors, although there is only one in this case:%
\begin{equation}\label{eq:fold-base-before}
|foldAcc A R P p .x (acc x as) = fold-base foldAccP foldAcc A R P p x (acc x as)|
\end{equation}
Now normalise the right-hand side,
\begin{equation}\label{eq:fold-base-after}
|foldAcc A R P p .x (acc x as) = p x (λ y lt → foldAcc A R P p y (as y lt))|
\end{equation}
and this final definition can be directly shown to satisfy the connecting equation
\begin{code}
foldAccC : FoldC foldAccP foldAccT
foldAccC = record { equation = λ { (inl (x , as , refl)) → refl } }
\end{code}
where |foldAccT _ (A , R , P , p , _) {x , _} == foldAcc A R P p x| is a wrapper function.
(The inverse property |DataC.fromN-toN| does not appear in the proof, but we need it at the meta-level to argue generically that the proof always works.)

%Everything we did manually above was highly mechanical and deserves to be automated; this we do next in \cref{sec:reflection} using Agda's reflection mechanism, after which we will see some examples of datatype-generic programming with |DataC| and |FoldC| connections in \cref{sec:examples}.

\section{Establishing Connections Using Elaborator Reflection}
\label{sec:reflection}

To automate the mechanical constructions in \cref{sec:connections}, we use Agda's elaborator reflection to define a set of macros
\begin{enumerate*}[label=(\roman*)]
  \item to translate between fully typed higher-order representations used by generic programs and uni-typed first-order representations used by the reflection framework in \cref{sec:translation};
  \item to generate connections by synchronising two different types of representations in \cref{sec:connection-generation};
  \item to partially evaluate generic programs (\cref{sec:FoldC}) and derive definitions that are comparable, if not identical, to hand-written definitions in \cref{sec:specialising}.
\end{enumerate*}
Regarding elaborator reflection itself, we briefly introduce its basic design in \cref{sec:elab}, and leave explanations of reflection primitives to later sub-sections when needed.
Due to space restrictions, we will only be able to provide sketches in most of this section.
Examples of using the macros are given in \cref{sec:examples}.

\subsection{Elaborator Reflection in Agda} \label{sec:elab}
The reflection API includes the elaborator monad |TC|, a set of |TC| computations, and datatypes ---|Term|, |Pattern|, |Literal|, |Clause|, and |Definition| (\cref{fig:reflected-term,fig:reflected pattern,fig:other-type,fig:clause,fig:definition})--- reflecting the core language where every expression is in weak head normal form and every application is in spine-normal form.
%Type expressions are a part of |Term| but usually marked as |Type| ---a synonym of |Term|--- for clarity.
The type |Arg| decorates a type with an |ArgInfo| about visibility (being implicit or not) and modality; the type |Abs| with a |String| as the binder's name.
For brevity, we often suppress |i : ArgInfo| and a binder's name |s|, so for example we write |pi a b | (a reflected \textPi-type) for |pi (arg i a) (abs s b)|.

\begin{figure}[t]
\codefigure
\begin{minipage}[t]{.55\textwidth}%
\begin{code}
data Term : Set where
  unknown   : Term
  lit       : (l  : Literal)                      → Term
  agda-sort : (s  : Sort)                         → Term
  pi        : (a  : Arg Type)   (b  : Abs Type)   → Term
  lam       : (v  : Visibility) (t  : Abs Term)   → Term
  var       : (i  : Nat)        (xs : Args Term)  → Term
  con       : (c  : Name)       (xs : Args Term)  → Term
  def       : (f  : Name)       (xs : Args Term)  → Term
  pat-lam   : (cs : Clauses)    (xs : Args Term)  → Term
  meta      : (x  : Meta)       (xs : Args Term)  → Term
\end{code}
\end{minipage}%
\begin{minipage}[t]{.45\textwidth}%
\begin{code}
data Sort    : Set where
  set      : (t  : Term)   → Sort
  lit      : (n  : Nat)    → Sort
  prop     : (t  : Term)   → Sort
  propLit  : (n  : Nat)    → Sort
  inf      : (n  : Nat)    → Sort
  unknown  : Sort

data Arg (A : Set)  : Set where
  arg  : (i : ArgInfo)  (x : A) → Arg A

data Abs (A : Set)  : Set where
  abs  : (s : String)   (x : A) → Abs A
\end{code}
\end{minipage}%
\caption{Reflected expressions}\label{fig:reflected-term}
\end{figure}

\begin{figure}[t]
\codefigure
\begin{minipage}[t]{.34\textwidth}%
\begin{code}
data Pattern where
  con     : (c : Name) (ps : Patterns)
          → Pattern
  proj    : (f : Name)     → Pattern
  var     : (i : ℕ)        → Pattern
  absurd  : (i : ℕ)        → Pattern
  lit     : (l : Literal)  → Pattern
  dot     : (t : Term)     → Pattern
\end{code}
\end{minipage}%
\begin{minipage}[t]{.33\textwidth}
\begin{code}
data Literal : Set where
  nat     : (n : Nat)      → Literal
  word64  : (n : Word64)   → Literal
  float   : (x : Float)    → Literal
  char    : (c : Char)     → Literal
  string  : (s : String)   → Literal
  name    : (x : Name)     → Literal
  meta    : (x : Meta)     → Literal
\end{code}
\end{minipage}%
\begin{minipage}[t]{.33\textwidth}
\begin{code}
postulate
  Name  : Set
  Meta  : Set
Args A     =  List (Arg A)
Type       =  Term
Telescope  =  List (String × Arg Type)
Names      =  List Name
Patterns   =  List Pattern
\end{code}
\end{minipage}
\par
\begin{minipage}[t]{.34\textwidth}
\caption{Reflected patterns}\label{fig:reflected pattern}
\end{minipage}%
\begin{minipage}[t]{.66\textwidth}
\caption{Other types and abbreviations for reflection}\label{fig:other-type}\label{fig:type abbrs}
\end{minipage}%
\end{figure}

The quotation of an expression~|e| can be obtained by |quoteTerm e| and the resolved unique name for a definition~|f| or a constructor by |quote f|.
For example, |quoteTerm acc| is |con (quote acc) []|, where the empty list~|[]| indicates that no arguments follow the |acc| constructor.

The |TC| monad (short for `type-checking monad'~\citep{Agda}) stores states needed for elaboration such as the context of the call site, the scope of names with its definition, the set of metavariables and so forth.
A macro~|f| is a definition of type |A₁ → ... → Term → TC ⊤| declared with keyword |macro|.
When executed during elaboration, the call site of~|f| becomes a metavariable~|x| supplied as the last argument of~|f| for manipulation inside~|f|.
A minimal example is
\begin{code}
macro  give = unify
\end{code}
where we declare the primitive |unify : Term → Term → TC ⊤| unifying two expressions as a macro.
Elaborating |give e| would splice the given expression |e : Term| in place of the call, if Agda did nothing to its argument |e|.
In fact, Agda quotes macro arguments of types |Term| and |Name| upon invocation, so elaborating |give e| amounts to running |unify (quoteTerm e) (meta x [])|. 
Afterwards, the call site becomes~|e| (and is elaborated again).
In general, we can compute whatever expression we need inside a macro and then place it at the call site by unifying it with~|x|.

\begin{figure}[t]
\begin{minipage}[t]{.53\textwidth}
\codefigure
\begin{code}
data Clause : Set where
  clause  : (Δ : Telescope) (lhs : Patterns) (rhs : Term)
          → Clause
  absurd-clause : (Δ : Telescope) (lhs : Patterns) → Clause

Clauses = List Clause
\end{code}
\caption{Clauses}\label{fig:clause}
\end{minipage}%
\begin{minipage}[t]{.47\textwidth}
\codefigure
\begin{code}
data Definition : Set where
  data-type   : (#ps  : ℕ)  (cs   : Names)    → Definition
  data-cons   :             (d    : Name)     → Definition
  function    :             (cls  : Clauses)  → Definition
  ...
\end{code}
\caption{A snippet of reflected declarations}
\label{fig:definition}
\end{minipage}%
\end{figure}
\subsection{Translating Higher-Order Representations with Local Variable Creation}\label{sec:translation}

This section's main task is to translate |DataD|, a fully typed higher-order representation, into the reflected language to declare native datatypes.
The reflected language is, by contrast, a uni-typed first-order representation using de Bruijn indices and \emph{not} hygiene, posing a challenge.
Rather than presenting the full detail, it suffices to see how telescopes~(\cref{fig:telescopes}) are handled to get the essence of the translation.
For example, the tree-shaped telescope |[[ (A , _) ∶ [ _ ∶ Set ] [] ]] [ _ ∶ (A → A) ] []| of type |Tel (lsuc lzero)| should be translated to this (flattened) list of reflected types
\begin{equation}\label{eq:telescope}
|`Set ∷ pi (var 0 []) (var 1 []) ∷ [] : Telescope|
\end{equation}
where the type |Telescope| is defined in \cref{fig:type abbrs}, and the variables |var 0 []| and |var 1 []| in |pi| both refer to the quotation $|`Set| = |agda-sort (lit 0)|$ of |Set|.

One obvious approach is to analyse the quotation of |T : Tel ℓ|.
Such a macro needs to analyse abstract syntax trees \emph{modulo judgemental equality} --- it has to check which case is being analysed by reducing, say, a reflected expression |def (quote f) xs| for a definition $f$ to one of the three cases |con (quote Tel.[]) []|, |con (quote Tel._∷_) xs|, and |con (quote Tel._++_) xs|.
This approach is error-prone, and moreover, Agda fails to check if the macro terminates or not.

Instead, let us pattern-match against |T : Tel ℓ|.
The case for the empty telescope |[]| is simple to define but the other two cases |A :: T| and |U ++ V| seem impossible:
\begin{code}
fromTel : Tel ℓ → TC Telescope
fromTel  []         = return []
fromTel  (A ∷   T)  = ... fromTel (T ?) ...
fromTel  (U ++  V)  = ... fromTel (V ?) ...
\end{code}
Note that |T|~is a function from |A|, and |V|~a function from |⟦ U ⟧ᵗ|, for some \emph{arbitrary} |A|~and~|U|; how do we give their arguments?
We solve this problem by creating a \emph{local variable}.
The |TC| monad stores the context during elaboration, which can be extended by a variable of a given type to run a |TC| computation locally, using the primitive $|extendContext| : |Type → TC A → TC A|$.
The first argument of |extendContext| is a reflected type, which should be the quotation of the actual value of~|A|, which is not known until elaboration and thus cannot be obtained by |quoteTerm|; to obtain the quotation, we use the primitive $|quoteTC| : |A → TC Term|$.
Then, in the second argument of |extendContext|, the local variable can be actually brought into scope by another primitive $|unquoteTC| : |Term → TC A|$ which unquotes a given reflected expression within the |TC| monad.
The above construction amounts to a |TC| computation
\begin{code}
exCxtT : (B : Set ℓ) → (Type → B → TC A) → TC A
exCxtT B f = do  `B ← quoteTC B
                 extendContext `B (unquoteTC (var 0 []) >>= λ x → f `B x)
\end{code}
which creates a local variable~|x| of type~|B| for use in a |TC| computation~|f|.

As for |⟦ U ⟧ᵗ|, if we merely created a local variable |u : ⟦ U ⟧ᵗ|, then each reference to a component of |u| would be formed by projections |fst| and |snd|. 
For example, instead of \eqref{eq:telescope} we would have
\begin{code}
  `Set :: pi (def (quote fst) ((var 0 []) :: [])) (def (quote fst) ((var 1 []) :: [])) :: [] 
\end{code}
To eliminate projections, we create a list of local variables for each type in |U : Tel ℓ| as a tuple and give it to a |TC| computation (\Cref{fig:exCxtTel}).
The last two cases of |fromTel| can then be defined by
\begin{code}
fromTel (A ∷ T) = do  {-"\hspace{4em}"-}  fromTel (U ++ V) = do  Γ ← fromTel U
  exCxtT A λ `A x → do                                           exCxtTel U λ u → do
    Γ ← fromTel (T x)                                            {-"\quad"-}  Δ ← fromTel (V u)
    return (`A ∷ Γ)                                                           return (Γ ++ Δ)
\end{code}
As long as local variables are not pattern-matched, the computation can proceed.
Indeed, we are exploiting the fact that our representations are used as if they are higher-order abstract syntax!

\begin{figure}[t]
\codefigure
\begin{minipage}[t]{.5\textwidth}
\begin{code} 
exCxtTel : (T : Tel ℓ) (f : ⟦ T ⟧ᵗ → TC A) → TC A
exCxtTel []        f  = f tt
exCxtTel (A ∷ T)   f  = exCxtT A λ _ x →
  exCxtTel (T x) λ t → f (x , t)
exCxtTel (T ++ U)  f  = exCxtTel T λ t →
  exCxtTel (U t) λ u → f (t , u)
\end{code}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\begin{code} 
exCxtℓs : (n : ℕ) (f : Level ^ n → TC A) → TC A
exCxtℓs  zero      f  = f tt
exCxtℓs  (suc n)   f  = exCxtT Level λ _ ℓ →
  exCxtℓs n λ ℓs → f (ℓ , ℓs)
\end{code}
\end{minipage}
\par
\begin{minipage}[t]{.5\textwidth}
\caption{Context extension by |T : Tel ℓ|} 
\label{fig:exCxtTel}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\caption{Context extension by |Level|'s} 
\label{fig:exCxtls}
\end{minipage}%
\end{figure}

For the rest of the task we can only provide a sketch.
To handle |D : DataD|, a |TC| computation |defineByDataD| is defined using the same local variable creation technique, but to apply |D .applyL : Level ^ #levels → PDataD| we need a variant |exCxtℓs| (\cref{fig:exCxtTel}) which extends the context by a list of |Level| variables.
To actually define a datatype described by |D : DataD|, we have extended Agda's |unquoteDecl| mechanism to allow macros to declare datatypes, and can write
\begin{code}
  unquoteDecl data d constructor c₁ ... cₙ = defineByDataD D d (c₁ :: ... :: cₙ :: [])
\end{code}
to introduce a datatype~|d| and its constructors |c₁|,~\ldots,~|cₙ| into the scope.
(The declaration form is somewhat verbose, but is chosen so that Agda's scope- and type-checking can be kept unchanged.)

Conversely, we also have a macro |genDataD| that expands to a description of a native datatype~|N|.
This direction is syntactical and unsurprising though --- for example, telescopes are handled by
\begin{code}
to`Tel : Telescope → Term
to`Tel = foldr (λ `A `T →  `A `∷ `T) `[]
\end{code}
where $|`[]| = |con (quote Tel.[]) []|$ and $|`A `∷ `T| = |con (quote Tel._∷_) (`A ∷ lam `T ∷ [])|$.

%The implementation of |defineByDataD| is similar to |fromTel| and omitted.
%so we refrain ourself from the nitty-gritty details. 
%Moreover, the level of a datatype specified by |alevel ⊔ ilevel| and the telescopes |Param| and |Index| for parameters and indices are given separately in |PDataD| which may refer to level parameters introduced by |applyL|, but
%to define a datatype via reflection a reflected $\Pi$-type is used for the datatype signature consisting of the telescopes of parameters.
%Hence we need to compose the quotation of |Set (alevel ⊔ ilevel)| with the quotation of |Param| and |Index| to form a reflected $\Pi$-type.
%One possible way to achieve this is to take the quotation of |Set (alevel ⊔ ilevel)| first and weaken its de Bruijn indices by the number of datatype parameters and indices.
%Alternatively, we extend the context by |Param ++ Index| using |exCxtTel| first and take the quotation that can be composed with |fromTel (Param ++ Index)| to form the desired $\Pi$-type directly.
%Other parts of the translation become rather straightforward.
%In fact, we do not manipulate de Bruijn indices at all to translate from |DataD|.
%(and is defined with primitives |getDefinition| and |getType|).
%The macro can be invoked as |genDataD Acc| to generate a description identical to |AccD| in \cref{sec:DataD}.
%This direction of translation involves strengthening indices to decompose the quotation of a datatype signature, sadly.

%Similarly, the bulk of the translation from |FoldP| to a recursive function relies on the creation of a local variable by |fromTel|.
%The elimination of intermediate conversions during instantiating generic functions will be discussed the detail in \cref{sec:specialising}. 
\subsection{Generating Wrappers and Connections}
\label{sec:connection-generation}

Our next task is generating |DataT|, |DataC|, and |FoldC|~(\cref{fig:DataC,fig:FoldC}).
Their main ingredients are functions, which we define by pattern-matching \textlambda-expressions, reflected as |pat-lam| in \cref{fig:reflected-term}.
We will focus on |DataT| and omit |DataC| and |FoldC|, which are handled similarly.
For example, we should generate the datatype wrapper |AccT| as
\begin{code}
λ { {ℓ , ℓ' , tt} (A , R , tt) (as , tt) → Acc {ℓ} {ℓ'} {A} R as }
\end{code}
where all the implicit arguments are given.
To construct the |pat-lam|, we need to construct a clause whose left-hand side consists of patterns in the form of uncurried tuples of variables (which in general can be tree-shaped), and whose right-hand side is the native datatype applied to a list of curried arguments.
Moreover, we need to assign the right visibilities to the arguments of |Acc|.

The macro |genDataT| that expands to a suitable pattern-matching \textlambda-expression is
\begin{code}
macro  genDataT : DataD → Name → Term → TC ⊤
       genDataT D d hole = do  `D ← quoteωTC D
                               checkType hole (def (quote DataT) (`D ∷ []))
                               uncurryDataD D d >>= unify hole
\end{code}
where $|uncurryDataD| : |DataD → Name → TC Term|$ does the real work (explained below), before which the primitive $|checkType| : |Term → Type → TC Term|$ effectively provides a type annotation so that, for example, we can write $|AccT| = |genDataT AccD Acc|$ without giving its type.

%with lists or tuples of variables and the argument information accordingly while traversing a telescope, a $\Pi$-type, or a tree-shaped higher-order telescope |T : Tel ℓ|.
As for |uncurryDataD|, first we need to explain how clauses are given.
A clause takes the form $|Δ| \vdash \overline{p} \hookrightarrow e$ (\cref{fig:clause}) where $\overline{p}$ is a list of patterns and $e$~a reflected expression; the types of the variables in~$\overline{p}$ are specified in the context~|Δ|.
It may appear that the context~|Δ| needs to be fully specified beforehand, but actually it is not the case.
This is because the reflected language plays the dual role of unchecked input and checked output of the elaborator~\cite{Cockx2020}: the context of a checked clause is fully specified, whereas the context of an unchecked clause, which has the form $\overline{p} \hookrightarrow e$, can simply be filled with |unknown|'s.
So |uncurryDataD| only needs to give $\overline{p}$~and~$e$ for each clause:
Each pattern in~$\overline{p}$ is computed from a |Tel| by labelling the elements with de Bruijn indices and replacing every `|∷|'~or~`|++|' with a (reflected) pair constructor and `|[]|' with the quotation of |tt|.
And $e$~is computed by applying the native datatype~|d| to a list of de Bruijn indices paired with their visibilities, which are obtained with the help of the primitives $|getDefinition| : |Name → TC Definition|$ and $|getType| : |Name → TC Type|$.

%whose length is the number of variables used in the clause.
%To generate a wrapper function, it suffices to generate a pattern-matching \textlambda-expression consisting of unchecked clauses and then type-check it using the primitive |checkType|.
%\begin{enumerate*}[label=(\roman*)]
%  \item either check the function against its type |DataT D| as a pattern-matching lambda by the primitive |checkType|, 
%  \item or define the function by the primitives |defineFun| and |declareDef|.
%\end{enumerate*}

%Another issue to deal with is the visibility of an argument.
%The two types |(x : A) → B x| and |{x : A} → B x| are different, so a single program is not possible to uncurry a function regardless of the visibility of its arguments.
%Their quotation |pi `A `B| are, however, essentially the same, so the obstacle just disappears for metaprogramming.

%The native datatype to wrap or to connect can be provided by the user possibly with different choices of visibility (but in the same order) that are not and should not be specified by datatype descriptions or generic programs, so we have to visit and compare two different types of representations from both sides.
%For example, to check if a datatype |N| matches a description |D : DataD|, we have a |TC| computation |_⊆ᵗ?_| (\cref{fig:compare-tel-telescope}) that checks if |T : Tel ℓ| is a prefix of |Γ : Telescope| and returns a partition of |Γ|.\footnote{%
%Note that |unify| in \cref{fig:compare-tel-telescope} is used to check the equivalence between types (instead of just unifying some |e : Term| with a metavariable), since a unifier is indeed an equivalence~\cite{Cockx2016,Cockx2018}.}
%We also have a |TC| computation |telToVars| to generate a tuple and a list of variables based on a given |T : Tel ℓ| with a tuple and a list of arguments |Arg Term| based on the quotation of the type of a datatype, since the shape of a tuple such as |(A , R , _)| is specified by |Param| in |PDataD| but the visibility of arguments is by the type of datatype.

%\begin{figure}[t]
%\codefigure
%\begin{minipage}[t]{.6\textwidth}
%\begin{code}
%_⊆ᵗ?_  : Tel ℓ → Telescope → TC (Telescope × Telescope)
%(A ∷ T)   ⊆ᵗ? (`B ∷ Γ)  = do
%  `A ← quoteTC A
%  (HL (unify `A `B))
%  exCxtT A λ _ x → do
%    (vs , Δ) ← T x ⊆ᵗ? Γ
%    return (`B ∷ vs , Δ)
%\end{code}
%\end{minipage}%
%\begin{minipage}[t]{.4\textwidth}
%\begin{code}
%[]        ⊆ᵗ? Γ         = return ([] , Γ)
%(T ++ U)  ⊆ᵗ? Γ         = do
%  (vs , Γ) ← T ⊆ᵗ? Γ
%  exCxtTel T λ t → do
%    (ws , Γ) ← U t ⊆ᵗ? Γ
%    return (vs <> ws , Γ)
%(A ∷ T)   ⊆ᵗ? []        = typeError ...
%\end{code}
%\end{minipage}
%\caption{The prefix comparison of a higher-order telescope with a first-order telescope}
%\label{fig:compare-tel-telescope}
%\end{figure}

%We have macros |genDataT|, |genDataC|, |genFoldC|, etc.\ in our framework.
%In particular the wrapper |AccT| and connections |AccC| and |foldAccC| in \cref{sec:connections} are generated respectively by 
%\begin{code}
%AccT  = genDataT  AccD  Acc    {-"\hspace{3em}"-}   foldAccC = genFoldC foldAccP foldAcc
%AccC  = genDataC  AccD  AccT
%\end{code}

\subsection{Instantiating Generic Functions with Normalisation}
\label{sec:specialising}

Finally, we define a |TC| computation |defineFold|~(\cref{fig:defineFold}) to instantiate a given |F : FoldP| as a native function~|f| by
\begin{enumerate*}[label=(\roman*)]
  \item generating the instantiated type using |FoldNT|, 
  \item generating a clause for each constructor of the datatype specified in~|F|, and
  \item normalising these clauses.
\end{enumerate*}

For step~(i), if we simply normalise, say, |∀ {ℓs} → FoldNT foldAccP ℓs|, then we will have
\begin{code}
∀ {ℓs : Level ^ 3} (A : Set (fst (snd ℓs))) (R : A → A → Set (fst (snd (snd ℓs)))) → ...
\end{code}
instead of the preferred curried form shown in \cref{sec:FoldC}.
As discussed in \cref{sec:telescopes}, we have to separately curry the level parameters with reflection after normalising the rest of the type, namely |FoldNT F ℓs|.
But where does the variable |ℓs| come from?
We reuse |exCxtℓ|~(\cref{fig:exCxtls}) to extend the context with |(F .#levels)| many |Level| variables and collect those variable in a tuple~|ℓs|, so that the expression |FoldNT F ℓs| makes sense and can be normalised with the primitive $|normalise| : |Term → TC Term|$.
It remains to add quantification over the same number of |Level| variables we extend with (which is carried out by |addLevels|).
Finally, we declare the type of~|f| as the one we just generated using the primitive $|declareDef| : |Name → Type → TC ⊤|$.

%Let us first consider the clause generation defined as |conClause|. 
For step~(ii), we use the primitive $|getDefinition| : |Name → TC Definition|$ to get the list~|cs| of constructor names of the datatype |F .Native|, and generate the clause for each constructor.
Abstracted from~\eqref{eq:fold-base-before}, each clause has the form
\begin{equation} \label{eq:clause}
  |Δ| \vdash \overline{\Varid{ℓ}}\; \overline{p}\;\overline{x}\;(c_i\;\overline{a}) \hookrightarrow 
  \Varid{fold-base}\;F\;\{\Varid{ℓ}_1, \dots , \Varid{ℓ}_n, \Conid{tt}\}\;f\;\overline{p}\;\overline{x}\;(c_i\;\overline{a})
\end{equation}
where $\overline{\Varid{ℓ}}$ is the list of level parameters, $\overline{p}$ the ordinary parameters, $\overline{x}$ the indices, and $\overline{a}$ the constructor arguments.
In general, the context~|Δ| needs to be given because it will be used by the elaborator to determine the types of the variables when the right-hand side of \eqref{eq:clause} ---call it~|e|--- is normalised.
But in this case only the length of~|Δ| needs to be specified, since all types will be determined upon synthesising the type of~|e|, which is the first step of normalisation.
Moreover, the patterns $\overline{x}$ are forced since the values of indices is determined by pattern-matching with $c_i\;\overline{a}$.
It follows that $\overline{x}$ can be given as $\overline{\cons{unknown}}$ on both sides.
Therefore, we only need to generate a simpler clause
\begin{equation}\label{eq:clause'}
  \overline{\Varid{ℓ}}\;\overline{p}\;\overline{\cons{.unknown}}\;(c_i\;\overline{a}) \hookrightarrow \Varid{fold-base}\;F\;\{\Varid{ℓ}_1,\dots,\Varid{ℓ}_n,\Conid{tt}\}\;f\;\overline{p}\;\overline{\cons{unknown}}\;(c_i\;\overline{a})
\end{equation}
for each constructor~$c_i$. 

%In short, the first two steps of |defineFold| are given as 
%where |`type| is the reflected type for the instantiated function |f|, |FoldPToNativeName| revolves the name |N| of the datatype |F .Native|, |getDataDefinition| retrieves the datatype definition (\Cref{fig:definition}).

%needs to be normalised to eliminate~|ℓs| using another primitive |normalise|.
%For efficiency, Agda provides a primitive |withNormalisation| where primitives in a |TC| computation normalise their results.
%For example, |quoteTC! x = withNormalisation true (quoteTC x)| normalises a term~|x| before returning its quotation.

For step (iii), we normalise the right-hand side of \eqref{eq:clause'} within a context extended with variables from the left-hand side of \eqref{eq:clause'} and obtain the list of clauses with normalised expressions on the right-hand side as the result of |mapRHS normalise cls|.
Then, we define the function |f| by the primitive $|defineFun| : |Name → List Clause → TC ⊤|$ with the clauses we just obtained.

%To define a function $f$ by reflection by |F|, for example, the following declaration 
%\begin{code}
%unquoteDecl foldAcc  = defineFold  foldAccP  foldAcc
%\end{code}
%defines the very same function |foldAcc| in \cref{sec:FoldC} modulo variable renaming. 
%Similarly, we also have defined |defineInd| in our framework for inductive programs |I : IndP|.

\begin{figure}
\codefigure
\begin{code}
defineFold : FoldP → Name → TC ⊤
defineFold F f = let open FoldP F in do
-- step (i)
  `type ← addLevels #levels <$> exCxtℓs #levels λ ℓs → normalise =<< quoteTC (FoldNT F ℓs)
  declareDef f `type
-- step (ii)
  cls ← caseM (getDefinition =<< FoldPToNativeName F) of λ
          {  (data-type pars cs)  → exCxtℓs #levels λ ℓs → forM cs (conClause pars #levels)
          ;  _                    → typeError [] }
-- step (iii)
  defineFun f =<< mapRHS normalise cls
\end{code}
\caption{Definition of the |TC| computation |defineFold|}
\label{fig:defineFold}
\end{figure}

\section{Examples}
\label{sec:examples}

As a demo of our framework, here we provide some samples of generic constructions that should have been made available to the Agda programmer.
To be more precise, these constructions are not new (or not too novel compared to those in the literature), but they have not been in the main toolbox of the Agda programmer, who prefers to work with native datatypes and functions;
our framework makes it possible to instantiate these constructions for native entities.
We will omit the details except those related to the design of our framework, and briefly discuss mechanisms that could make these constructions more convenient to use.

\subsection{Fold Operators}
\label{sec:fold-operators}

The generic program that instantiates to fold operators on native datatypes is given the type
\begin{code}
fold-operator : (C : DataC D N) → FoldP
\end{code}
%For example, the fold program |foldAccP| can be obtained as |fold-operator AccC|.
As an example of instantiating the generic program, suppose that we have written the datatype |Acc| manually, and want to derive its fold operator.
First we generate the description |AccD| by the macro |genDataD Acc|, and then the datatype connection |AccC| by |genDataC AccD (genDataT AccD Acc)|.
Now |fold-operator AccC| is exactly the fold program |foldAccP|, and the fold operator/function |foldAcc| can be manufactured from |foldAccP| by
\begin{code}
unquoteDecl foldAcc = defineFold foldAccP foldAcc
\end{code}
and connected with |foldAccP| by |genFoldC foldAccP foldAcc|.
(The macros are manually invoked for now, but the process could be streamlined as, say, pressing a few buttons of an editor.)

Let us look at |fold-operator| in a bit more detail.
The ordinary parameters of |fold-operator C| are mainly a |⟦ D ⟧ᵈ|-algebra in a curried form, so the work of |fold-operator| is purely cosmetic:
at type level, compute the types of a curried algebra, which are the curried types of the constructors of~|D| where all the recursive fields are replaced with a given carrier, and at program level, uncurry a curried algebra.
The level parameters of |fold-operator C| include those of~|D| and one more for the carrier~|X| appearing in the |Param| telescope shown below, which also contains the ordinary parameters of~|D| and a curried algebra represented as a telescope computed (by |FoldOpTel|) from the list of constructor descriptions in~|D|:
\begin{code}
fold-operator {D} C .applyL (ℓ , ℓs) .Param
  = let Dᵖ == D .applyL ℓs in  [[ ps ∶ Dᵖ .Param ]] [ X ∶ Curriedᵗ (Dᵖ .Index ps) (λ _ → Set ℓ) ]
                               FoldOpTel (Dᵖ .applyP ps) (uncurryᵗ X)
\end{code}
%(The reader may want to compare this generic definition with the instantiated |Param| field of |foldAccP|.)
The type of~|X| is in a curried form, which is then uncurried for |FoldOpTel| and other parts of the definition of |fold-operator|, for example the |Carrier| field:
\begin{code}
fold-operator C .applyL (ℓ , ℓs) .Carrier = λ (ps , X , calgs) → uncurryᵗ X
\end{code}
This is a recurring pattern (which we first saw in \cref{sec:DataC}): curried forms are exposed to the library user, whereas uncurried forms are processed by generic programs.
The pattern is also facilitated by the telescope-appending constructor, which appears in |Param| above (disguised with the syntax~|[[ ... ]]|): the parameters are instantiated in a curried form for the library user, but for generic programs they are separated into three groups |ps|, |X|, and |calgs|, making it convenient to refer to each group like in |Carrier| above.

%Part~(i) is computed by
%\begin{code}
%FoldOpTel :  (D : ConDs I cbs) → (I → Set ℓ) →
%             Tel (maxMap max-π cbs ⊔ maxMap max-σ cbs ⊔ hasCon? ℓ cbs)
%FoldOpTel []        X = []
%FoldOpTel (D ∷ Ds)  X = [ _ ∶ FoldOpT D X ] FoldOpTel Ds X
%\end{code}
%which converts each constructor description to a type by |FoldOpT| and collects the types in a telescope.
%The actual conversion by |FoldOpT| produces the required curried type:
%\begin{code}
%FoldOpT : (D : ConD I cb) → (I → Set ℓ) → Set (max-π cb ⊔ max-σ cb ⊔ ℓ)
%FoldOpT (ι i     ) X = X i
%FoldOpT (σ A  D  ) X = (a : A)   → FoldOpT (D a) X
%FoldOpT (ρ D  E  ) X = ⟦ D ⟧ʳ X  → FoldOpT E X
%\end{code}

%For part~(ii), we are given a list of functions of the types in a telescope computed by |FoldOpTel|, from which we should construct an algebra; this is done by performing a case analysis on the argument of the algebra ---which is a sum structure--- to determine which function to apply:
%\begin{code}
%fold-op : (D : ConDs I cbs) → ⟦ FoldOpTel D X ⟧ᵗ → Alg D X
%fold-op (D ∷ Ds) (f , fs) (inl  xs) = fold-opᶜ  D   f   xs
%fold-op (D ∷ Ds) (f , fs) (inr  xs) = fold-op   Ds  fs  xs
%\end{code}
%The task of the next layer |fold-opᶜ| is also constructing a |D|-algebra, but here |D|~is a single constructor description (|ConD|) rather than a list of constructor descriptions (|ConDs|).
%For convenience, define
%\begin{code}
%Algᶜ : ConD I cb → (I → Set ℓ) → Set _
%Algᶜ D X = ∀ {i} → ⟦ D ⟧ᶜ X i → X i
%\end{code}
%so that the type of |fold-opᶜ| can be written in a form corresponding to the type of |fold-op|:
%\begin{code}
%fold-opᶜ : (D : ConD I cb) → FoldOpT D X → Algᶜ D X
%fold-opᶜ (ι  i     ) x  refl           = x
%fold-opᶜ (σ  A  D  ) f  (a   , xs   )  = fold-opᶜ (  D a)  (f  a   ) xs
%fold-opᶜ (ρ  D  E  ) f  (xs  , xs'  )  = fold-opᶜ    E     (f  xs  ) xs'
%\end{code}
%The definition of |fold-opᶜ| is essentially uncurrying, gradually applying a given function to the argument of the algebra --- which is a tuple.

It would not be too interesting if we could only manufacture functions but not prove some of their properties.
For fold operators, one of the most useful theorems is the fusion theorem~\citep{Bird-AoP}, of which |foldr-fusion| in \cref{sec:introduction} is an instance.
The interface to the theorem is
\begin{code}
fold-fusion : (C : DataC D N) (fC : FoldC (fold-operator C) f) → IndP
\end{code}
where the fold connection~|fC| is used to quantify over functions~|f| that are fold operators of~|N|.
Although the version of |foldr| in \cref{sec:introduction} is not manufactured by |defineFold| from the fold program $|foldListP| = |fold-operator ListC|$ (where |ListC| is the datatype connection for |List|) and the arguments of |foldr| are in a different order from that specified by |foldListP|, there is no problem instantiating |fold-fusion| for |foldr|: in this case we can still manually write a wrapper $|foldrT| = |λ _ ((A , _) , B , e , f , _) → foldr f e| : |FoldT foldListP|$ and manufacture a fold connection |foldrC| by |genFoldC' foldListP foldrT|, and then |fold-fusion ListC foldrC| instantiates to |foldr-fusion|.

In general, if the library user is not satisfied with the form of a manufactured function (argument order, visibility, etc), they can print the function definition, change it to a form they want, and connect the customised version back to the library in the same way as we treated |foldr|.
This customisation can be tiresome if it has to be done frequently, however, and there should be ways to get the manufactured forms right most of the time.
We have implemented a cheap solution where argument name suggestions (for definition-printing) and visibility specifications are included in |FoldP| (and |IndP|) and processed by relevant components such as |Curriedᵗ|, and the solution works well for our small selection of examples.
More systematic solutions are probably needed for larger libraries though, for example name suggestion based on machine learning~\citep{Alon-code2vec} and visibility calculation by analysing which arguments can be inferred by unification.

\subsection{Algebraic Ornamentation}
\label{sec:algebraic-ornamentation}

Ornaments~\citep{McBride-ornaments} are descriptions of relationships between two structurally similar datatype descriptions, one of which has more information than the other.
For example, after computing the descriptions |ListD| and |NatD| of |List| and~|ℕ| using |genDataD|, the following ornament states that |List| ---having an additional element field--- is a more informative version of~|ℕ|:
\begin{code}
ListO : DataO ListD NatD
ListO = record { level = λ _ → tt ;{-"~~"-} applyL = λ (ℓ , _) → record
  { param = λ _ → tt;{-"~~"-} index = λ _ _ → tt;{-"~~"-} applyP = λ _ → ι ∷ ∺ (cΔ[ _ ] ρ ι ι) ∷ ∺ [] } }
\end{code}
Do not worry about the details --- the point here is that it is not difficult to write ornaments between concrete datatypes (and it will be even easier if there is a (semi-)automatic inference algorithm~\citep{Ringer-ornaments-Coq} or an editing interface showing two datatypes side by side and allowing the user to mark their differences intuitively).
%Moreover, the ornament is the only thing the user needs to write to derive all the entities related to |List| and~|ℕ| below.

The first thing we can derive from an ornament is a forgetful function; in the case of |ListO|, the derived forgetful function is list |length|, which discards the additional element field.
More can be derived from special kinds of ornaments, with a notable example being `algebraic ornaments'.
In our formulation, given a fold program |F : FoldP| we can compute a more informative version of the description~|F .Desc| and an ornament between them:
\begin{code}
AlgD : FoldP → DataD{-"\,"-};{-"\quad"-} AlgO : (F : FoldP) → DataO (AlgD F) (F .Desc)
\end{code}
The new datatype described by |AlgD F| has the parameters of~|F| and an extra index that is the result of the fold corresponding to~|F|.
For example, the following datatype of `algebraic lists'~\citep{Ko-metamorphisms-in-Agda} can be obtained by applying the macro |defineByDataD| to the description |AlgD (fold-operator ListC)|:
\begin{code}
data AlgList {A : Set ℓ} {B : Set ℓ'} (e : B) (f : A → B → B) : B → Set (ℓ ⊔ ℓ') where
  []   :                                    AlgList e f    e
  _∷_  : (a : A) → ∀ {b} → AlgList e f b →  AlgList e f (  f a b)
\end{code}
But it is usually easier to program with more specialised datatypes such as |Vec|, which is a standard example of a datatype computed by algebraic ornamentation (over |List|), using the forgetful function derived from |ListO|, namely |length|.
From the algebraic ornament between |Vec| and |List|, in addition to a forgetful function |fromV| we can also derive its inverse |toV| and the inverse properties:
\begin{code}
fromV  : Vec A n → List A
toV    : (as : List A) → Vec A (length as)

from-toV  : (as : List  A)    → fromV (toV as) ≡ as
to-fromV  : (as : Vec   A n)  → (length (fromV as) , toV (fromV as)) (EQ(Σ ℕ (Vec A))) (n , as)
\end{code}
Note that, besides a new datatype |Vec|, we have derived an isomorphism between |List A| and |Σ ℕ (Vec A)| from the ornament |ListO|, allowing us to promote a natural number~|n| to a list if a vector of type |Vec A n| can be supplied (or the other way around).
In general, every ornament gives rise to such a `promotion isomorphism'~\citep{Ko-pcOrn}.
%We can repeat the construction for the ornament between |Vec| and |List|: the new datatype is the inductive predicate stating that a list has a particular length,
%\begin{code}
%data Len {A : Set ℓ} : ℕ → List A → Set ℓ where
%  zero  :                          Len    zero    []
%  suc   : ∀ {a n as} → Len n as →  Len (  suc n)  (a ∷ as)
%\end{code}
%and the isomorphism is between |Vec A n| and |Σ (List A) (Len n)|, allowing us to promote a list to a vector of type |Vec A n| if the list has length~|n|.
A more interesting and notable example is the conversion between extrinsically and intrinsically typed \textlambda-terms~\citep{Kokke-PLFA}:\pagebreak
\begin{code}
data Λ : Set where {-"\hspace{4em}"-}  data _⊢_ : List Ty → Ty → Set where
  var  : ℕ → Λ                         {-"\quad"-}  var  : vΓ ∋ τ → vΓ ⊢ τ
  app  : Λ → Λ → Λ                                  app  : vΓ ⊢ vσ ⇒ τ → vΓ ⊢ vσ → vΓ ⊢ τ
  lam  : Λ → Λ                                      lam  : vσ ∷ vΓ ⊢ τ → vΓ ⊢ vσ ⇒ τ

data Ty : Set where                    data _⊢_∶_ : List Ty → Λ → Ty → Set where
  base  : Ty                                        var  : (i : vΓ ∋ τ) → vΓ ⊢ var (toℕ i) ∶ τ
  _⇒_   : Ty → Ty → Ty                              app  : vΓ ⊢ t ∶ vσ ⇒ τ → vΓ ⊢ u ∶ vσ → vΓ ⊢ app t u ∶ τ
                                                    lam  : vσ ∷ vΓ ⊢ t ∶ τ → vΓ ⊢ lam t ∶ vσ ⇒ τ
\end{code}
(The list membership relation~`|_∋_|' will be defined in \cref{sec:simple-containers}.)
Write an ornament between the datatypes |Λ|~and~`|_⊢_|' of untyped and intrinsically typed \textlambda-terms, and we get the typing relation `|_⊢_∶_|' and an isomorphism between |vΓ ⊢ τ| and |Σ[ t ∶ Λ ] vΓ ⊢ t ∶ τ| for free, allowing us to promote an untyped term~|t| to an intrinsically typed one if a typing derivation for~|t| can be supplied.

We have deliberately omitted the types of the generic programs because they are somewhat verbose, making generic program invocation less cost-effective --- for example, the generic programs proving the inverse properties need connections for the original and the new datatypes, the fold used to compute the algebraic ornament, and the `from' and `to' functions.
In general, we should seek to reduce the cost of invoking generic programs.
We have implemented a smaller-scale solution where generic programs use Agda's instance arguments~\citep{Devriese-instance-arguments} to automatically look for the connections and other information they need, and the solution works well --- for example, |to-fromV| can be derived by supplying just the names |Vec| and |List|.
Larger-scale solutions such as instantiating the definitions in a parametrised module all at once may be required in practice.

Finally, we should briefly mention how |AlgD| handles universe polymorphism.
Given |F : FoldP|, the most important change from |F .Desc| to |AlgD F| is adding a suitably typed |σ|-field (for example, the field~|b| in |AlgList|) in front of every |ρ|-field; this is mirrored in the computation of  the |struct| field of |AlgD F| from that of |F .Desc|, primarily using the function
\begin{code}
algConB : Level → ConB → ConB
algConB ℓ []               = []
algConB ℓ (inl  ℓ'  ∷ cb)  = inl ℓ' ∷ algConB ℓ cb
algConB ℓ (inr  rb  ∷ cb)  = inl (max-ℓ rb ⊔ ℓ) ∷ inr rb ∷ algConB ℓ cb
\end{code}
(where |max-ℓ rb| is the maximum level in |rb|).
Subsequently we need to prove |level-ineq| for |AlgD F|, which requires non-trivial reasoning and involves properties about |algConB| such as |max-σ (algConB ℓ cb) ≡ max-π cb ⊔ max-σ cb ⊔ hasRec? ℓ cb|.
The reasoning is not difficult, but is probably one of the first examples that require non-trivial reasoning about universe levels.

\subsection{Predicates on Simple Containers}
\label{sec:simple-containers}

\begin{figure}
\codefigure
\begin{minipage}[t]{.4\textwidth}
\begin{code}
SC : DataD → Setω
SC D = ∀ {ℓs} → SCᵖ (D .applyL ℓs)

SCᵇ : ConB → Set
SCᵇ = ListAll (λ  {  (inl  _) → Bool
                  ;  (inr  _) → ⊤})
\end{code}
\end{minipage}%
\begin{minipage}[t]{.55\textwidth}
\begin{code}
record SCᵖ (D : PDataD) : Setω where field
  {elevel} : Level
  El   :  ⟦ D .Param ⟧ᵗ → Set elevel
  pos  :  ListAll SCᵇ (D .struct)
  coe  :  (ps : ⟦ D .Param ⟧ᵗ) → SCᶜˢ (D .applyP ps) pos (El ps)
\end{code}
\end{minipage}\\[.5\baselineskip]
\begin{minipage}[t]{.95\textwidth}
\begin{code}
SCᶜˢ  : {I : Set ℓⁱ} → ConDs I cbs → ListAll SCᵇ cbs → Set ℓ → Setω
SCᶜˢ  []           _             X = ⊤
SCᶜˢ  (D ∷ Ds)     (s ∷ ss)      X = SCᶜ D s E × SCᶜˢ Ds ss X

SCᶜ   : {I : Set ℓⁱ} → ConD I cb → SCᵇ cb → Set ℓ → Setω
SCᶜ   (ι i      )  _             X = ⊤
SCᶜ   (σ  A  D  )  (true   ∷ s)  X = ((_ , A) (EQ(Σ[ ℓ ∶ Level ] Set ℓ)) (_ , X)) × (  (a : A) →  SCᶜ (  D a)  s X)
SCᶜ   (σ  A  D  )  (false  ∷ s)  X =                                                   (a : A) →  SCᶜ (  D a)  s X
SCᶜ   (ρ  D  E  )  (_      ∷ s)  X =                                                              SCᶜ    E     s X
\end{code}
\end{minipage}
\caption{The simple-container predicate on datatype descriptions}
\label{fig:SC}
\end{figure}

There are not too many generic programs that work without assumptions on the datatypes they operate on; with dependent types, such assumptions can be formulated as predicates on datatype descriptions.
As a simple example, below we characterise a datatype~|N| as a `simple container' type by marking some fields of its description as elements of some type~|X|, and then derive predicates |All P| and |Any P| on~|N| lifted from a predicate~|P| on~|X|, stating that |P|~holds for all or one of the elements in an inhabitant of~|N|.
For example, the |ListAll| datatype (\cref{sec:connections}) is an instance of |All|.

The definition of simple containers (in several layers) is shown in \cref{fig:SC}.
%\footnote{\Cref{fig:SC} is in fact simplified:
%As mentioned in \cref{sec:level-parameters}, the type |Σ[ ℓ ∶ Level ] Set ℓ| cannot be built using the usual |Σ|-type former, and has to be defined separately; moreover, it resides in |Setω|, so the outer `|≡|' and `|×|' also have to be re-defined for |Setω|, as well as the |⊤|~type.
%The need for more powerful universe polymorphism shows clearly here.}
The top layer |SC| on |DataD| only quantifies over the level parameters, and the main definition is at the next layer |SCᵖ| on |PDataD|:
First is the element type~|El|, which can refer to the ordinary parameters.
Then in |pos| we assign a |Bool| to every |σ|-field indicating whether it is an element or not.
More precisely, the assignments are performed on the |struct| field of the description, and might not make sense since any |σ|-field could be marked with |true|, not just those of type~|El|.
However, the |coe| field of |SCᵖ| makes sure that the types of the fields marked with |true| are equal to~|El|; subsequently, when a generic program sees such a field, it can use the equality to coerce the type of the field to |El|.

The |All| predicate is simpler since it is just the datatype created along with a promotion isomorphism (\cref{sec:algebraic-ornamentation}).
For example, to derive |ListAll|, we mark the element field of |List| in an |SC ListD| structure, from which we can compute a more informative |ListWP| datatype that requires every element~|a| to be supplemented with a proof of |P a|:
\begin{code}
data ListWP {A : Set ℓ} (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  []       :                             ListWP P
  ⟨_,_⟩∷_  : (a : A) → P a → ListWP P →  ListWP P
\end{code}
Then the ornament between |ListWP| and |List| gives rise to |ListAll| and an isomorphism between |ListWP P| and |Σ (List A) (ListAll P)|, allowing us to convert between a list of pairs of an element and a proof (|ListWP P|) and a pair of a list of elements (|List A|) and a list of proofs (|ListAll P|).

The |Any| predicate is more interesting since its structure is rather different from that of the original datatype, although in the case of |List|, the |Any| structure happens to degenerate quite a bit:
\begin{code}
data ListAny {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  here   : ∀ {a as} → P a           → ListAny P (a ∷ as)
  there  : ∀ {a as} → ListAny P as  → ListAny P (a ∷ as)
\end{code}
The list membership relation |xs ∋ x| used in \cref{sec:algebraic-ornamentation}, defined by |ListAny (λ y → x ≡ y) xs|, is a special case.
In general, a proof of |Any P| is a path pointing to an element satisfying~|P|, and we can write a generic lookup function that follows a path to retrieve the element it points to (resembling \varcitet{Diehl-InfIR}{'s} construction) --- for |ListAny|, this lookup function specialises to
\begin{code}
lookupListAny : {A : Set ℓ} {P : A → Set ℓ'} {as : List A} → ListAny P as → Σ A P
lookupListAny (here   p  ) = _ , p
lookupListAny (there  i  ) = lookupListAny i
\end{code}
A path can be regarded as an (enriched) natural number that instructs the lookup function to stop (|here|/|zero|) or go further (|there|/|suc|) --- that is, there is an ornament between |Any| and~|ℕ|, allowing us to derive a forgetful function |toℕ| that computes the length of a path.
Moreover, a path should specify which element it points to if stopping, or which sub-tree to go into if going further, so the numbers of |here| and |there| constructors are exactly the numbers of element positions and recursive fields respectively.
For example, the |Any| predicate for the datatype of balanced 2-3 trees below (taken from \citet{McBride-pivotal}) would have three |here| constructors and five |there| constructors:%
%\footnote{Incidentally, this example shows that simple container types do not have to be parametric in their element types.}
\begin{code}
data B23T : Height → Value → Value → Set where  -- both |Height| and |Value| are~|ℕ|
  node₀  : ⦃ l ≤ r ⦄                                              → B23T    zero    l r
  node₂  : (x    : Value) → B23T h l x → B23T h x r               → B23T (  suc h)  l r
  node₃  : (x y  : Value) → B23T h l x → B23T h x y → B23T h y r  → B23T (  suc h)  l r
\end{code}
It is nice not having to write |B23TAny| and |lookupB23TAny| by hand.

%\begin{code}
%data AccAny {A : Set ℓ} {R : A → A → Set ℓ'} (P : A → Set ℓ'') :
%  (x : A) → Acc R x → Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
%  here   : ∀ {x as}                → P x                  → AccAny P x (acc as)
%  there  : ∀ {x as y} (r : R y x)  → AccAny P y (as y r)  → AccAny P x (acc as)
%\end{code}

%\section{Practical Issues}
%
%\subsection{Portability}
%\LT{Address the statement that our development is not specific to Agda.
%So, what features do we need to implement?
%(Elaborator reflection)}
%\LT{Axiom K is used for ornaments but this axiom is not generally desirable especially for homotopy type theory.
%This seemingly conflicting requirement in fact originates in the false belief that only one identity type is allowed in a type theory.
%Indeed, it is possible to have more than one identity type with different strength.
%For example, the two-level type theory proposed by \citet{Capriotti2017} consists of a strict equality (satisfying the axiom K) and a weak equality compatible with the homotopy-theoretic interpretation.
%Agda has an experimental option \texttt{--two-level} in the cubical mode which introduces additional universes \texttt{SSet}.
%This extra sort of universes will make our library portable to proof assistants based on homotopy type theory.
%(A bit of experiments should be performed to testify.)
%
%\subsection{Naming, Visibility, and Order of Arguments}
%
%\begin{figure}
%\codefigure
%\begin{minipage}[t]{.45\textwidth}\setlength{\mathindent}{0em}
%\begin{code}
%mutual
%  data (HL (Sort : Set)) where
%    set      : (t : Term)  →  Sort
%    lit      : (n : ℕ)     →  Sort
%    prop     : (t : Term)  →  Sort
%    propLit  : (n : ℕ)     →  Sort
%    inf      : (n : ℕ)     →  Sort
%    unknown  :                Sort
%
%  data (HL (Abs (A : Set)  : Set)) where
%    abs : (s : String)   (x : A) → Abs A
%
%  data (HL (Arg (A : Set)  : Set)) where
%    arg : (i : ArgInfo)  (x : A) → Arg A
%
%  data (HL (ArgInfo     : Set)) where
%    arg-info : (v : Visibility) (m : Modality) → ArgInfo
%  ...
%\end{code}
%\end{minipage}%
%\begin{minipage}[t]{.55\textwidth}\setlength{\mathindent}{0em}
%\begin{code}
%{-" "-}
%data Term : Set where
%  (HL agda-sort)  : (s : Sort)                                      → Term
%  pi              : (a : (HL Arg) Type) (b : (HL Abs) Type  )       → Term
%  lit             : (l : Literal)                                   → Term
%  lam             : ((HL(v : Visibility)))   (t : (HL Abs) Term)    → Term
%  (HL pat-lam)    : (cls : Clauses)          (xs : Args Term)       → Term
%  var             : (i : ℕ)                  (xs : (HL Args) Term)  → Term
%  con             : (c : Name)               (xs : (HL Args) Term)  → Term
%  def             : (f : Name)               (xs : (HL Args) Term)  → Term
%  meta            : (x : Meta)               (xs : (HL Args) Term)  → Term
%  unknown         : Term
%\end{code}
%\end{minipage}
%
%\begin{minipage}[t]{.6\textwidth}\setlength{\mathindent}{0em}
%\begin{code}
%\end{code}
%\end{minipage}%
%
%\caption{A snippet of reflected expressions (actual)}
%\label{fig:full reflected syntax}
%\end{figure}
%
%\begin{code}
%Args : Set ℓ → Set ℓ
%Args A = List (Arg A)
%\end{code}
%
%\begin{code}
%Telescope = List (String × Type)
%\end{code}
%
%\todo[inline]{Chosen by generic programs, dependency analysis, refactoring tools, heuristics, machine learning; interaction with generalised variables; the wrapper trick retains all these possibilities}
%
%\subsection{Normalisation and Printing}
%
%\todo[inline]{`type preservation', optimisation, name scope and qualification}
%
%\subsection{Interactive User Interface}
%
%\subsection{Automatic Resolution of Arguments to Generic Programs}
%
%\todo[inline]{Type classes, instance arguments}

\section{Discussion}
\label{sec:discussion}

\paragraph{Interoperability between generic and native entities}

Our framework makes generic constructions parametrised by our version of datatype descriptions interoperable with native datatypes and functions.
Generic libraries using their own descriptions could achieve the same by duplicating our framework, but there are alternatives:
In Haskell, \citet{Magalhaes-GGP} provide automatic conversions between the datatype representations of several libraries ---targeting different families of datatypes--- and a representative representation, through which native datatypes are connected to all the libraries at once; our descriptions (possibly with extensions to support mutual recursion, induction-recursion, etc) can serve as a representative representation.
Moreover, in a dependently typed setting it is possible to attain better uniformity and reusability by defining families of datatypes as predicates on a single representation like in \cref{sec:simple-containers}, in contrast to a simply typed setting where different families of datatypes need to be modelled by separate representations.

%\todo[inline]{Missing the feature that converts fold functions to algebras, although there seems to be some overlap between this feature and the functionalities of the termination checker; update the reflection API?}

\paragraph{Optimisation of datatype-generic programs}

%\Josh{The Haskell programmer produces recursive function definitions~\citep{de-Vries-true-SoP}.
%We adopt the approach where generic function representations are non-recursive and then weaved into recursive definitions.}

%\Viktor{\citet{Pickering-staged-SoP, Yallop-staged-generic-programming, Jones-partial-evaluation, de-Vries-masters-thesis, Alimarine2004}; partial evaluation is more programmer-friendly than staging, and elaborator reflection provides, to some extent, the ability to do partial evaluation.
%Staging may be better for controlling what appears in the final code, but there's no implementation for dependently typed languages.
%Efficiency problem due to conversion between generic and native representations (see below) since the Haskell era~\citep{Magalhaes-optimising-generics}.}

A traditional way to instantiate a generic program is to compose the program with conversions between a native datatype and its generic description.
If the generic program was defined on datatypes decoded by the |μ|~operator and then instantiated by the recursive conversion between the native and |μ|-decoded datatypes, the conversion overhead would be roughly the same as that of unoptimised Haskell generic programs, and had to be eliminated.
%We have not found much work on optimising such programs.
Rather than optimising the composition of several recursive functions, the Haskell community has employed a shallow encoding and studied relevant optimisation/specialisation (see, for example, \citet[Section~5.1]{de-Vries-true-SoP}); this encoding is the basis of our design.
Below we discuss previous attempts at optimising instantiated programs using the shallow encoding.

Recent work using staging~\citep{Yallop-staged-generic-programming, Pickering-staged-SoP} eliminates performance overheads by generating native function definitions that are almost identical to hand-written ones.
There is, however, no implementation of staging in existing dependently typed languages, so we cannot compare them properly on the same ground.
But it shares a similar purpose with our framework of generating function definitions containing neither generic representations nor conversions, making them comparable regardless of the specific languages they work in.

We compare staging with our framework from the view of partial evaluation~\citep{Jones-partial-evaluation}.
A partial evaluator takes a general program and known parts of its input, and generates a program that takes the remaining input; the resulting program is extensionally equal to ---and usually more optimised than--- the general program partially applied to the known input.
Our macro |defineFold|~(\cref{sec:specialising}) is a partial evaluator which specialises a generic program (general program) to a given datatype description (known input).
Indeed, it has been observed that we can perform partial evaluation in functional languages by normalisation~\citep{Filinski1999}, which |defineFold| does.

% seperation of concerns + reasoning of metaprogram (generic struture not apearing in residual program), ref principles in staged-sop
Similar to a partial evaluator, a staged generic program is a more specialised program-generator --- the generic/general program to be specialised has been fixed.
%It essentially acts as an intermediate between a partial evaluator and a specialised program. 
%So not only do we share the same purpose, we share similar means to achieve it as well.
However, staging requires manually inserting staging annotations; this puts burdens on the programmer and mixes a part of the instantiation process with generic definitions.
%Moreover, \citet[Section~4.2]{Pickering-staged-SoP} need to perform certain manipulations on generic programs, are undesireable since they alter the definitions of generic programs.
Our approach separates how we instantiate generic programs (by metaprograms) from how we define them (as algebras).
As a result, our generic programs are annotation-free, making them easier to write and read.
%The separation of the instantiation process as metaprograms also provides a basis for future work on the reasoning of its correctness.
On the other hand, staging has its own benefit: \citet[Section~4.1]{Pickering-staged-SoP} provide principles followed by the programmer to avoid generic representations from appearing in specialised programs; without staging annotations, it seems difficult to formulate similar principles in our setting.
But we can explore alternative approaches --- for example, \citet{Alimarine2004} give theorems guaranteeing that generic representations can be removed from instantiated programs with suitable types by normalisation.
%Similar guidelines may be stated for metaprograms, and their correctness can be stated and proved if we have better tools for reasoning about them. \todo{cref next paragraph?}
%\todo{say something good about staging?}
 
There have also been attempts using compiler optimisation~\citep{de-Vries-masters-thesis, Magalhaes-inlining}, which are less relevant to our work as explained in \cref{sec:introduction}.
However, as generic programs become more complex, we may need more advanced code generation techniques that can be borrowed from compiler optimisation, possibly through extensions to elaborator reflection.
%However, their techniques can still be of use to us if elaborator reflection is better designed.
%For example, elaborator reflection may provide an interface for adding normalisation rules in certain contexts, such that programmers can optimise instantiation of generic programs~\citep{de-Vries-masters-thesis} without modifying the global language behaviour.

\paragraph{Analysis of higher-order encodings}
The local variable creation technique has been used extensively to analyse higher-order encodings, but it has to be used with caution.  
Agda's elaborator checks if a local variable escapes its context in the result of |extendContext| during the runtime of elaboration.\footnote{%
In previous versions of Agda, the existing de Bruijn indices in an extended context were not weakened~\citep{AgdaIssue3831} and the check was not implemented in full until the recent version 2.6.2 of Agda~\citep{AgdaIssue4898}.}
This is similar to the |nu| constructor of the typed tactic language Mtac~\citep{Ziliani2015}, which checks the escape of local variables during tactic execution.
Indeed, \citet{Chen-Mtac-Agda} implemented Mtac's |nu| constructor by elaborator reflection in the same way.
On the contrary, the $\nu$-operator for \emph{local name creation} in a modal calculus \citep{Nanevski2005} and a two-level functional language \citep{Schurmann2005} statically ensures that local names cannot escape their scope. 

Our higher-order encodings are not actually higher-order abstract syntax~\citep{Harper1993}, since exotic terms such as |Bool ∷ λ { false → [ A ∶ Set ] [] ; true → [ P ∶ (ℕ → Set) ] [] }| are not excluded by the typing discipline.
As argued by \citet{McBride-ornaments}, exotic terms, which we do not use, could be exploited for richer expressiveness, but then it is harder to analyse and deviates too much from Agda's current datatype declarations, which our framework targets.

\paragraph{Dependently typed datatype-generic libraries}
Our framework makes it possible and worthwhile to develop datatype-generic libraries for wider and practical use in Agda.
The change to traditional Agda generic programs required by our framework is a mild generalisation from the operators |μ|~and |fold| to datatype and fold connections capturing the behaviour of the operators, so it is easy to adapt existing libraries to our framework as well as develop new ones.
There are still many opportunities to explore for dependently typed datatype-generic libraries:
Even for recursion schemes~\citep{Yang-recursion-schemes}, a standard datatype-generic example, we can start supplying theorems about them like in \cref{sec:fold-operators}.
Datatypes derived from others, such as the lifted predicates |All| and |Any| in \cref{sec:simple-containers}, are also common and should be treated generically (as opposed to manually duplicating an instance for each datatype as in the standard library~\citep{Agda-stdlib}).
Domain-specific organisation of datatypes with intrinsic invariants is another important goal, for which ornaments~\citep{McBride-ornaments} still have much potential (although the community has focussed mostly on lifting ornaments to programs and proofs~\citep{Dagand-functional-ornaments,McDonell-Ghostbuster,Williams-principle-ornamentation,Ringer-ornaments-Coq}).
For example, \cref{sec:algebraic-ornamentation} mentions that the relationship between intrinsically and extrinsically typed \textlambda-terms can be captured as an ornament, whose properties and derived constructions should be formulated generically for reuse in developments of typed embedded languages --- a direction already proved fruitful by \citet{Allais-binding-syntax-universe-JFP}.

%\todo[inline]{Success of the App Store: dependent types need richer type structures and allow assumptions about datatype descriptions to derive more functionalities (boring if we can only automate Eq, Show, Read etc), so DGP has much more potential in dependently typed settings; also, keep generic programs natural so that libraries can be developed more easily — no staging (which is not in the current dependently typed languages anyway)!}

%\Josh{Our work enables the practical development and applications of datatype-generic libraries.
%Duplicated code in Standard Library.
%Ornaments have been used to lift functions, but its original purpose ---organisation of datatypes--- should not be forgotten (\citet{McBride-ornaments}; porting some constructions from \citet{Ko-OAOAOO}; more experimental developments~\citep{Ko-OrnJFP, Dagand-functional-ornaments}; theory and developments about function transportation in simply typed settings~\cite{Williams-principle-ornamentation, Williams-ornaments-in-practice}; realistic dependently typed application and automated synthesis of ornaments~\citep{McDonell-Ghostbuster,Ringer-ornaments-Coq}).
%Make \citet{McBride-pivotal, Allais-binding-syntax-universe-JFP} native.}

\paragraph{Code generation versus first-class datatypes}

Similar to staged approaches~\citep{Yallop-staged-generic-programming,Pickering-staged-SoP}, our framework instantiates generic programs by generating code separately for each native instance.
A potential problem is code duplication, on which we take a conservative position: while we cannot solve the problem, which is inherent in languages with datatype declarations, we do alleviate it a little by removing the overhead of manual instantiation and maintaining explicit connections between generic and instantiated entities, which generic libraries can exploit.
A possible solution to the problem was proposed by \citet{Chapman-levitation} in the form of a more radically redesigned type theory where datatype declarations are replaced with first-class descriptions, and the |μ|~operator becomes the exclusive built-in mechanism for manufacturing datatypes.
Generic programs in this theory are directly computable and do not require instantiation.
However, there have been no subsequent developments of the theory, in particular a practical implementation.
While waiting for better languages to emerge, it is also important to enable the development and practical use of datatype-generic libraries as soon as possible, which our framework does.

%\Josh{The language supports a single generic representation akin to the generic |μ| and |fold| operators, which avoid code duplication/explosion but (potentially?) sacrificing efficiency~\citep{Allais-n-ary-functions}.
%No development since levitation, in particular no implementation.
%Our work provides a foundation for the development of generic libraries \emph{now}.
%Feel free to port the libraries to a new foundation when it's ready.}

%\todo[inline]{\citet{Chapman-levitation} propose a more radical redesign of type theory where datatype definitions are first-class, but the theory is still at an early stage of development and lacks an implementation; our proposal is more practical and serves as a platform for the development of mature datatype-generic libraries, which can be ported to new platforms when ready}

\paragraph{Foundations}
While the use of universe polymorphic-datatypes is convenient in practice, its theory is, surprisingly, an unexplored territory, and the notion of universe polymorphism is less studied than it should be.
To the best of our efforts, we did not find any type theory backing Agda's current design of first-class universe levels and universe polymorphism.
Even worse, without universe cumulativity, subject reduction does not hold for expressions in |Setω|~\citep{AgdaIssue5810}.
\citet{Kovacs-universe-hierarchies} initiated a theoretical framework for first-class universe levels which is able to model features like bounded universe polymorphism, but its metatheory is bare-bones and lacks, for example, an elaboration algorithm needed for implementation.  
A type theory of first-class datatypes \citep{Chapman-levitation} requires internal universe-polymorphic encodings, but most of internal encodings \citep{Dybjer-indexed-induction-recursion,nordvallforsberg2013thesis,Kaposi2020a} do not encode universe polymorphism.

Due to the nature of uni-typed encodings, our experience with Agda's elaborator reflection was painful, especially in contrast to datatype-generic programming.
Elaborator reflection is a useful paradigm but it has not been specified in theory, and to use it the understanding of the inner workings of elaborator is much needed.
More importantly, the correctness of a macro can only be verified externally at best, but it is internally guaranteed by typed metaprogramming like staging.
\citet{Christiansen-elaborator-reflection} argued that programs in the reflected elaborator are shorter and simpler than typed metaprograms, but they also admitted the additional cost is for the mandatory correctness.
Hopefully, the best of two worlds could be combined. 
Say, suppose that we have a type |TTerm A| of |A|-typed reflected expressions.
Normalisation (by evaluation) always works on well-typed expressions, so the type of |normalise| could be |TTerm A → TTerm A|;
type checking transforms a possibly ill-formed expression to a typed expression if successful, so the type of |checkType| could be |Term → (A : Set ℓ) → TC (TTerm A)|.
Typed reflected expressions also benefit efficiency, since they need not be elaborated again.

We hope that our framework can serve as inspiration and a call for a foundation for universes and metaprogramming not only for theoretical interests but also for practical needs.

%\paragraph{Conclusion}
%
%\todo[inline]{From the angle of datatype-generic programming, the generic constructions should work on native datatypes and functions for maximum interoperability with language facilities and other libraries, and the gap between generic and native entities can be filled straightforwardly with (powerful enough) metaprogramming.
%From the angle of metaprogramming, one way to offer better correctness guarantees about the meta-level constructions is to introduce types, and (dependently typed) datatype-generic programming already provides a working solution for typing a good range of the constructions.
%Each of the two programming disciplines works nicely as the other's natural extension.}
%
%\todo[inline]{Suggestions for the future evolution of Agda or the design of new languages with elaborator reflection}
%
%\todo[inline]{Provide a practically relevant application whose foundation the theorists can investigate and formalise}

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
