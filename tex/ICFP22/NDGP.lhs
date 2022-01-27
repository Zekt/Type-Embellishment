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

\usepackage{bbold}
\usepackage[euler]{textgreek}

\usepackage[color=yellow,textsize=footnotesize]{todonotes}

\newenvironment{halfcol}{\begin{minipage}{.45\textwidth}\setlength{\mathindent}{0em}}{\end{minipage}}

\newcommand{\arXiv}[1]{\href{http://arxiv.org/abs/#1}{arXiv:\nolinkurl{#1}}}

\let\Bbbk\relax
%include agda.fmt

\setlength{\mathindent}{\parindent}
%\renewcommand{\Varid}{\texttt}
%\renewcommand{\Conid}{\texttt}
\newcommand{\iden}{\mathit}

%format pattern = "\Keyword{pattern}"

%format → = "\mathop{\to}"
%format 𝟘 = "\mathbb{0}"
%format 𝟙 = "\mathbb{1}"
%format 𝕣 = "\mathbb{r}"
%format × = "\mathop{\times}"
%format ⊎ = "\mathop{\uplus}"
%format ≡ = "\mathop{\equiv}"
%format ∘ = "\mathop{\circ}"
%format ⊔ = "\mathop{\sqcup}"

%format ᵖ = "_{\Conid P}"
%format ⟦_⟧ᵖ = ⟦_⟧ ᵖ
%format ⟧ᵖ = ⟧ ᵖ
%format Algᵖ = Alg ᵖ
%format depthᵖ = depth ᵖ
%format fmapᵖ = fmap ᵖ
%format Allᵖ = All ᵖ
%format ind-fmapᵖ = ind-fmap ᵖ
%format Dᵖ = D "\kern.5pt" ᵖ

%format ˢ = "_{\Conid S}"
%format ⟦_⟧ˢ = ⟦_⟧ ˢ
%format ⟧ˢ = ⟧ ˢ
%format Algˢ = Alg ˢ
%format depthˢ = depth ˢ
%format fmapˢ = fmap ˢ
%format IndAlgˢ = IndAlg ˢ
%format Allˢ = All ˢ
%format ind-fmapˢ = ind-fmap ˢ

%format ᵗ = "_{\Conid T}"
%format ⟦_⟧ᵗ = ⟦_⟧ ᵗ
%format ⟧ᵗ = ⟧ ᵗ
%format Curriedᵗ = Curried ᵗ
%format uncurryᵗ = uncurry ᵗ

%format ʳ = "_{\Conid R}"
%format ⟦_⟧ʳ = ⟦_⟧ ʳ
%format ⟧ʳ = ⟧ ʳ

%format ᶜ = "_{\Conid C}"
%format Algᶜ = Alg ᶜ
%format FoldOpTᶜ = FoldOpT ᶜ
%format fold-opᶜ = fold-op ᶜ

%format ᶜˢ = "_{\Conid{Cs}}"
%format Algᶜˢ = Alg ᶜˢ
%format FoldOpTelᶜˢ = FoldOpTel ᶜˢ
%format fold-opᶜˢ = fold-op ᶜˢ
%format FoldOpTelᶜˢ = FoldOpTel ᶜˢ

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
%format args = "\iden{args}"
%format cb = "\iden{cb}"
%format cbs = "\iden{cbs}"
%format d = "\iden d"
%format ds = "\iden{ds}"
%format f = "\iden f"
%format fs = "\iden{fs}"
%format i = "\iden i"
%format ℓs = "\iden{" ℓ "\kern-1pt s}"
%format n = "\iden n"
%format ns = "\iden{ns}"
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

\citet{de-Vries-true-SoP}

\begin{halfcol}\begin{code}
data ProdD : Set₁ where
  𝟙    : ProdD
  𝕣    : ProdD → ProdD
  _⊗_  : Set → ProdD → ProdD
\end{code}\end{halfcol}%
%
\begin{halfcol}\begin{code}
⟦_⟧ᵖ : ProdD → Set → Set
⟦ 𝟙       ⟧ᵖ X = ⊤
⟦ 𝕣    D  ⟧ᵖ X = X  × ⟦ D ⟧ᵖ X
⟦ A ⊗  D  ⟧ᵖ X = A  × ⟦ D ⟧ᵖ X
\end{code}\end{halfcol}

\begin{halfcol}\begin{code}
data SumD : Set₁ where
  𝟘    : SumD
  _⊕_  : ProdD → SumD → SumD
\end{code}\end{halfcol}%
%
\begin{halfcol}\begin{code}
⟦_⟧ˢ : SumD → Set → Set
⟦ 𝟘       ⟧ˢ X = ⊥
⟦ D ⊕ Ds  ⟧ˢ X = ⟦ D ⟧ᵖ X ⊎ ⟦ Ds ⟧ˢ X
\end{code}\end{halfcol}

\begin{code}
data μ (D : SumD) : Set where
  con : ⟦ D ⟧ˢ (μ D) → μ D
\end{code}

\begin{code}
ListNatSP : SumD
ListNatSP = 𝟙 ⊕ (Nat ⊗ 𝕣 𝟙) ⊕ 𝟘
\end{code}

\begin{code}
pattern []        = con (inl                 tt    )
pattern _∷_ n ns  = con (inr (inl (n , ns ,  tt))  )
\end{code}

\begin{code}
decon : μ D → ⟦ D ⟧ˢ (μ D)
decon (con ds) = ds

con-decon : (d : μ D) → con (decon d) ≡ d
con-decon (con _) = refl
\end{code}

\begin{code}
Algˢ : SumD → Set → Set
Algˢ D X = ⟦ D ⟧ˢ X → X
\end{code}

\begin{code}
Algᵖ : ProdD → Set → Set
Algᵖ D X = ⟦ D ⟧ᵖ X → X
\end{code}

\todo[inline]{a typical layer-by-layer definition}

\begin{code}
depthᵖ : (D : ProdD) → Algᵖ D Nat
depthᵖ    𝟙        _          = 0
depthᵖ (  𝕣    D)  (n  , ns)  = suc n ⊔  depthᵖ D ns
depthᵖ (  A ⊗  D)  (_  , ns)  =          depthᵖ D ns

depthˢ : (D : SumD) → Algˢ D Nat
depthˢ (D ⊕ Ds) (inl  ns) = depthᵖ  D   ns
depthˢ (D ⊕ Ds) (inr  ns) = depthˢ  Ds  ns
\end{code}

\begin{code}
fmapᵖ : (D : ProdD) → (X → Y) → ⟦ D ⟧ᵖ X → ⟦ D ⟧ᵖ Y
fmapᵖ    𝟙        f _          = tt
fmapᵖ (  𝕣    D)  f (x  , xs)  = f x  , fmapᵖ D f xs
fmapᵖ (  A ⊗  D)  f (a  , xs)  = a    , fmapᵖ D f xs

fmapˢ : (D : SumD) → (X → Y) → ⟦ D ⟧ˢ X → ⟦ D ⟧ˢ Y
fmapˢ (D ⊕ Ds) f (inl  xs) = inl  (fmapᵖ  D   f xs)
fmapˢ (D ⊕ Ds) f (inr  xs) = inr  (fmapˢ  Ds  f xs)
\end{code}

\begin{code}
{-# TERMINATING #-}
fold : (D : SumD) → Algˢ D X → μ D → X
fold D f = f ∘ fmapˢ D (fold D f) ∘ decon
\end{code}

\begin{code}
IndAlgˢ : (D : SumD) → Alg D X → (X → Set) → Set
IndAlgˢ {X} D f P = (xs : ⟦ D ⟧ˢ X) → Allˢ D P xs → P (f xs)
\end{code}

\begin{code}
Allᵖ : (D : ProdD) → (X → Set) → ⟦ D ⟧ᵖ X → Set
Allᵖ    𝟙        P _          = ⊤
Allᵖ (  𝕣    D)  P (x  , xs)  = P x ×  Allᵖ D P xs
Allᵖ (  A ⊗  D)  P (a  , xs)  =        Allᵖ D P xs

Allˢ : (D : SumD) → (X → Set) → ⟦ D ⟧ˢ X → Set
Allˢ (D ⊕ Ds) P (inl  xs) = Allᵖ  D   P xs
Allˢ (D ⊕ Ds) P (inr  xs) = Allˢ  Ds  P xs
\end{code}

\begin{code}
ind-fmapᵖ : (D : ProdD) → ((x : X) → P x) → (xs : ⟦ D ⟧ᵖ X) → Allᵖ D P xs
ind-fmapᵖ    𝟙        f _          = tt
ind-fmapᵖ (  𝕣    D)  f (x  , xs)  = f x ,  ind-fmapᵖ D f xs
ind-fmapᵖ (  A ⊗  D)  f (a  , xs)  =        ind-fmapᵖ D f xs

ind-fmapˢ : (D : SumD) → ((x : X) → P x) → (xs : ⟦ D ⟧ˢ X) → Allˢ D P xs
ind-fmapˢ (D ⊕ Ds) f (inl  xs) = ind-fmapᵖ   D   f xs
ind-fmapˢ (D ⊕ Ds) f (inr  xs) = ind-fmapˢ   Ds  f xs
\end{code}

\begin{code}
{-# TERMINATING #-}
ind : (D : SumD) → (P : μ D → Set) → IndAlgˢ D con P → (d : μ D) → P d
ind D P f = subst P (con-decon _) ∘ f _ ∘ ind-fmapˢ D (ind D P f) ∘ decon
\end{code}

\section{Inductive Families}

\section{Datatype Parameters and Universe Polymorphism}

\section{Connecting Generic and Native Entities}

\section{Establishing Connections via Metaprogramming}

\todo[inline]{Introduction to reflection in Agda}

\section{Examples}

\subsection{Fold and Induction Operators}

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
For example, the two-level type theory proposed by Capriotti consists of a strict equality (satisfying the axiom K) and a weak equality compatible with the homotopy-theoretic interpretation.
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

\todo[inline]{Type class, instance arguemtnts}
\section{Discussion}

\citet{Gibbons-DGP, Altenkirch-GP-within-DTP, Pickering-staged-SoP, Yallop-staged-generic-programming, de-Vries-masters-thesis, Jones-partial-evaluation, Chapman-type-theory-should-eat-itself, Christiansen-elaborator-reflection, Kovacs-universe-hierarchies, Allais-binding-syntax-universe-JFP, McBride-ornaments, Ko-OAOAOO, Chen-Mtac-Agda, Allais-n-ary-functions}

\todo[inline]{Partial evaluation is more programmer-friendly than staging, and elaborator reflection provides, to some extent, the ability to do partial evaluation}

\todo[inline]{From the angle of datatype-generic programming, the generic constructions should work on native datatypes and functions for maximum interoperability with language facilities and other libraries, and the gap between generic and native entities can be filled straightforwardly with (powerful enough) metaprogramming.
From the angle of metaprogramming, one way to offer better correctness guarantees about the meta-level constructions is to introduce types, and (dependently typed) datatype-generic programming already provides a working solution for typing a good range of the constructions.
Each of the two programming disciplines works nicely as the other's natural extension.}

\todo[inline]{The native world as the common playground of multiple generic libraries}

\todo[inline]{Suggestions for the future evolution of Agda or the design of new languages with elaborator reflection}

\todo[inline]{Our experience with untyped metaprogramming was painful, especially in contrast to the experience with datatype-generic programming (a form of typed metaprogramming, as we argued above)}

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
