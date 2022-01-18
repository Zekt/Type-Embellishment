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

\usepackage[color=yellow,textsize=footnotesize]{todonotes}

\newcommand{\arXiv}[1]{\href{http://arxiv.org/abs/#1}{arXiv:\nolinkurl{#1}}}

\let\Bbbk\relax
%include agda.fmt

\newcommand{\identifier}{\mathit}

%format Set = "\Keyword{Set}"
%format X = "\identifier{X}"
%format z = "\identifier{z}"
%format s = "\identifier{s}"
%format n = "\identifier{n}"


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
\author{Tzu-Chi Lin}
\orcid{0000-0000-0000-0000}
\email{vik@@iis.sinica.edu.tw}
\author{Liang-Ting Chen}
\email{liang.ting.chen.tw@@gmail.com}
\orcid{0000-0002-3250-1331}
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
  Datatype generic programming is typed metaprogramming over datatypes.
\end{abstract}

\begin{CCSXML}
<ccs2012>
   <concept>
       <concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
       <concept_desc>Software and its engineering~Functional languages</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
   <concept>
       <concept_id>10003752.10003790.10011740</concept_id>
       <concept_desc>Theory of computation~Type theory</concept_desc>
       <concept_significance>100</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011024.10011028</concept_id>
       <concept_desc>Software and its engineering~Data types and structures</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
 </ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Functional languages}
\ccsdesc[300]{Theory of computation~Type theory}
\ccsdesc[300]{Software and its engineering~Data types and structures}

\keywords{typed metaprogramming, datatype-generic programming, inductive families, ornaments}
\maketitle

\section{Introduction}

\citet{Gibbons-DGP, Altenkirch-GP-within-DTP, Pickering-staged-SoP, Yallop-staged-generic-programming, de-Vries-masters-thesis, Jones-partial-evaluation, Chapman-type-theory-should-eat-itself, Christiansen-elaborator-reflection, Kovacs-universe-hierarchies, Allais-binding-syntax-universe-JFP, McBride-ornaments, Ko-OAOAOO, Chen-Mtac-Agda}

\begin{itemize}
\item Encoding of universe-polymorphic and parametrised inductive families (precise calculation of universe levels)
\item Interoperability with native datatypes and functions (generating new native datatypes and functions, and connecting with existing ones for which generic constructions can be specialised)
\item A new use case of elaborator reflection where traditional datatype-generic programs are simply normalised to yield native programs (and do not need more radical adaptations like staging)
\item Simpler and less error-prone `object-level' binder-manipulating techniques with (Agda's) elaborator reflection (bypassing the manipulation of de Bruijn indices; a tutorial for Agda's reflection mechanism)
\end{itemize}

\section{A First Taste of Datatype-Generic Programming}

\todo[inline]{Sums-of-products datatypes and inductive functions (as predicate algebras); `exotic' fixed points (and their problems); parametrisation}

\citet{de-Vries-true-SoP}

\section{Datatype-Generic Programming with Inductive Families}

\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat
  
foldNat : {X : Set} -> X -> (X -> X) -> Nat -> X
foldNat z s    zero    = z
foldNat z s (  suc n)  = s (foldNat z s n)
\end{code}

\section{Native Fixed Points}

\todo[inline]{Introduction to reflection in Agda; manufacturing native datatypes and inductive functions from datatype-generic definitions}

\section{Universe Polymorphism}

\section{Examples}

\todo[inline]{Derived datatypes and functions; ornamentation; specialised universes}

\section{Discussion}

%%
%% The acknowledgments section is defined using the "acks" environment
%% (and NOT an unnumbered section). This ensures the proper
%% identification of the section in the article metadata, and the
%% consistent spelling of the heading.
\begin{acks}
The work is supported by \grantsponsor{MOST}{Ministry of Science and Technology of Taiwan}{https://www.most.gov.tw/} under grant \grantnum{MOST}{MOST 109-2222-E-001-002-MY3}.
\end{acks}

%%
%% The next two lines define the bibliography style to be used, and
%% the bibliography file.
\bibliographystyle{ACM-Reference-Format}
\bibliography{/Users/joshko/Documents/bib}

%%
%% If your work has an appendix, this is the place to put it.
%\appendix
%
%\section{Research Methods}

\end{document}
