Dear Shepherd and Reviewers,

We have revised our paper to address the issues raised in the reviews.
In particular, for the two mandatory requirements we have made the following revisions:

[Accessibility/Big Picture]

> 1. All reviewers agree that the paper is, as currently written, not very accessible, or at least only to a very narrow audience. Please restructure to focus more on the ideas and the big picture and try not to get lost in the technical details.

Regarding paper structure, the biggest distraction was the treatment of universe polymorphism, which is now extracted and simplified as Section 5 and comes after our main contribution (the metaprograms for generic program instantiation) in Section 4.
Before Section 4, Section 2 still recaps standard datatype-generic programming, and Section 3 introduces only the necessary components of our framework (parametrised datatypes/fold definitions and datatype/fold connections) and is much simpler than Sections 3 & 4 in the previous version, so now we get to Section 4 more quickly without having to go through complex technical content first.
Section 4 itself is also streamlined and simplified since we don’t handle universe polymorphism there anymore.
And the opening of each of the Sections 2–5 has been rewritten or reorganised to present a better big picture.

[Novelties/Contributions]

> 2. We think you could be much clearer in highlighting what exactly the technical novelties and contributions of the paper are, as opposed to the parts where you are applying known techniques.

Both the paragraph on elaborator reflection in Section 1 (L95–113) and the opening of Section 5 have been rewritten to emphasise the advantages of using elaborator reflection to perform our tasks compared to traditional metaprogramming.
The contribution paragraphs in Section 1 (L114–133) have also been rewritten to say (i) that the central components of our framework are the metaprograms and describe the benefit of the design, (ii) that our design can be ported to other languages as soon as the necessary metaprogramming primitives are ported there (so while currently the framework is implemented only in Agda, the design should be of interest to the broader ICFP community), and (iii) that our universe-polymorphic datatype descriptions are made possible because of Agda’s first-class levels, so our work provides a practical justification for Agda’s design for universe polymorphism (that is, first-class levels are actually useful rather than just a nuisance, and deserve to be discussed in the paper).

Point-by-point responses to the reviews are attached below.
We intend to go over the paper a couple more times to do some more polishing (we didn’t get as much time as we liked for this revision), but we don’t expect the overall appearance to change much (and probably can’t change much since we’ve reached the page limit).
If there are specific parts you think can be improved, please let us know.
Thanks!

– Josh, Liang-Ting, and Tzu-Chi


> Review #20A
> ===========================================================================

> Comments for author
> -------------------

> The presentation is mostly good. I appreciate that the authors are trying to motivate the design in small steps, and provide examples. Nevertheless, there are a lot of mechanics that complicate things, in particular the treatment of level polymorphism. And the authors are not even showing the most complicated form of the development (for inductive proofs), but limit themselves to the presentations of folds and algebras, which are supposedly a little bit simpler. It occasionally feels like the paper gets perhaps lost a bit in the technical details and loses sight of the big picture.

See [Accessibility/Big Picture].

> It is also a bit unfortunate that the paper uses a lot of forward references, making it sometimes difficult to fully appreciate a part of it until much later.

The worst one was probably the telescope-appending constructor, whose purpose wasn’t explained when the constructor was introduced.
We have added some explanation at L368–371 before referring the reader to Section 6.1 for the example.
We’ll look for more forward references, and it would be great if you could let us know those you still remember.

> In my opinion, the real meat of the paper is Section 5, and that only starts in the second half of the paper. In addition, it feels as if far more details are given about the chosen generic representation than are presented about the intricacies of elaborator reflection in Section 5, which makes me wonder if it would not perhaps have been possible to find a simpler scenario in which to demonstrate the core ideas, i.e., a more limited universe without as many features, then describe the elaborator reflection idea in that context, and spend a section later in the paper to talk about the generalisations needed to scale up to the real deal.

See [Accessibility/Big Picture].

> One concern (also reflected below in the Questions for the authors) is that little is being said in this section about the reliability of the approach. Using elaborator reflection feels at least somewhat reminiscent of using Template Haskell in Haskell to derive datatypes and class instances automatically: the resulting code is checked, but the algorithm itself can fail. The point in favour here seems to be that the users of this approach do not have to employ elaborator reflection themselves, so there is a limited "trusted" code base. Nevertheless, how do we now that the elaborator macros work, and under what conditions they work, and what kind of errors would be observe if there was a mistake?

[Reliability/Correctness]

The issue is briefly discussed by the paragraph at L1308–1320 (which was also present in the previous version).
With elaborator reflection in its current state, *all kinds* of failures can happen in the metaprograms, and usually they can only be fixed by trial and error because we don’t have a clear specification or semantics of elaborator reflection.
But the design of our framework separates the part that has to be implemented using elaborator reflection from the generic libraries, which, thanks to the type-checker, are much harder to get wrong than corresponding implementations in elaborator reflection (for example done by Christiansen and Brady [2016]).
For universe levels there is a similar story: since in Agda we can reason about universe levels internally, we can guarantee in advance that generically computed universe-polymorphic datatypes will satisfy the level constraints, as opposed to merely checking every generated datatype.
Because of the separation, we only have to worry about the metaprograms themselves (‘a limited trusted code base’), and improve their reliability by traditional means such as informal reasoning (Section 4.3.1) and testing.
The contribution paragraph now briefly mentions that the metaprograms can be independently maintained (L119–120); we’re hoping to expand the paragraph at L1308–1320 to say all the above more clearly (after making some space).

> Despite the density of the paper, though, I think this is impressive work and occupies an interesting point in the design space that deserves to be explored further in the future. In particular the examples in Section 6 are chosen well to demonstrate the power of the approach.

> Questions for authors’ response
> -------------------------------
> Due to space constraints, I'm aware you may not be able to answer all of these, but I would be most interested in some comments about the following:

> 1. Little is being said in the paper about performance. I guess performance of the generic programs or types itself is not that relevant due to the elaborator approach, but what about compiler performance? Is there a noticable impact in running the elaborator macros?

[Performance]

A paragraph discussing performance issues has been added at L1228–1247.

> 2. Do you really think the / an Agda standard library should be structured using this approach? Would it not make it less accessible to the end user, because any user would have to understand this approach in order to make sense of the definitions in there? Or do you believe exposing the genericity of the underlying concepts is worth it?

We haven’t managed to include our answer to this question given in the author response, but we’ll try.

> 3. [perhaps the most important question] How can we trust the elaborator reflection code? Of course, we can trust the resulting programs, because they're passing the Agda type-checker. But how can we know this will always work?

See [Reliability/Correctness].

> Review #20B
> ===========================================================================

> Comments for author
> -------------------
> ### Evaluation

> I think the library contributed in this paper looks fantastic (if it works as
> well as advertised).
> Generic programming is something that *seems* it should be a perfect fit in
> Agda: the powerful type system facilitates the proper description of the generic
> types, and the automation that it facilitates would really reduce the burden on
> some uglier proofs.
> For whatever reason, though, generic libraries aren't used much (in my
> experience).
> This paper argues that it is the lack of interoperability, and I think that is
> one of the reasons, also however Agda itself doesn't seem to have a lot of
> general libraries in use, or many large projects that might benefit from this
> kind of thing.

Indeed, there are other equally important reasons.
Changed ‘The major problem’ to ‘One major problem’ (L34).

> Performance is also a concern.

See [Performance].

> So, in summary: the contributions of this paper look really good, in terms of
> the practical usefulness of a generic programming library.
> I would like to see the following areas of criticism addressed:

> #### Too much time on (some) implementation details

> I think the paper would benefit from a more high-level focus, rather than a
> detailed accounting of every problem encountered while implementing the library.
> The latter is fine for a technical report or similar, but for a paper for an
> ICFP audience I do not think that a detailed description of wrangling Agda's
> peculiar system of universe polymorphism is warranted.
> Instead, I would like to see a summary of the techniques and insights learned
> while implementing that system.

See [Accessibility/Big Picture] and [Novelties/Contributions].

> I highlight the universe polymorphism in particular because very little of the
> code for dealing with that is generally applicable to other languages, or
> gives general insight about dependent types.
> (as the authors note, much of the effort in that section is spent on handling a
> particular limitation of *this version* of Agda).

Section 5 on universe polymorphism is revised to argue that Agda’s first-class levels are in fact useful, and maybe even essential, for datatype-generic programming.
This makes first-class levels a feature that other languages might consider adopting if they want to support universe-polymorphic datatype-genericity (which we don’t think has been done before, which might explain why first-class levels aren’t popular).
We did use too much space for describing the limitation, which is now only briefly mentioned in Section 5.4 (in the hope of drawing someone’s attention and motivating them to work on it).

> The code examples in the end of the paper are excellent (and should be given
> more space), but for level polymorphism in particular it reads a little like a
> description of "problems encountered when implementing this library", instead
> of "insights and techniques gained when implementing this library".

The sentence at L1118–1120 is changed to say something more positive.

> Another example is the reflection system: a brief summary is fine, and a
> high-level overview of the technique used is good, but it is absolutely
> unnecessary (and confusing) to include the definition of the entire reflected
> Agda AST as is done on page 14.

Section 4.1 has been rewritten to focus more on the general ideas and give only a few of the definitions.

> #### Not Enough Theory or General Applicability

> I think the paper is just about general enough to be interesting to an ICFP
> audience, but the focus on Agda-specific constructs hurts it in this regard.

> In the paper's favour, generics are widely useful in dependently typed
> programming languages, and indeed the technique that the paper itself builds on
> comes from Haskell, not Agda.
> Furthermore, elaborator reflection is a technique widely available in other
> languages, notably Idris (as mentioned), and as such is also generally
> applicable.
> I would like to see the contributions of the paper phrased in a way that points
> out that what is done here is generally useful,
> and I would like to see less focus on the Agda specifics of the implementation.

See [Novelties/Contributions].

> #### More Evaluation, please

> There is a lack of evaluation of the library from a user's perspective.
> Part of this is focus: the end of the paper (the examples) should be expanded,
> and should be given as much space as the other parts, *especially* with more
> code examples.

Sections 6.1 and 6.2 have been expanded (though not much) to give more code for generic program instantiation and macro invocation.

> In the fold-fusion example (line 914), for instance, I would like to see an
> actual simple theorem using fold fusion proven.
> I know that such a theorem is not novel, but it would greatly aid in
> understanding.

A foldr-map fusion example is now included at L967–974.

> The other issue is one of the usability of the library from more practical
> perspectives.
> No mention is made of performance, which is important for an editor-driven
> language like Agda,

See [Performance].

> or of error messages.
> Perhaps as a fleshed-out example of the fold fusion operator, a simple program
> proving (something like) map fusion could be included, including the full code,
> and a mention of type errors that might arise.
> Custom type errors are also possible using Agda's metaprogramming, but it seems
> that they are not used here.

We’re not sure what kind of type error is being referred to here — as soon as foldr-fusion (L966) is unquoted (and also printed to the debug buffer, so the user even sees the definition at L66–72), it’s an ordinary function, and the subsequent development is the same as any other development.
The only interesting kind of type error we can think of arises from wrong macro invocations, and we’ve included one at L943–946.

> ### Small Notes

> * Please use Agda's generalization of declared variables more, it makes code
>   much more readable.
>   `foldr` on line 43 and `foldr-fusion` on line 52 are particularly bad
>   examples: `{A : Set ell}` etc should not be present.

The purpose of including `{A : Set ℓ} {B : Set ℓ'}` in the type of `foldr` is to emphasise that it is fully universe-polymorphic — we’ve inserted a sentence to say this at L73.
As for `foldr-fusion`, the types of `h`, `e`, `f`, etc may look cluttered, but they correspond to the kind of type information that would appear in a normal theorem statement to help the reader to (mentally) type-check and make sense of the statement; also, the types/meaning of `h`, `e`, `f`, etc are local to the theorem and can easily change elsewhere, so we wouldn’t want to generalise these variables in actual developments.

> * On line 218, the non-terminating fold example needs more explanation as to why
>   we should not be concerned that it doesn't pass the termination checker.
>   "Our work does not use fold" doesn't make sense on first reading: surely your
>   work *does* use fold and folds?
>   Of course what you're saying is that you don't use this definition of a fold,
>   but folds generated later *do* pass the termination checker.
>   This needs to be said explicitly.

Now explained more clearly in footnote 4 (L291–293).
A bit more reasoning about how generated folds pass the termination check has also been added at L707–709.

> * Page 14: do not include a copy-paste of Agda's entire AST!

Section 5.1 has been rewritten.

> * line 711: hygienic, not hygiene

Fixed.

> Less important to include, but I would like to see some mention of cubical agda
> or similar in the paper.
> Since you're using --without-K, everything should be compatible, and the DataC
> type constructs a full isomorphism between a type and its generic
> representation.
> It should be possible, then, to convert that to be a full equality I think,
> using cubical, which would potentially increase the power of the system
> somewhat.

We don’t immediately come up with a nice example that uses the equality obtained from the isomorphism, and right now there’s no space left...

> Review #20C
> ===========================================================================

> Comments for author
> -------------------
> Post rebuttal: the rebuttal did not answer some of my questions properly, other
> than the response to performance. My main concern with this paper is its
> accessibility. I think it'd be necessary for the authors to improve the
> presentation and also include a more detailed discussion about its applicability
> to other languages during revisions.

See [Accessibility/Big Picture] and [Novelties/Contributions].

> ----------
> 1. The paper is not easy to read for non-experts. For example, while
>    section 2 aims to recap standard datatype-generic programming, it
>    assumes lots of background from the readers, and it is not clear to
>    me what the purpose of a "description" is after reading Section
>    2.1.

See [Accessibility/Big Picture].
For Section 2.1 in particular, we think this is because we forgot to give the general idea of datatype-genericity, which is now explained (briefly) at the beginning of Section 2.
In particular, we give a preliminary explanation of what descriptions are and why they are important, before looking at a specific form of descriptions in Section 2.1.

> 2. I failed to understand how much of the paper is theoretical
>    contributions, how much is engineering, and how much of the theory
>    and engineering is specific to Agda. Can you apply those
>    techniques to other dependently typed languages, e.g., Idris?

>    You mentioned why Haskell's approach does not apply to Agda (l68).
>    Can you apply the approach in the paper to improve the
>    implementations in Haskell then?

See [Novelties/Contributions].

> 3. The final definition of `AccD` (l442) is intimidating. Is that what
>    the user needs to write?

We have added a sentence at L323–326 to remind the reader that definitions like `AccD` will eventually be generated by metaprograms.

>    Have you considered the usability of this
>    approach for "the practical Agda programmer"?

The metaprograms, which are our main contribution, exist exactly for the purpose of automatically generating the components of the framework and saving the programmer’s time.
There is now a paragraph at the beginning of Section 4 (L504–510) saying this.
We have also mentioned a few mechanisms that could possibly make our framework and generic libraries more convenient to use in Section 6 (L919–920, L946–947, L1020–1023, and L1096–1106).

> 4. You mentioned that the framework can generate native datatypes from
>    a description. Will the approach introduce any performance
>    regression, e.g., on your examples?

See [Performance].

> 5. What're the criteria of correctness for the framework? Are there
>    any properties you could prove? Something like if a description is
>    valid, then the generated datatypes are well-typed?

See [Reliability/Correctness].
