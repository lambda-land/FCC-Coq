# Formula Choice Calculus

This repository accompanies the following paper:

[Spencer Hubbard][Spencer] and [Eric Walkingshaw][Eric].
"Formula Choice Calculus",
*Int. Conf. on Feature-Oriented Software Development ([FOSD][FOSD])*,
2016.

(**[Preprint PDF][Preprint]**)


### Abstract:

The choice calculus is a simple metalanguage and associated theory that has
been successfully applied to several problems of interest to the
feature-oriented software development community. The formal presentation of the
choice calculus essentially restricts variation points, called choices, to vary
based on the inclusion or not of a single feature, while in practice variation
points may depend on several features. Therefore, in both theoretical
applications of the choice calculus, and in tools inspired by the choice
calculus, the syntax of choices has often been generalized to depend on an
arbitrary propositional formula of features. The purpose of this paper is to
put this syntactic generalization on more solid footing by also generalizing
the associated theory. Specifically, after defining the syntax and denotational
semantics of the formula choice calculus (FCC), we define and prove the
soundness of a syntactic equivalence relation on FCC expressions. This effort
validates previous work which has implicitly assumed the soundness of rules in
the equivalence relation, and also reveals several rules that are specific to
FCC. Finally, we describe some further generalizations to FCC and their limits.


[Eric]: http://web.engr.oregonstate.edu/~walkiner/
[Spencer]: http://web.engr.oregonstate.edu/~hubbarsp/
[FOSD]: http://2016.splashcon.org/track/fosd2016
[Preprint]: http://web.engr.oregonstate.edu/~walkiner/papers/fosd16-formula-choice-calculus.pdf
